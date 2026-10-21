-- Prove2me | Definitions.Def_RetirePartialInfo_Duality_Dual
-- name    : RetirePartialInfo_Duality_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:36.050312+00:00
-- url     : https://prove2.me/theorems/19852216-c07d-48a6-947a-0847d97c4841
-- title:
--   (13), (14), (17)–(18), Assumption 2.3, pp. 11–13 — dual values 𝐋(0, y, 1), 𝐋(0, y, 0), the candidate (c*, H*), the budget cost 𝒳
-- statement:
--   **The dual problem** ((13), (14), Definition 2.7 and Assumption 2.3 of Chen, Jeon and Wong), at time $0$, with the dual process $y_s=y\,e^{\beta s}\mathcal Z_s/B_s$.
--
--   *After retirement* (13):
--   $$\mathbf L(0,y,1)=\mathbb E\Bigl[\int_0^Te^{-\beta s}\tilde U_1(s,y_s)\,ds+e^{-\beta T}\tilde U_2(T,y_T)\Bigr].$$
--
--   *With the retirement option* (14): for a retirement time $\tau$ ($\mathcal F^S$-stopping time in $[0,T_1]$), let
--   $$\Lambda(y,\tau)=\mathbb E\Bigl[\int_0^\tau e^{-\beta s}\bigl(\tilde U_1(s,y_s)-\ell\bigr)ds+e^{-\beta\tau}\bigl(\mathbf L(\tau,y_\tau,1)+y_\tau b(\tau)\bigr)\Bigr],$$
--   where $e^{-\beta\tau}\mathbf L(\tau,y_\tau,1)=\mathbb E\bigl[\int_\tau^Te^{-\beta s}\tilde U_1(s,y_s)ds+e^{-\beta T}\tilde U_2(T,y_T)\bigm|\mathcal F^S_\tau\bigr]$, and $\mathbf L(0,y,0)=\sup_\tau\Lambda(y,\tau)$ over all such $\tau$. A retirement time $\hat\tau$ is **optimal in (14)** at $y$ if $\Lambda(y,\tau)\le\Lambda(y,\hat\tau)$ for every retirement time $\tau$; the paper's $\hat\tau_{0,y}=\inf\{u\ge0:\mathbf L(u,y_u,0)=\mathbf L(u,y_u,1)+y_ub(u)\}\wedge T_1$ is one.
--
--   *Candidate and budget cost* ((17)–(18)). $c^*_s=I_1(s,y_s)$, $H^*_T=I_2(T,y_T)$, $R^*_s=\mathbf 1\{s\ge\hat\tau\}$, and
--   $$\mathcal X(0,y)=\tilde{\mathbb E}\Bigl[\frac{H^*_T}{B_T}+\int_0^T\frac{c^*_u}{B_u}\,du-\int_0^T\frac{b(u)}{B_u}\,dR^*_u\Bigr],\qquad \mathcal X_1(0,y)+\mathcal X_2(0,y)=\tilde{\mathbb E}\Bigl[\int_0^T\frac{I_1(s,y_s)}{B_s}ds+\frac{I_2(T,y_T)}{B_T}\Bigr].$$
--   **Assumption 2.3** at $t=0$: $\mathcal X(0,y)<\infty$ for all $y>0$.
--
--   The dual problem (15) is to minimise $\mathbf L(0,y,R_0)+y(x-b(0)(1-R_0))$ over $y>0$; Proposition 2.4 states when its solution gives the primal optimum.
--
--   **Formalization Note.** $\mathcal X$ is computed in $[0,\infty]$ as a lower Lebesgue integral (every term is nonnegative, since $b\le0$); the atom $-b(\tau)/B_\tau$ of $dR^*$ is counted also when $\tau=0$, as in (14). The retirement time entering $\mathcal X$ is passed in, in place of the paper's $\hat\tau_{0,y}$. Since the retirement term lies in $[0,-b(0)]$, Assumption 2.3 is stated as $\mathcal X_1(0,y)+\mathcal X_2(0,y)<\infty$. Added hypothesis `DualIntegrable`: for every $y>0$, $e^{-\beta s}\tilde U_1(s,y_s)$ is $ds\otimes\mathbb P$-integrable on $[0,T]\times\Omega$ and $\tilde U_2(T,y_T)$ is $\mathbb P$-integrable (the paper treats $\mathbf L$ as finite). $\mathbf L(\tau,y_\tau,1)$ is restarted from $(\tau,y_\tau)$ with the same multiplicative dual process, and the conditional expectation is given the σ-algebra of the stopping time; the tower-collapsed form of (14) is a proof step and is not used as the definition.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 11–14, (13), (14), Definition 2.7 (17)–(18), Assumption 2.3, and p. 14 (𝒳₁, 𝒳₂)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The dual value after retirement** `𝐋(0, y, 1)` ((13), p. 11, SSRN 3683553, June 8, 2021):
"`E_t[∫_t^T e^{−β(s−t)} Ũ_1(s, y_s) ds + e^{−β(T−t)} Ũ_2(T, y_T)] := 𝐋(t, y, 1)`", at `t = 0`:
`𝐋(0, y, 1) = E[∫_0^T e^{−βs} Ũ_1(s, y_s) ds + e^{−βT} Ũ_2(T, y_T)]`,
with the dual process `y_s = y e^{βs} 𝒵_s / B_s` (`ydual`). -/
noncomputable def L1 (p : Params) (st : Setting Ω) (Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (y : ℝ) : ℝ :=
  ∫ ω, (∫ s in Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
    Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω) ∂st.P

/-- `e^{−βτ} 𝐋(τ, y_τ, 1)` inside (14), p. 12 (SSRN 3683553, June 8, 2021), for a retirement time
`τ`: the value (13) restarted at the stopping time `τ` from the dual state `y_τ`,
`E[∫_τ^T e^{−βs} Ũ_1(s, y_s) ds + e^{−βT} Ũ_2(T, y_T) | F^S_τ]`.

**Formalization Note.** The dual process started at `(τ, y_τ)` is the same process
`y_s = y e^{βs} 𝒵_s/B_s` (it is multiplicative), so `e^{−βτ} 𝐋(τ, y_τ, 1)` is this conditional
expectation given the σ-algebra `F^S_τ` of the stopping time (`IsStoppingTime.measurableSpace`). -/
noncomputable def L1at (p : Params) (st : Setting Ω) (Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (y : ℝ) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) : Ω → ℝ :=
  st.P[fun ω => (∫ s in Icc (τ ω : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
      Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω) | hτ.1.measurableSpace]

/-- The objective of the optimal stopping problem (14), p. 12 (SSRN 3683553, June 8, 2021), at
`t = 0`, for a retirement time `τ`:
`E[∫_0^τ e^{−βs}(Ũ_1(s, y_s) − ℓ) ds + e^{−βτ}(𝐋(τ, y_τ, 1) + y_τ b(τ))]`. -/
noncomputable def stopObj (p : Params) (st : Setting Ω) (Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (y : ℝ) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) : ℝ :=
  ∫ ω, (∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s) * (Utilde U1 s (ydual p Zv y s ω) - p.ℓ)) +
    L1at p st Zv U1 U2 y τ hτ ω +
    Real.exp (-p.β * (τ ω)) * ydual p Zv y (τ ω) ω * b p (τ ω) ∂st.P

/-- **The dual value of the working agent** `𝐋(0, y, 0)` ((14), p. 12, SSRN 3683553,
June 8, 2021):
"`= max_{τ∈ℛ_{t,T1}} E_t[∫_t^τ e^{−β(s−t)}(Ũ_1(s, y_s) − ℓ)ds + e^{−β(τ−t)}(𝐋(τ, y_τ, 1) + y_τb(τ))]
:= 𝐋(t, y, 0)`, where `ℛ_{t,T1}` is the set of all stopping times taking values in `[t, T1]`", at
`t = 0`: the supremum of `stopObj` over all `F^S`-stopping times `τ ∈ [0, T1]`.

**Formalization Note.** The paper's "max" is a supremum; its attainment by an optimal stopping
time is a hypothesis wherever it is used (`IsOptimalStop`). -/
noncomputable def L0 (p : Params) (st : Setting Ω) (Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (y : ℝ) : ℝ :=
  sSup {v | ∃ τ : Ω → ℝ≥0, ∃ hτ : IsRetirementTime p st τ, v = stopObj p st Zv U1 U2 y τ hτ}

/-- `τ̂` is an **optimal stopping time of (14)** at the multiplier `y`: a retirement time whose
objective is at least that of every `F^S`-stopping time `τ ∈ [0, T1]`. The paper's
`τ̂_{0,y} = inf {u ≥ 0 : 𝐋(u, y_u, 0) = 𝐋(u, y_u, 1) + y_u b(u)} ∧ T1` ((18), p. 12) is such a time
("is optimal in (14) for a fixed y", p. 12, citing Peskir–Shiryaev). -/
def IsOptimalStop (p : Params) (st : Setting Ω) (Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ) (y : ℝ)
    (τhat : Ω → ℝ≥0) (hτhat : IsRetirementTime p st τhat) : Prop :=
  ∀ (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ),
    stopObj p st Zv U1 U2 y τ hτ ≤ stopObj p st Zv U1 U2 y τhat hτhat

/-- The candidate consumption of (18), p. 12: `c*_s = I_1(s, y_s)`. -/
noncomputable def cstar (p : Params) (Zv : ℝ≥0 → Ω → ℝ) (U1 : ℝ → ℝ → ℝ) (y : ℝ) (s : ℝ≥0)
    (ω : Ω) : ℝ :=
  Iinv U1 s (ydual p Zv y s ω)

/-- The candidate terminal wealth of (18), p. 12: `H*_T = I_2(T, y_T)`. -/
noncomputable def Hstar (p : Params) (Zv : ℝ≥0 → Ω → ℝ) (U2 : ℝ → ℝ → ℝ) (y : ℝ) (ω : Ω) : ℝ :=
  Iinv U2 p.T (ydual p Zv y p.T ω)

/-- `𝒳_1(0, y) + 𝒳_2(0, y)` (p. 14, SSRN 3683553, June 8, 2021): the budget cost of the candidate
consumption and terminal wealth, `Ẽ[∫_0^T I_1(s, y_s)/B_s ds + I_2(T, y_T)/B_T]`, in `[0, ∞]`. -/
noncomputable def X12 (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Hstar p Zv U2 y ω / Bt p p.T) +
    (∫⁻ s in Icc (0 : ℝ) p.T, ENNReal.ofReal (cstar p Zv U1 y s.toNNReal ω / Bt p s))
    ∂Pt p st Iθ

/-- **The budget cost** `𝒳(0, y)` of Definition 2.7, (17)–(18), p. 12 (SSRN 3683553,
June 8, 2021), at `t = 0`, for the retirement time `τ` of the candidate:
`𝒳(0, y) = Ẽ[H*_T/B_T + ∫_0^T c*_u/B_u du − ∫_0^T b(u)/B_u dR*_u]`
with `H*_T = I_2(T, y_T)`, `c*_s = I_1(s, y_s)`, `R*_s = 1{s ≥ τ}`, so that the last integral is
the atom `b(τ)/B_τ`.

**Formalization Note.** Every term is nonnegative (`b ≤ 0`), so `𝒳` is computed in `[0, ∞]` as a
lower Lebesgue integral. The atom at `τ` is counted also when `τ = 0` (immediate retirement), as in
(14). The paper's `τ̂_{0,y}` is replaced by the retirement time `τ` passed in; the goal takes for it
an optimal stopping time of (14). -/
noncomputable def Xcal (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (y : ℝ) (τ : Ω → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Hstar p Zv U2 y ω / Bt p p.T) +
    (∫⁻ s in Icc (0 : ℝ) p.T, ENNReal.ofReal (cstar p Zv U1 y s.toNNReal ω / Bt p s)) +
    ENNReal.ofReal (-(b p (τ ω)) / Bt p (τ ω)) ∂Pt p st Iθ

/-- **Assumption 2.3**, p. 13 (SSRN 3683553, June 8, 2021), at `t = 0`: "`𝒳(t, y) < ∞` for all
`y > 0`". Since the retirement term of `𝒳` lies in `[0, −b(0)]`, this is
`𝒳_1(0, y) + 𝒳_2(0, y) < ∞` for every `y > 0`, whichever retirement time enters `𝒳`. -/
def Assumption23 (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ) :
    Prop :=
  ∀ y : ℝ, 0 < y → X12 p st Iθ Zv U1 U2 y < ⊤

/-- **Integrability of the dual** (added): for every `y > 0`, `(s, ω) ↦ e^{−βs} Ũ_1(s, y_s)` is
`ds ⊗ P`-integrable on `[0, T] × Ω` and `Ũ_2(T, y_T)` is `P`-integrable.

**Formalization Note.** The paper treats `𝐋(t, y, 1)` and `𝐋(t, y, 0)` as finite real numbers
((13)–(16)); this hypothesis makes the expectations defining them genuine integrals instead of
Lean's junk value `0`. -/
def DualIntegrable (p : Params) (st : Setting Ω) (Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 0 < y →
    Integrable (fun z : ℝ × Ω => Real.exp (-p.β * z.1) * Utilde U1 z.1 (ydual p Zv y z.1 z.2))
      ((volume.restrict (Icc (0 : ℝ) p.T)).prod st.P) ∧
    Integrable (fun ω => Utilde U2 p.T (ydual p Zv y p.T ω)) st.P

end RetirePartialInfo.Duality


