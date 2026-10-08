-- Prove2me | Definitions.Def_ViscosityPPDE_Comparison_Perron
-- name    : ViscosityPPDE_Comparison_Perron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:30:57.3088+00:00
-- url     : https://prove2.me/theorems/33689cff-6329-4111-bbe2-a73813163dff
-- title:
--   Definitions 2.6, 2.8, (6.2) — $C^{1,2}_b(\bar\Lambda(\tau))$, $\bar C^{1,2}_{\mathbb P}(\Lambda^t)$ and the Perron classes $\overline{\mathcal D}$, $\underline{\mathcal D}$
-- statement:
--   Let $t\le T$ and $\mathbb P$ a measure on $\Omega^t$.
--
--   1. (Definition 2.6) For $\sigma \in \mathcal T^r$, $\psi \in C^{1,2}_b(\bar\Lambda^r(\sigma))$ if some $\tilde u \in C^{1,2}_b(\Lambda^r)$ equals $\psi$ on $\bar\Lambda^r(\sigma) = \{(s,\omega) \in\Lambda^r : s\le\sigma(\omega)\}$.
--   2. (Definition 2.8) $\varphi : \Lambda^t\to\mathbb R$ is in $\bar C^{1,2}_{\mathbb P}(\Lambda^t)$ if there is an increasing sequence of $\mathbb F^t$-stopping times $t = \tau_0\le\tau_1\le\dots\le T$ such that (i) for each $i$ and $\omega\in\Omega^t$, $\tau_{i+1}^{\tau_i(\omega),\omega} \in \mathcal T^{\tau_i(\omega)}_+$ and $\varphi^{\tau_i(\omega),\omega} \in C^{1,2}_b\big(\bar\Lambda^{\tau_i(\omega)}(\tau_{i+1}^{\tau_i(\omega),\omega})\big)$; (ii) for each $i$ and $\omega$, $s\mapsto\varphi(s,\omega)$ is continuous on $[t,\tau_i(\omega)]$; (iii) for $\mathbb P$-a.e. $\omega$ the set $\{i : \tau_i(\omega) < T\}$ is finite. On $\tau_i(\omega)\le s<\tau_{i+1}(\omega)$ the derivatives of $\varphi$ are those of the local extension of $\varphi^{\tau_i(\omega),\omega}$, taken at the shifted path (2.10).
--   3. (6.2) For $(t,\omega) \in \Lambda$,
--   $$\overline{\mathcal D}(t,\omega) = \big\{\varphi\in\bar C^{1,2}_{P^t_0}(\Lambda^t)\text{ bounded} : (\mathcal L\varphi)^{t,\omega}_s \ge 0,\ s\in[t,T]\text{ and }\varphi_T \ge g^{t,\omega},\ P^t_0\text{-a.s.}\big\},$$
--   and $\underline{\mathcal D}(t,\omega)$ is the same with $\le$ in both inequalities. The class with a general terminal bound $G$ in place of $g^{t,\omega}$ is also defined; at $(t,\omega) = (0,\mathbf 0)$ with $G = u^1(T,\cdot)$ it is the class of condition (5.11).
--
--   The Perron envelopes of the paper are $\bar u(t,\omega) = \inf\{\varphi(t,\mathbf 0):\varphi\in\overline{\mathcal D}(t,\omega)\}$ and $\underline u(t,\omega) = \sup\{\varphi(t,\mathbf 0) : \varphi\in\underline{\mathcal D}(t,\omega)\}$ (6.1); the statements of the mission use the classes directly and never form these infima.
--
--   **Formalization Note** "$(\mathcal L\varphi)^{t,\omega}_s \ge 0$, $s\in[t,T]$ and $\varphi_T\ge g^{t,\omega}$, $P^t_0$-a.s." is read as: for $P^t_0$-a.e. $\omega'$, for every $s\in[t,T)$ the operator at $(s,\omega')$ is $\ge0$, and $\varphi(T,\omega')\ge g(\omega\otimes_t\omega')$. The time $s = T$ is excluded because $\partial_t$ at $T$ is the limit (2.4), which need not exist for a piecewise object. The operator at $(s,\omega')$ on the piece $[\tau_i(\omega'),\tau_{i+1}(\omega'))$ is required to have the sign for every local extension. In Definition 2.8, "$\mathbb P$ a semimartingale measure" is only used with $\mathbb P = P^t_0$, and (ii)'s "$\omega\in\Omega$, continuous on $[0,\tau_i(\omega)]$" is read in the shifted space as $\omega \in \Omega^t$ and $[t,\tau_i(\omega)]$. The sequence is existentially quantified together with the a.s. conditions.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, Definition 2.6, (2.10), p. 6; Definition 2.8, p. 8; (5.11), p. 23; (6.1), (6.2), p. 25

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Viscosity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

variable {d : ℕ} {T : ℝ≥0}

/-- The shifted field `u^{r,ω}(s, ω'') = u(s, ω ⊗_r ω'')` on `Λ^r`, for `u` on `Λ^t` and `ω ∈ Ω^t`. -/
def shiftField {t : ℝ≥0} (u : ℝ≥0 → Omega d T t → ℝ) (r : ℝ≥0) (ω : Omega d T t) :
    ℝ≥0 → Omega d T r → ℝ :=
  fun s ω'' => u s (concat ω r ω'')

/-- The shifted random time `τ^{r,ω}(ω'') = τ(ω ⊗_r ω'')` on `Ω^r`. -/
def shiftTime {t : ℝ≥0} (τ : Omega d T t → ℝ≥0) (r : ℝ≥0) (ω : Omega d T t) :
    Omega d T r → ℝ≥0 :=
  fun ω'' => τ (concat ω r ω'')

/-- `X` witnesses `ψ ∈ C^{1,2}_b(Λ̄^r(σ))` (Definition 2.6, shifted): `X.fn ∈ C^{1,2}_b(Λ̂^r)`
(so its restriction `ũ` to `Λ^r` lies in `C^{1,2}_b(Λ^r)`) and `ψ = ũ` on
`Λ̄^r(σ) = {(s, ω'') ∈ Λ^r : s ≤ σ(ω'')}` (2.9). -/
def IsLocalExt (r : ℝ≥0) (ψ : ℝ≥0 → Omega d T r → ℝ) (σ : Omega d T r → ℝ≥0)
    (X : C12Data d) : Prop :=
  IsC12bHat T r X ∧ ∀ s (ω'' : Omega d T r), r ≤ s → s ≤ T → s ≤ σ ω'' → X.fn s ω''.1 = ψ s ω''

/-- The sequence `t = τ_0 ≤ τ_1 ≤ ⋯ ≤ T` of `𝔽^t`-stopping times witnessing
`φ ∈ C̄^{1,2}_P(Λ^t)` (Definition 2.8): (i) for each `i` and `ω ∈ Ω^t`,
`τ_{i+1}^{τ_i(ω), ω} ∈ 𝒯^{τ_i(ω)}_+` and `φ^{τ_i(ω), ω} ∈ C^{1,2}_b(Λ̄^{τ_i(ω)}(τ_{i+1}^{τ_i(ω), ω}))`;
(ii) for each `i` and `ω`, `s ↦ φ(s, ω)` is continuous on `[t, τ_i(ω)]`; (iii) for `P`-a.e. `ω`,
`{i : τ_i(ω) < T}` is finite. -/
def IsCbarSeq {t : ℝ≥0} (P : Measure (Omega d T t)) (φ : ℝ≥0 → Omega d T t → ℝ)
    (τ : ℕ → Omega d T t → ℝ≥0) : Prop :=
  (∀ ω, τ 0 ω = t) ∧ (∀ i ω, τ i ω ≤ τ (i + 1) ω) ∧ (∀ i, IsStop T t (τ i)) ∧
    (∀ i (ω : Omega d T t),
      IsStopTPlus T (τ i ω) (shiftTime (τ (i + 1)) (τ i ω) ω) ∧
        ∃ X, IsLocalExt (τ i ω) (shiftField φ (τ i ω) ω) (shiftTime (τ (i + 1)) (τ i ω) ω) X) ∧
    (∀ i ω, ContinuousOn (fun s => φ s ω) (Set.Icc t (τ i ω))) ∧
    (∀ᵐ ω ∂P, Set.Finite {i | τ i ω < T})

/-- `φ ∈ C̄^{1,2}_P(Λ^t)` (Definition 2.8). -/
def IsCbar {t : ℝ≥0} (P : Measure (Omega d T t)) (φ : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  ∃ τ, IsCbarSeq P φ τ

/-- `(ℒφ)^{t,ω}_s(ω') ≥ 0` for every `s ∈ [t, T)` along the path `ω' ∈ Ω^t`, for `φ ∈ C̄^{1,2}`
with sequence `τ`: on the piece `τ_i(ω') ≤ s < τ_{i+1}(ω')` the derivatives of `φ` at `(s, ω')` are
those (2.10) of any local extension `X` of `φ^{τ_i(ω'), ω'}`, taken at the shifted path
`ω'_{· ∨ τ_i(ω')} − ω'_{τ_i(ω')}`. -/
def OpNonnegAlong (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (t : ℝ≥0) (ω : Omega d T 0)
    (φ : ℝ≥0 → Omega d T t → ℝ) (τ : ℕ → Omega d T t → ℝ≥0) (ω' : Omega d T t) : Prop :=
  ∀ i s, τ i ω' ≤ s → s < τ (i + 1) ω' → s < T → ∀ X,
    IsLocalExt (τ i ω') (shiftField φ (τ i ω') ω') (shiftTime (τ (i + 1)) (τ i ω') ω') X →
      0 ≤ shiftedOp f t ω X s (shiftFrom ω' (τ i ω')).1 ω' (φ s ω')

/-- `(ℒφ)^{t,ω}_s(ω') ≤ 0` for every `s ∈ [t, T)` along `ω'` (see `OpNonnegAlong`). -/
def OpNonposAlong (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (t : ℝ≥0) (ω : Omega d T 0)
    (φ : ℝ≥0 → Omega d T t → ℝ) (τ : ℕ → Omega d T t → ℝ≥0) (ω' : Omega d T t) : Prop :=
  ∀ i s, τ i ω' ≤ s → s < τ (i + 1) ω' → s < T → ∀ X,
    IsLocalExt (τ i ω') (shiftField φ (τ i ω') ω') (shiftTime (τ (i + 1)) (τ i ω') ω') X →
      shiftedOp f t ω X s (shiftFrom ω' (τ i ω')).1 ω' (φ s ω') ≤ 0

/-- Supersolution-type membership with terminal bound `G` (the class of (5.11) and of `𝒟̄` in
(6.2)): `φ ∈ C̄^{1,2}_{P^t_0}(Λ^t)` bounded, and `P^t_0`-a.s., `(ℒφ)^{t,ω}_s ≥ 0` for `s ∈ [t, T)`
and `φ_T ≥ G`. -/
def IsSuperC (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (t : ℝ≥0)
    (ω : Omega d T 0) (G : Omega d T t → ℝ) (φ : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  (∃ C, ∀ s ω', t ≤ s → s ≤ T → |φ s ω'| ≤ C) ∧
    ∃ τ, IsCbarSeq (Pt P0 t) φ τ ∧
      ∀ᵐ ω' ∂(Pt P0 t), OpNonnegAlong f t ω φ τ ω' ∧ G ω' ≤ φ T ω'

/-- Subsolution-type membership with terminal bound `G` (the class of `𝒟̲` in (6.2)). -/
def IsSubC (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (t : ℝ≥0)
    (ω : Omega d T 0) (G : Omega d T t → ℝ) (φ : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  (∃ C, ∀ s ω', t ≤ s → s ≤ T → |φ s ω'| ≤ C) ∧
    ∃ τ, IsCbarSeq (Pt P0 t) φ τ ∧
      ∀ᵐ ω' ∂(Pt P0 t), OpNonposAlong f t ω φ τ ω' ∧ φ T ω' ≤ G ω'

/-- `φ ∈ 𝒟̄(t, ω)` (6.2): `IsSuperC` with terminal bound `g^{t,ω}`. -/
def InDbar (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ)
    (g : Omega d T 0 → ℝ) (t : ℝ≥0) (ω : Omega d T 0) (φ : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  IsSuperC P0 f t ω (fun ω' => g (concat ω t ω')) φ

/-- `φ ∈ 𝒟̲(t, ω)` (6.2): `IsSubC` with terminal bound `g^{t,ω}`. -/
def InDlow (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ)
    (g : Omega d T 0 → ℝ) (t : ℝ≥0) (ω : Omega d T 0) (φ : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  IsSubC P0 f t ω (fun ω' => g (concat ω t ω')) φ

end ViscosityPPDE.Comparison


