-- Prove2me | Definitions.Def_UnobservedWelfare_potential
-- name    : UnobservedWelfare_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:47.962447+00:00
-- url     : https://prove2.me/theorems/84b1349b-40d4-48d1-88a7-d42d03561fb4
-- title:
--   Potential $\Psi_t$, forgetting error $E_t$, surrogate score $F_w$, population energy $R_M$ and anchor $\Lambda_t$
-- statement:
--   Along an execution of Algorithm 1 with comparison price $p^\star$:
--
--   1. **Surrogate history score** $F_w(z)=H_w(z)+\sum_j w_j\,[S_{\theta_j}(p_j)-S_{\theta_j}(p^\star)-c^*(p^\star)]$, used for the weights $w_t$ before and $w^+_t=(w_t,1)$ after the purchase of round $t$.
--   2. **Potential** after the purchase of round $t$ (39):
--   $$\Psi_t=p^\star\cdot I_t+\kappa W\log\frac{\int e^{-[I_t\cdot z+\Gamma_{w^+_t}(z)]/(\kappa W)}dz}{\int e^{-q_1\cdot z/(\kappa W)}dz}+W\log\frac{\int e^{[c^*(z)-F_{w^+_t}(z)]/W}dz}{\int e^{-c^*(z)/W}dz}.$$
--   3. **Forgetting error** $E_t=\Gamma_{w_t}(p^I_t)+F_{w_t}(p^H_t)$, $2\le t\le T$.
--   4. **Surplus ratio** $r_\theta(p)=\exp([S_\theta(p)-S_\theta(p^\star)]/W)$ and **population energy** (52)
--   $$R_M(z)=2W+(M+1)\big[W(\bar r(z)-1)+c^*(z)-c^*(p^\star)+\varepsilon_T\big],\qquad \bar r(z)=\mathbb E_\theta[r_\theta(z)].$$
--   5. **Anchor** $\Lambda_t=\mathbb E_{\Pi_t}\big[e^{[F_{w_t}(Y)-R_{M_t}(Y)]/W}\big]$ with $\Pi_t=\pi^{R_{M_t}}_{2W}$.
--
--   These are analysis quantities: they use the unobserved types, and the policy never computes them.
--
--   **Formalization Note** All integrals are over $\mathbb R^m_{++}$ (`gibbsZ`). $\Lambda_t$ is a $[0,\infty]$-valued lower integral. Every quantity takes the paper's round index $t$.
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), §4.1, pp.22–23 (PDF pp.24–25): (39), $F_w$, $E_t$; §5, p.27 (PDF p.29): $r_\theta$; (52), p.29 (PDF p.31); p.30 (PDF p.32): $\Pi_t$, $\Lambda_t$

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret
import Definitions.Def_UnobservedWelfare_gibbsMean
import Definitions.Def_UnobservedWelfare_alg1
import Definitions.Def_UnobservedWelfare_roundLoss

open MeasureTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- The surrogate history score (Cheng–Tao–Xing manuscript, p.22 (PDF p.24)) of a weighted list of
records `(p_j, X_j)` of buyers of types `θ_j`:
`F_w(z) := H_w(z) + Σ_j w_j [S_{θ_j}(p_j) − S_{θ_j}(p⋆) − c*(p⋆)]`. It uses the unobserved types
and serves the analysis only.

**Formalization Note** The surpluses are at strictly positive prices, where they are finite under
RC, so `EReal.toReal` is faithful. -/
noncomputable def surrScore {m n : ℕ} {Θ : Type*} (W : ℝ) (c : (Fin m → ℝ) → ℝ)
    (u : Θ → (Fin m → ℝ) → EReal) (pstar : Fin m → ℝ) (w : Fin n → ℝ)
    (rec : Fin n → (Fin m → ℝ) × (Fin m → ℝ)) (ty : Fin n → Θ) (z : Fin m → ℝ) : ℝ :=
  histScore W c w rec z + ∑ j, w j *
    ((surplus (u (ty j)) (rec j).1).toReal - (surplus (u (ty j)) pstar).toReal - costConj c pstar)

namespace Execution

variable {m T : ℕ} {Θ : Type*} [MeasurableSpace Θ] {P : Measure Θ}
  {u : Θ → (Fin m → ℝ) → EReal} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The first `n` transaction records `(p_j, X_j)` of a path (record `i : Fin n` is the paper's
record `i + 1`). -/
def records (E : Execution m T P u μ) (n : ℕ) (ω : Ω) : Fin n → (Fin m → ℝ) × (Fin m → ℝ) :=
  fun i => (E.p i ω, E.X i ω)

/-- The types `θ_j` of the first `n` buyers of a path. -/
def types (E : Execution m T P u μ) (n : ℕ) (ω : Ω) : Fin n → Θ := fun i => E.θ i ω

/-- The inventory correction `Γ_{w_t}` before the purchase of paper round `t` (Cheng–Tao–Xing
manuscript, p.20 (PDF p.22)). -/
noncomputable def gam (E : Execution m T P u μ) (W γ : ℝ) (t : ℕ) (ω : Ω) (z : Fin m → ℝ) : ℝ :=
  invCorr W γ (wts T t (t - 1)) (E.records (t - 1) ω) z

/-- The inventory correction `Γ_{w⁺_t}` after the purchase of paper round `t` (Cheng–Tao–Xing
manuscript, p.22 (PDF p.24)). -/
noncomputable def gamPlus (E : Execution m T P u μ) (W γ : ℝ) (t : ℕ) (ω : Ω) (z : Fin m → ℝ) :
    ℝ :=
  invCorr W γ (wts T t t) (E.records t ω) z

/-- The surrogate history score `F_{w_t}` before the purchase of paper round `t` (Cheng–Tao–Xing
manuscript, p.22 (PDF p.24)). -/
noncomputable def surr (E : Execution m T P u μ) (W : ℝ) (c : (Fin m → ℝ) → ℝ)
    (pstar : Fin m → ℝ) (t : ℕ) (ω : Ω) (z : Fin m → ℝ) : ℝ :=
  surrScore W c u pstar (wts T t (t - 1)) (E.records (t - 1) ω) (E.types (t - 1) ω) z

/-- The surrogate history score `F_{w⁺_t}` after the purchase of paper round `t` (Cheng–Tao–Xing
manuscript, p.22 (PDF p.24)). -/
noncomputable def surrPlus (E : Execution m T P u μ) (W : ℝ) (c : (Fin m → ℝ) → ℝ)
    (pstar : Fin m → ℝ) (t : ℕ) (ω : Ω) (z : Fin m → ℝ) : ℝ :=
  surrScore W c u pstar (wts T t t) (E.records t ω) (E.types t ω) z

/-- The inventory price `p^I_t` of paper round `t` (Cheng–Tao–Xing manuscript, (37), p.20 (PDF
p.22)), at the available inventory `A_t`. -/
noncomputable def pInv (E : Execution m T P u μ) (W γ κ : ℝ) (t : ℕ) (ω : Ω) : Fin m → ℝ :=
  inventoryPrice W γ κ (wts T t (t - 1)) (E.records (t - 1) ω) (E.avail (t - 1) ω)

/-- The history price `p^H_t` of paper round `t` (Cheng–Tao–Xing manuscript, (37), p.20 (PDF
p.22)). -/
noncomputable def pHist (E : Execution m T P u μ) (W : ℝ) (c : (Fin m → ℝ) → ℝ) (t : ℕ) (ω : Ω) :
    Fin m → ℝ :=
  historyPrice W c (wts T t (t - 1)) (E.records (t - 1) ω)

/-- The potential after the purchase of paper round `t` (Cheng–Tao–Xing manuscript, (39), p.22
(PDF p.24)):
`Ψ_t := p⋆·I_t + κW log (∫ e^{−[I_t·z + Γ_{w⁺_t}(z)]/(κW)} dz / ∫ e^{−q_1·z/(κW)} dz)
  + W log (∫ e^{[c*(z) − F_{w⁺_t}(z)]/W} dz / ∫ e^{−c*(z)/W} dz)`, all integrals over `ℝ^m_{++}`.

**Formalization Note** Each integral is a `gibbsZ`; `q_1` is the execution's round-`0` production. -/
noncomputable def potential (E : Execution m T P u μ) (W γ κ : ℝ) (c : (Fin m → ℝ) → ℝ)
    (pstar : Fin m → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  pstar ⬝ᵥ E.invAfter t ω
    + κ * W * Real.log (gibbsZ (κ * W) (fun z => E.invAfter t ω ⬝ᵥ z + E.gamPlus W γ t ω z) /
        gibbsZ (κ * W) (fun z => E.q 0 ω ⬝ᵥ z))
    + W * Real.log (gibbsZ W (fun z => E.surrPlus W c pstar t ω z - costConj c z) /
        gibbsZ W (costConj c))

/-- The forgetting error before the purchase of paper round `t`, `2 ≤ t ≤ T`
(Cheng–Tao–Xing manuscript, p.23 (PDF p.25)): `E_t := Γ_{w_t}(p^I_t) + F_{w_t}(p^H_t)`. -/
noncomputable def forgettingError (E : Execution m T P u μ) (W γ κ : ℝ) (c : (Fin m → ℝ) → ℝ)
    (pstar : Fin m → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  E.gam W γ t ω (E.pInv W γ κ t ω) + E.surr W c pstar t ω (E.pHist W c t ω)

end Execution

/-- The surplus ratio `r_θ(p) := exp([S_θ(p) − S_θ(p⋆)]/W)` for `p ≫ 0` (Cheng–Tao–Xing
manuscript, §5, p.27 (PDF p.29)). -/
noncomputable def surplusRatio {m : ℕ} {Θ : Type*} (u : Θ → (Fin m → ℝ) → EReal) (W : ℝ)
    (pstar : Fin m → ℝ) (θ : Θ) (z : Fin m → ℝ) : ℝ :=
  Real.exp (((surplus (u θ) z).toReal - (surplus (u θ) pstar).toReal) / W)

/-- The population energy (Cheng–Tao–Xing manuscript, (52), p.29 (PDF p.31)) of a deterministic
mass `M`: `R_M(z) := 2W + (M + 1)[W(r̄(z) − 1) + c*(z) − c*(p⋆) + ε_T]`, with
`r̄(z) := E_θ[r_θ(z)]`. -/
noncomputable def popEnergy {m : ℕ} {Θ : Type*} [MeasurableSpace Θ] (u : Θ → (Fin m → ℝ) → EReal)
    (P : Measure Θ) (c : (Fin m → ℝ) → ℝ) (W : ℝ) (T : ℕ) (pstar : Fin m → ℝ) (M : ℝ)
    (z : Fin m → ℝ) : ℝ :=
  2 * W + (M + 1) * (W * ((∫ θ, surplusRatio u W pstar θ z ∂P) - 1) + costConj c z
    - costConj c pstar + epsT W T)

/-- The anchor variable of paper round `t` (Cheng–Tao–Xing manuscript, p.30 (PDF p.32)):
`Λ_t := E_{Π_t}[e^{[F_{w_t}(Y) − R_{M_t}(Y)]/W}]` with the deterministic reference distribution
`Π_t := π^{R_{M_t}}_{2W}`.

**Formalization Note** A lower Lebesgue integral with values in `[0, ∞]`, so that "`0 < Λ_t < ∞`
almost surely" has content. -/
noncomputable def Execution.anchor {m T : ℕ} {Θ : Type*} [MeasurableSpace Θ] {P : Measure Θ}
    {u : Θ → (Fin m → ℝ) → EReal} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (E : Execution m T P u μ) (W : ℝ) (c : (Fin m → ℝ) → ℝ) (pstar : Fin m → ℝ) (t : ℕ)
    (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (Real.exp ((E.surr W c pstar t ω y - popEnergy u P c W T pstar (mass T t) y) / W))
    ∂(gibbsMeasure (2 * W) (popEnergy u P c W T pstar (mass T t)))

end UnobservedWelfare


