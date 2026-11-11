-- Prove2me | Definitions.Def_GEGIAMP_Relative_Model
-- name    : GEGIAMP_Relative_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:50:54.248894+00:00
-- url     : https://prove2.me/theorems/aff9ea29-ff3a-44e5-aa79-8b30e393882a
-- title:
--   The SK Hamiltonian, its optimum, the Parisi data and Assumption 2.1
-- statement:
--   For a real $N\times N$ array $A$ (the GOE input of (2.1), law `RandMatDisc.goe N`): $H_N(x)=\tfrac12x^\top Ax$ and $\mathrm{OPT}_N=\max_{\sigma\in\{-1,1\}^N}H_N(\sigma)$ (2.2), both total energies; the Euclidean norm, the induced operator norm $\|A\|$, coordinatewise clipping to $[-1,1]$ and $\mathrm{dist}(x,[-1,1])$ (§5.1). The logarithmic weights $L_u=\log(e/u)$ (3.1), $r_t=1-t$, $\ell_t=\log(e/r_t)$, $\Lambda(t)=\ell_t/r_t$ (7.8). The Parisi data of the published bundle `SKFullSupport`: $\gamma(t)$, $m=\Phi_x$, $a=\Phi_{xx}$ (with $\Phi$ the control formula (5.2)), $a_x$, $a_{xx}$, the Parisi value $P^*=\mathsf P(\gamma)$ of the fixed minimizer, $g(t)=\mathbb E\,a(t,X_t)$, $M_t=m(t,X_t)$, the Brownian filtration; Assumption 2.1 ($\mathbb E[m(t,X_t)^2]=t$ for $0\le t<1$ along every Parisi diffusion) and the standing hypotheses (minimizer + Assumption 2.1).
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), §2.1–§2.3, pp. 6–7; §5.1, p. 14; (3.1) p. 7; (7.8) p. 21

import Mathlib
import Definitions.Def_SKFullSupport
import Definitions.Def_RandMatDisc_goe

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-!
# The SK model, the Parisi data and Assumption 2.1

Herman, Chakrabarti, Kim, Ozgul (2026), *A Fully Polynomial Approximation Algorithm for the
Sherrington–Kirkpatrick Model*, arXiv:2611.05446v1 (held file SHA-256 ea6508af…5658e),
§2.1–§2.3, pp. 6–7, and the notation of §5.1 (p. 14) and (7.8) (p. 21).

* (2.1): the GOE law is the published `RandMatDisc.goe N` (entries above the diagonal
  `N(0, 1/N)`, on it `N(0, 2/N)`), on `Fin N → Fin N → ℝ`.
* (2.2): `H A x = ½ xᵀ A x` and `OPT A = max_{σ ∈ {−1,1}^N} H A σ` (total energies).
* The order parameter, the Parisi solution `Φ` (read as the stochastic-control formula (5.2),
  which the paper identifies with the PDE solution on p. 15), `m = Φₓ`, `a = Φₓₓ`, the Parisi
  functional, minimizers and the Parisi diffusion (2.5) are those of the published bundle
  `OAI.ZeroTemperatureSK` (`SKFullSupport`).
* Assumption 2.1: `E[m(t, X_t)²] = t` for `0 ≤ t < 1`, for every Parisi diffusion `X`.

Spins are real vectors with entries `±1`; `spinVec b` turns a Boolean vector into one.
-/

namespace GEGIAMP.Relative

open OAI.ZeroTemperatureSK

/-! ## The SK Hamiltonian and its optimum (2.2) -/

/-- `H_N(x) = ½ xᵀ A x`, (2.2), p. 6 (a total, not per-spin, energy). -/
noncomputable def H {N : ℕ} (A : Fin N → Fin N → ℝ) (x : Fin N → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, x i * A i j * x j

/-- The spin vector `σ ∈ {−1, 1}^N` encoded by `b : Fin N → Bool` (`true ↦ 1`, `false ↦ −1`). -/
def spinVec {N : ℕ} (b : Fin N → Bool) : Fin N → ℝ := fun i => if b i then 1 else -1

/-- `x` is a spin vector: every entry is `1` or `−1`. -/
def IsSpin {N : ℕ} (x : Fin N → ℝ) : Prop := ∀ i, x i = 1 ∨ x i = -1

/-- `OPT_N = max_{σ ∈ {−1,1}^N} H_N(σ)`, (2.2), p. 6: a maximum over the `2^N` spin vectors
(the finite index set is nonempty for every `N`). -/
noncomputable def OPT {N : ℕ} (A : Fin N → Fin N → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin N → Bool)).sup' Finset.univ_nonempty (fun b => H A (spinVec b))

/-- The Euclidean norm `‖x‖ = (∑ xᵢ²)^{1/2}` (§5.1, p. 14). -/
noncomputable def vnorm {N : ℕ} (x : Fin N → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- The induced operator norm `‖A‖ = sup_{‖x‖ = 1} ‖Ax‖` (§5.1, p. 14), as the operator norm of
`A` acting on Euclidean space. -/
noncomputable def opNorm {N : ℕ} (A : Fin N → Fin N → ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N) (Matrix.of A)‖

/-- `A` is symmetric. -/
def IsSymm {N : ℕ} (A : Fin N → Fin N → ℝ) : Prop := ∀ i j, A i j = A j i

/-- `clip(x, [−1, 1]) = min{1, max{−1, x}}` (§5.1, p. 14). -/
noncomputable def clip1 (x : ℝ) : ℝ := min 1 (max (-1) x)

/-- Coordinatewise clipping to the cube `[−1, 1]^N`. -/
noncomputable def clipVec {N : ℕ} (f : Fin N → ℝ) : Fin N → ℝ := fun i => clip1 (f i)

/-- `dist(x, [−1, 1]) = inf_{y ∈ [−1,1]} |x − y|` (§5.1, p. 14), i.e. `|x − clip(x)|`. -/
noncomputable def distI (x : ℝ) : ℝ := |x - clip1 x|

/-! ## Logarithmic weights (3.1), (7.8) -/

/-- `L_u = log(e/u)` ((3.1), p. 7: `L_ε = log(e/ε)`; `L_u` for other accuracies). -/
noncomputable def Lg (u : ℝ) : ℝ := Real.log (Real.exp 1 / u)

/-- `r_t = 1 − t`, (7.8), p. 21. -/
def rr (t : ℝ) : ℝ := 1 - t

/-- `ℓ_t = log(e/r_t)`, (7.8), p. 21. -/
noncomputable def ell (t : ℝ) : ℝ := Real.log (Real.exp 1 / rr t)

/-- `Λ(t) = ℓ_t / r_t = log(e/(1 − t))/(1 − t)`, (6.5) p. 17 and (7.8) p. 21. -/
noncomputable def Lam (t : ℝ) : ℝ := ell t / rr t

/-! ## Parisi data (§2.1, p. 6; Definition 2.2, p. 7) -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The order parameter as a function of time: `γ(t)` for `0 ≤ t < 1` (and `0` outside, the
`extend` convention of `SKFullSupport`). This is the `γ` oracle of (2.7). -/
noncomputable def gam (γ : OrderParameter) (t : ℝ) : ℝ := extend γ.val t

/-- `m = Φₓ` (§2.1, p. 6), with `Φ` the control formula (5.2): `gradient` of `SKFullSupport`. -/
noncomputable def mF (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  gradient W γ t x

/-- `a = Φₓₓ` (§2.1, p. 6): `curvature` of `SKFullSupport`. -/
noncomputable def aF (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  curvature W γ t x

/-- `aₓ = Φₓₓₓ` (used in (7.4) and (7.11)). -/
noncomputable def axF (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (aF W γ t) x

/-- `aₓₓ = Φₓₓₓₓ` (used in (7.11)). -/
noncomputable def axxF (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (axF W γ t) x

/-- The Parisi value `P* = P(γ)` of the fixed minimizer `γ` ((2.4), p. 6). -/
noncomputable def Pstar (W : BrownianSystem Ω) (γ : OrderParameter) : ℝ := parisi W γ

/-- **Assumption 2.1** (full-support identity, p. 7): for the Parisi diffusion `X` of (2.5) and
every `0 ≤ t < 1`, `E[m(t, X_t)²] = t`. It is stated for every process satisfying the
integral form `IsDiffusion` of (2.5). -/
def FullSupportIdentity (W : BrownianSystem Ω) (γ : OrderParameter) : Prop :=
  ∀ X : ℝ≥0 → Ω → ℝ, IsDiffusion W γ X → ∀ t : ℝ, 0 ≤ t → t < 1 → squareMoment W γ X t = t

/-- The standing hypotheses of §§3, 7–9: `γ` minimizes the Parisi functional over the
whole class `U` ("we fix a minimizing γ", p. 7), and Assumption 2.1 holds. -/
def Standing (W : BrownianSystem Ω) (γ : OrderParameter) : Prop :=
  IsMinimizer W γ ∧ FullSupportIdentity W γ

/-- `g(t) = E a(t, X_t)` along a Parisi diffusion `X` (Proposition 7.1, p. 21). -/
noncomputable def gFun (W : BrownianSystem Ω) (γ : OrderParameter) (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ) : ℝ :=
  ∫ ω, aF W γ t (X (Real.toNNReal t) ω) ∂W.law

/-- The magnetization `M_t = m(t, X_t)` (§2.1, p. 6). -/
noncomputable def Mag (W : BrownianSystem Ω) (γ : OrderParameter) (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  mF W γ t (X (Real.toNNReal t) ω)

/-- The natural filtration of the Brownian motion of `W`. -/
noncomputable def brownFiltration (W : BrownianSystem Ω) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)

end GEGIAMP.Relative


