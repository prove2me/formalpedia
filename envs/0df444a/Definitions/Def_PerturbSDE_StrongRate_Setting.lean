-- Prove2me | Definitions.Def_PerturbSDE_StrongRate_Setting
-- name    : PerturbSDE_StrongRate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:03.903178+00:00
-- url     : https://prove2.me/theorems/18c0a69d-35d6-419d-89ee-d39bea6b3a97
-- title:
--   pp. 5–6, (12)–(14) — classes 𝒞¹_𝒫 and 𝒞³_𝒟, the generator 𝒢_{µ,σ}, columns, taming map ψ, stopping times
-- statement:
--   This file fixes the notation of Hutzenthaler and Jentzen (arXiv:1401.0295v1, §1.1, pp. 5–6) used by every statement of the mission. Throughout, $d,m\in\mathbb N=\{1,2,\dots\}$, $\|\cdot\|$ is the Euclidean norm on $\mathbb R^d$, and a matrix $A\in\mathbb R^{d\times m}$ carries the **Hilbert–Schmidt (Frobenius)** norm $\|A\|_{HS(\mathbb R^m,\mathbb R^d)}=(\sum_{i,j}A_{ij}^2)^{1/2}$.
--
--   1. **Columns and products.** $\sigma_j(x)=\sigma(x)e_j$ is the $j$-th column of $\sigma(x)$, and $Aw=\sum_{j=1}^m w_j\,Ae_j$ for $w\in\mathbb R^m$.
--   2. **Taming map.** $\psi(v)=\dfrac{v}{1+\|v\|^2}$ for $v\in\mathbb R^d$.
--   3. **The class $\mathcal C^1_{\mathcal P}(\mathbb R^d,E)$** (13): continuous maps $f$ into a metric space $(E,d_E)$ for which there is $c\in[0,\infty)$ with
--   $$d_E(f(x),f(y))\le c\,(1+\|x\|^c+\|y\|^c)\,\|x-y\|\qquad\text{for all }x,y\in\mathbb R^d .$$
--   Despite the name, no differentiability is required: these are locally Lipschitz maps with polynomially growing Lipschitz constant.
--   4. **The class $\mathcal C^3_{\mathcal D}(\mathbb R^d,\mathbb R)$** (12): the union over $p,c\in[3,\infty)$ of the sets of $f\in C^2(\mathbb R^d,\mathbb R)$ such that $f''$ is locally Lipschitz continuous and, for all $i\in\{1,2,3\}$ and Lebesgue-almost all $x$,
--   $$\|f^{(i)}(x)\|_{L^{(i)}(\mathbb R^d,\mathbb R)}\le c\,|f(x)|^{1-i/p}.$$
--   5. **Generator** (14): for $\varphi\in C^2(\mathbb R^d,\mathbb R)$,
--   $$(\mathcal G_{\mu,\sigma}\varphi)(x)=\varphi'(x)\mu(x)+\tfrac12\operatorname{tr}\big(\sigma(x)\sigma(x)^*(\operatorname{Hess}\varphi)(x)\big)=\varphi'(x)\mu(x)+\tfrac12\sum_{j=1}^m\varphi''(x)\big(\sigma_j(x),\sigma_j(x)\big),$$
--   and the noise term $\|\sigma(x)^*(\nabla\varphi)(x)\|^2=\sum_{j=1}^m\big(\varphi'(x)\sigma_j(x)\big)^2$.
--   6. **Stopping times** $\tau:\Omega\to[0,T]$ of the stochastic basis.
--
--   These objects enter the Lyapunov-type condition (7), the classes of coefficients of Proposition 3.3, and the stopping times of Theorem 2.10, Corollary 2.12 and Lemma 3.2.
--
--   **Formalization Note** States are `EuclideanSpace ℝ (Fin d)` and diffusion values the published `Diffusion d m = EuclideanSpace ℝ (Fin d × Fin m)`, whose norm is the Hilbert–Schmidt norm. Derivatives are Mathlib's `fderiv` and `iteratedFDeriv`, whose norms are the operator norms of the multilinear maps $f^{(i)}(x)$. In (12) the third derivative exists almost everywhere by Rademacher's theorem; where it does not, Lean's value is $0$, and that only happens on a null set. The paper's filtration is normal; a stopping time here is a map $\tau\le T$ with $\{\tau\le t\}$ in the $\mathbb P$-completion of $\mathcal F_t$ for every $t$ (the filtration to which the published `IsItoProcess` asks processes to be adapted).
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, pp. 5–6, (12), (13), (14); p. 16, Lemma 3.1 (ψ)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_SabanisEuler_Shared_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- The `j`-th column `A e_j ∈ ℝ^d` of a matrix `A ∈ ℝ^{d×m}` (stored as `Diffusion d m`,
whose norm is the Hilbert–Schmidt norm). Hutzenthaler–Jentzen, p. 6: `σ_i(x) = σ(x) e_i`. -/
def col {d m : ℕ} (A : Diffusion d m) (j : Fin m) : SDEState d :=
  WithLp.toLp 2 (fun i => A (i, j))

/-- The matrix–vector product `A w = ∑_j w_j A e_j ∈ ℝ^d` of `A ∈ ℝ^{d×m}` and `w ∈ ℝ^m`. -/
noncomputable def mulVec {d m : ℕ} (A : Diffusion d m) (w : SDEState m) : SDEState d :=
  ∑ j, w j • col A j

/-- The taming map `ψ(v) = v / (1 + ‖v‖²)` on `ℝ^d` (Hutzenthaler–Jentzen, p. 16, Lemma 3.1;
it is the map applied to the increments in (8), (63) and (76)). -/
noncomputable def tame {d : ℕ} (v : SDEState d) : SDEState d :=
  (1 + ‖v‖ ^ 2)⁻¹ • v

/-- Hutzenthaler–Jentzen, p. 6, (13): the class `𝒞¹_𝒫(ℝ^d, E)` of continuous maps that are
locally Lipschitz with a polynomially growing constant: there is `c ∈ [0, ∞)` with
`d_E(f(x), f(y)) ≤ c (1 + ‖x‖^c + ‖y‖^c) ‖x − y‖` for all `x, y` (real powers).
Despite its name this class does not require differentiability. -/
def IsPolyLocLip {d : ℕ} {E : Type*} [PseudoMetricSpace E] (f : SDEState d → E) : Prop :=
  Continuous f ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∀ x y : SDEState d, dist (f x) (f y) ≤ c * (1 + ‖x‖ ^ c + ‖y‖ ^ c) * ‖x - y‖

/-- Hutzenthaler–Jentzen, p. 6, (12): the class `𝒞³_𝒟(ℝ^d, ℝ)`. There are `p, c ∈ [3, ∞)`
such that `f` is `C²`, `f''` is locally Lipschitz, and for `i ∈ {1, 2, 3}` and Lebesgue-almost
every `x`, `‖f^{(i)}(x)‖ ≤ c |f(x)|^{1 − i/p}` (operator norm of the `i`-linear map
`f^{(i)}(x)`). The third derivative exists almost everywhere by Rademacher's theorem; where it does
not, Lean's `iteratedFDeriv ℝ 3 f x` is `0`, which only happens on a null set. -/
def IsC3D {d : ℕ} (f : SDEState d → ℝ) : Prop :=
  ∃ p c : ℝ, 3 ≤ p ∧ 3 ≤ c ∧ ContDiff ℝ 2 f ∧ LocallyLipschitz (iteratedFDeriv ℝ 2 f) ∧
    ∀ i ∈ Finset.Icc 1 3, ∀ᵐ x ∂(volume : Measure (SDEState d)),
      ‖iteratedFDeriv ℝ i f x‖ ≤ c * |f x| ^ (1 - (i : ℝ) / p)

/-- Hutzenthaler–Jentzen, p. 6, (14): the generator
`(𝒢_{µ,σ}φ)(x) = φ'(x) µ(x) + ½ tr(σ(x)σ(x)^* (Hess φ)(x))
             = φ'(x) µ(x) + ½ ∑_j φ''(x)(σ_j(x), σ_j(x))`. -/
noncomputable def generator {d m : ℕ} (mu : SDEState d → SDEState d)
    (sigma : SDEState d → Diffusion d m) (φ : SDEState d → ℝ) (x : SDEState d) : ℝ :=
  fderiv ℝ φ x (mu x) +
    (1 / 2) * ∑ j, iteratedFDeriv ℝ 2 φ x ![col (sigma x) j, col (sigma x) j]

/-- The squared noise term `‖σ(x)^* (∇φ)(x)‖² = ∑_j (φ'(x) σ_j(x))²` appearing in (7)
(Hutzenthaler–Jentzen, p. 4) and in Proposition 3.3 (p. 19). -/
noncomputable def noiseSq {d m : ℕ} (sigma : SDEState d → Diffusion d m)
    (φ : SDEState d → ℝ) (x : SDEState d) : ℝ :=
  ∑ j, (fderiv ℝ φ x (col (sigma x) j)) ^ 2

/-- A stopping time `τ : Ω → [0, T]` of the stochastic basis. The paper's filtration is normal;
here it is the `P`-completion of `ℱ` (`EthierKurtz.completedSDEPast`), the filtration to which the
published `IsItoProcess` asks processes to be adapted. -/
def IsStopTime {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) : Prop :=
  (∀ ω, τ ω ≤ T) ∧ ∀ t : ℝ≥0, MeasurableSet[completedSDEPast P ℱ t] {ω | τ ω ≤ t}

end PerturbSDE.StrongRate


