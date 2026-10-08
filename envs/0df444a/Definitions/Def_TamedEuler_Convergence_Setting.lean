-- Prove2me | Definitions.Def_TamedEuler_Convergence_Setting
-- name    : TamedEuler_Convergence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:52.742113+00:00
-- url     : https://prove2.me/theorems/381b9395-3a4f-4023-a883-dc4fdc5d7e8f
-- title:
--   p. 2 — standing setting: Brownian motion, ξ with all moments, C¹ one-sided Lipschitz µ with polynomially growing derivative, Lipschitz σ (operator norm)
-- statement:
--   This file fixes the standing setting of Hutzenthaler, Jentzen and Kloeden (2012), §1, p. 2, which holds "throughout the whole article".
--
--   **Norms.** On $\mathbb R^k$, $\|v\|$ is the Euclidean norm and $\langle v,w\rangle$ the Euclidean inner product. For a matrix $A\in\mathbb R^{k\times l}$,
--   $$\|A\| := \sup_{v\in\mathbb R^l,\ \|v\|\le 1}\|Av\|$$
--   is the **operator norm** (not the Frobenius norm). We also name the matrix–vector product $Av$ and the $i$-th column $A\vec e_i$, and a map `toDiffusion` that reads a matrix $A\in\mathbb R^{d\times m}$ entrywise as a value of the published diffusion type used to state the SDE; only the entries are used there.
--
--   **Coefficients.** Let $d,m\in\mathbb N=\{1,2,\dots\}$ and $T\in(0,\infty)$. Let $\mu:\mathbb R^d\to\mathbb R^d$ and $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$. The coefficient hypotheses hold when there is one real number $c\in(0,\infty)$ such that $\mu$ is continuously differentiable and, for all $x,y\in\mathbb R^d$,
--   $$\|\mu'(x)\|\le c\,(1+\|x\|^c),\qquad \|\sigma(x)-\sigma(y)\|\le c\,\|x-y\|,\qquad \langle x-y,\mu(x)-\mu(y)\rangle\le c\,\|x-y\|^2 .$$
--   Here $\|\mu'(x)\|$ is the operator norm of the derivative and $\|x\|^c$ a real power.
--
--   **Full setting.** In addition, $(\Omega,\mathcal F,\mathbb P)$ is a probability space with a filtration $(\mathcal F_t)_{t\ge0}$, $W$ is an $m$-dimensional standard $(\mathcal F_t)$-Brownian motion, and the initial value $\xi:\Omega\to\mathbb R^d$ is $\mathcal F_0$-measurable with $\mathbb E[\|\xi\|^p]<\infty$ for every $p\in[1,\infty)$.
--
--   These are the hypotheses of Theorem 1.1 and of Lemmas 3.1, 3.3–3.6, 3.9 and 3.10. They allow superlinearly growing drifts such as $\mu(x)=x-x^3$, for which the explicit Euler scheme diverges in $L^p$.
--
--   **Formalization Note** The paper's filtration is "normal" (complete and right-continuous). Right-continuity is a field of the structure; completeness is handled by the published `IsSolution`, which asks adaptedness to the filtration augmented by the $\mathbb P$-null sets. The paper's $W$ lives on $[0,T]$; here it is the published `IsWienerMartingale` on $[0,\infty)$, the usual extension. One constant $c$ plays both roles, constant and growth exponent, as on p. 2. Moments of $\xi$ are stated as membership in $L^p$ for each real $p\ge1$.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 2, standing setting and (1)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

/-- Hutzenthaler–Jentzen–Kloeden, p. 2: `‖A‖ := sup_{v ∈ ℝˡ, ‖v‖ ≤ 1} ‖A v‖` for
`A ∈ ℝ^{k×l}`, the operator norm of `A` between the Euclidean spaces `ℝˡ` and `ℝᵏ`
(not the Frobenius norm). -/
noncomputable def opNorm {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- The matrix–vector product `A v ∈ ℝᵏ` of `A ∈ ℝ^{k×l}` and `v ∈ ℝˡ`. -/
noncomputable def matVec {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℝ) (v : SDEState l) :
    SDEState k :=
  Matrix.toEuclideanLin A v

/-- The `i`-th column `A e⃗ᵢ ∈ ℝᵏ` of `A ∈ ℝ^{k×l}`. -/
def column {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℝ) (i : Fin l) : SDEState k :=
  WithLp.toLp 2 (fun r => A r i)

/-- The same matrix `A ∈ ℝ^{d×m}`, read entrywise as a value of the published type
`SabanisEuler.Shared.Diffusion d m`. Only the entries are used (to state the SDE (2)); no
norm of this type enters any hypothesis or conclusion of the mission. -/
def toDiffusion {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) : SabanisEuler.Shared.Diffusion d m :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

/-- Hutzenthaler–Jentzen–Kloeden, p. 2: the deterministic part of the standing setting.
`d, m ∈ ℕ = {1, 2, …}`, `T ∈ (0, ∞)`, and there is one real `c ∈ (0, ∞)` such that
`µ : ℝᵈ → ℝᵈ` is continuously differentiable with `‖µ'(x)‖ ≤ c (1 + ‖x‖^c)` (operator norm of
the derivative, real power), `σ : ℝᵈ → ℝ^{d×m}` satisfies `‖σ(x) − σ(y)‖ ≤ c ‖x − y‖`
(operator norm), and `⟨x − y, µ(x) − µ(y)⟩ ≤ c ‖x − y‖²` for all `x, y ∈ ℝᵈ`. -/
structure Coefficients (d m : ℕ) (T : ℝ≥0) (c : ℝ) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ) : Prop where
  one_le_d : 1 ≤ d
  one_le_m : 1 ≤ m
  T_pos : 0 < T
  c_pos : 0 < c
  contDiff : ContDiff ℝ 1 mu
  deriv_growth : ∀ x, ‖fderiv ℝ mu x‖ ≤ c * (1 + ‖x‖ ^ c)
  sigma_lipschitz : ∀ x y, opNorm (σ x - σ y) ≤ c * ‖x - y‖
  one_sided : ∀ x y, inner ℝ (x - y) (mu x - mu y) ≤ c * ‖x - y‖ ^ 2

/-- Hutzenthaler–Jentzen–Kloeden, p. 2: the full standing setting. On top of
`Coefficients`: `P` is a probability measure, the filtration `ℱ` is right-continuous (the
completeness half of "normal filtration" is carried by the published `IsSolution`, which asks
adaptedness to the `P`-completed filtration), `W` is an `m`-dimensional standard
`(ℱ_t)`-Brownian motion (`SabanisEuler.Shared.IsWienerMartingale`, on `[0, ∞)`), and the
initial value `ξ : Ω → ℝᵈ` is `ℱ₀`-measurable with `𝔼‖ξ‖ᵖ < ∞` for all `p ∈ [1, ∞)`. -/
structure Setting {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (c : ℝ) (W : ℝ≥0 → Ω → SDEState m)
    (ξ : Ω → SDEState d) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ) : Prop
    extends Coefficients d m T c mu σ where
  isProbability : IsProbabilityMeasure P
  rightContinuous : ℱ.IsRightContinuous
  wiener : SabanisEuler.Shared.IsWienerMartingale P ℱ W
  xi_measurable : Measurable[ℱ 0] ξ
  xi_moments : ∀ p : ℝ, 1 ≤ p → MemLp ξ (ENNReal.ofReal p) P

end TamedEuler.Convergence


