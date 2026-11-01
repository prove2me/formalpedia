-- Prove2me | Definitions.Def_ExploreLQMFG_Model
-- name    : ExploreLQMFG_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:05.097521+00:00
-- url     : https://prove2.me/theorems/bd324872-ee24-46ed-bae2-70edb8055812
-- title:
--   Euclidean and $\|\cdot\|_{1,\infty}$ norms, the Riccati equation (2.3), the augmented filtration $\mathbb F^W$ and the geometric weight of (2.10)
-- statement:
--   This item fixes the standing data of the mission.
--
--   1. $\mathbb R^d$ carries the Euclidean norm $|x|=(\sum_i x_i^2)^{1/2}$; $d\times d$ matrices carry the Frobenius norm $|M|=(\sum_{i,j}M_{ij}^2)^{1/2}$.
--   2. A map $F:\mathbb R^d\to\mathbb R^d$ is *bounded and Lipschitz* when $\sup_x|F(x)|<\infty$ and $|F(x)-F(x')|\le L|x-x'|$ for some $L$, and
--   $$\|F\|_{1,\infty}=\sup_{x\in\mathbb R^d}|F(x)|+\sup_{x\neq x'}\frac{|F(x)-F(x')|}{|x-x'|}.$$
--   3. For a $d\times d$ matrix $Q$, $Q^\dagger f$ denotes the map $x\mapsto Q^\dagger(f(x))$, with $\dagger$ the transpose.
--   4. The Riccati equation (2.3): $\eta:[0,T]\to\mathbb R^{d\times d}$ with
--   $$\dot\eta_t-\eta_t^2+Q^\dagger Q=0,\quad t\in[0,T];\qquad \eta_T=R^\dagger R,$$
--   the derivative taken entrywise and one-sided at the endpoints.
--   5. The augmented filtration $\mathbb F^W$ of a $d$-dimensional Brownian motion $W$: $\mathcal F^W_t=\sigma(W_s,\,s\le t)\vee\mathcal N$, with $\mathcal N$ the null sets.
--   6. The geometric weight $c_n=\dfrac{(1-\varpi^{-1})\varpi^{-n}}{1-\varpi^{-(n+1)}}$ of the forward equation in (2.10); $c_0=1$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ`, whose Mathlib norm is the sup norm, so the Euclidean norm is written out. The suprema in $\|F\|_{1,\infty}$ are real suprema; for bounded Lipschitz $F$ (assumed of $f$ and $g$ in every statement) they are the true suprema. The filtration is built on the published natural filtration `Peng1990.SMP.brownianFiltration`; on a complete probability space it is the usual augmentation.
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), §1.9.1 p.18 (‖·‖_{1,∞}), footnote 1 p.3, Lemma 2.1(i) (2.3) p.20, §1.9.2 p.19 (𝔽^W), (2.9)–(2.10) pp.20–21

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

namespace ExploreLQMFG

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The squared Euclidean norm `|x|² = Σᵢ xᵢ²` of `x ∈ ℝᵈ` (Delarue & Vasileiadis,
arXiv:2107.00839v2, §1.2, p.3: `|·|` is the Euclidean norm).

**Formalization Note.** `ℝᵈ` is `Fin d → ℝ`; Mathlib's default norm on that type is the sup
norm, so the paper's `|·|` is written out explicitly. -/
def eSq {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The Euclidean norm `|x| = (Σᵢ xᵢ²)^{1/2}` on `ℝᵈ` (arXiv:2107.00839v2, p.3). -/
noncomputable def eNorm {d : ℕ} (x : Fin d → ℝ) : ℝ := Real.sqrt (eSq x)

/-- The Frobenius norm `|M| = (Σᵢⱼ Mᵢⱼ²)^{1/2}` of a `d × d` real matrix; used for the
matrix-valued processes `k` and for the Jacobian `∇ₓθ`.

**Formalization Note.** The paper writes `|k|` and `|∇ₓθ|` without naming the matrix norm;
all matrix norms on `ℝ^{d×d}` are equivalent up to a factor depending only on `d`, which the
constants of the paper (depending on `d`) absorb. -/
noncomputable def frob {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- `F : ℝᵈ → ℝᵈ` is bounded and Lipschitz continuous for the Euclidean norm, the standing
assumption on the coefficients `f` and `g` (arXiv:2107.00839v2, §1.9.1, pp.18–19). -/
def IsBddLip {d : ℕ} (F : (Fin d → ℝ) → (Fin d → ℝ)) : Prop :=
  (∃ M : ℝ, ∀ x, eNorm (F x) ≤ M) ∧
    ∃ L : ℝ, ∀ x y, eNorm (F x - F y) ≤ L * eNorm (x - y)

/-- The norm `‖F‖_{1,∞} = sup_x |F(x)| + sup_{x ≠ x'} |F(x) − F(x')| / |x − x'|`
(arXiv:2107.00839v2, §1.9.1, p.18).

**Formalization Note.** Both suprema are real `⨆`s over nonempty index types. For a bounded
Lipschitz `F` (`IsBddLip F`, which every statement of the mission assumes of `f` and `g`, hence
of `Q†f` and `R†g`) both families are bounded above, so the value is the paper's norm. When
`d = 0` the second index type is empty and the second term is `0`, the paper's convention for
an empty supremum of nonnegative numbers. -/
noncomputable def oneInfNorm {d : ℕ} (F : (Fin d → ℝ) → (Fin d → ℝ)) : ℝ :=
  (⨆ x, eNorm (F x)) +
    ⨆ p : {p : (Fin d → ℝ) × (Fin d → ℝ) // p.1 ≠ p.2},
      eNorm (F p.1.1 - F p.1.2) / eNorm (p.1.1 - p.1.2)

/-- The map `Q†F : x ↦ Q†(F(x))`, with `†` the transpose (arXiv:2107.00839v2, footnote 1,
p.3, and §2.1). The mission writes `tmul Q f` for the paper's `Q†f`. -/
def tmul {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (F : (Fin d → ℝ) → (Fin d → ℝ)) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => Qᵀ *ᵥ F x

/-- `η : [0, T] → ℝ^{d×d}` solves the Riccati equation (2.3) of arXiv:2107.00839v2 (Lemma 2.1(i),
p.20):  `η̇_t − η_t² + Q†Q = 0` for `t ∈ [0, T]`, `η_T = R†R`.

**Formalization Note.** `η` is a function `ℝ → ℝ^{d×d}`; only its values on `[0, T]` matter.
The derivative is taken entrywise, within `[0, T]` (one-sided at the endpoints), so `η` is
`C¹` on `[0, T]` (the derivative `η² − Q†Q` is continuous). The equation has exactly one
solution on `[0, T]` (standard LQ theory: it is symmetric and positive semidefinite). -/
def IsRiccatiSol {d : ℕ} (Q R : Matrix (Fin d) (Fin d) ℝ) (T : ℝ≥0)
    (η : ℝ → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j,
      HasDerivWithinAt (fun s => η s i j) ((η t * η t - Qᵀ * Q) i j) (Set.Icc (0 : ℝ) T) t) ∧
    η T = Rᵀ * R

/-- The σ-algebra generated by the `P`-null measurable sets. -/
abbrev nullSigma (P : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {N | MeasurableSet N ∧ P N = 0}

/-- The augmented filtration `𝔽^W` of the `d`-dimensional Brownian motion `W`
(arXiv:2107.00839v2, §1.9.2, p.19): `𝔽^W_t = σ(W_s, s ≤ t) ∨ 𝒩`, with `𝒩` the `P`-null sets.

**Formalization Note.** On a complete probability space (the paper's setting, assumed by every
statement of the mission through `P.IsComplete`) the null sets of `𝒜` are all subsets of null
sets, so this is the usual augmentation. It is built on the published natural filtration
`Peng1990.SMP.brownianFiltration`. -/
noncomputable def augFiltration {d : ℕ} {P : Measure Ω} {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : Peng1990.SMP.IsStdBrownian P W) : Filtration ℝ≥0 mΩ where
  seq t := Peng1990.SMP.brownianFiltration hW t ⊔ nullSigma P
  mono' _ _ hst := sup_le_sup_right ((Peng1990.SMP.brownianFiltration hW).mono hst) _
  le' t := sup_le ((Peng1990.SMP.brownianFiltration hW).le t)
    (MeasurableSpace.generateFrom_le fun _ hN => hN.1)

/-- The geometric weight `(1 − ϖ⁻¹) ϖ⁻ⁿ / (1 − ϖ^{−(n+1)})` in front of `hⁿ⁺¹` in the forward
equations (2.9)–(2.10) of arXiv:2107.00839v2 (p.20–21). For `ϖ > 1` the denominator is
positive, and the weight at `n = 0` is `1`. -/
noncomputable def geomWeight (ϖ : ℝ) (n : ℕ) : ℝ :=
  (1 - ϖ⁻¹) * ϖ ^ (-(n : ℤ)) / (1 - ϖ ^ (-((n : ℤ) + 1)))

end ExploreLQMFG


