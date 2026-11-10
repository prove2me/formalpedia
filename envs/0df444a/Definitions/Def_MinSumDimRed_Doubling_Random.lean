-- Prove2me | Definitions.Def_MinSumDimRed_Doubling_Random
-- name    : MinSumDimRed_Doubling_Random
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:34:38.979893+00:00
-- url     : https://prove2.me/theorems/37673652-253b-4388-a246-fb5a424149b9
-- title:
--   Gaussian JL map, random maps and random subsets, and the $\mu$-local ball-tail property (Definition 2.4)
-- statement:
--   1. **Gaussian JL map** (p. 4): "a random linear map given by a matrix whose entries are independent $N(0, 1/t)$ random variables". The matrix is $W : $ `Fin t → Fin d → ℝ` drawn from `gaussianJLLaw t d` $=$ `UnderstandingML.gaussianMatrixLaw t d (1/t)` (the published law: product of `gaussianReal 0 (1/t)`, whose second argument is the **variance** $1/t$), and the map is `jlMap W` $: x \mapsto Wx$, $\mathbb R^d \to \mathbb R^t$ (Euclidean norm on $\mathbb R^t$).
--   2. **Random map** `IsRandomMap f`: on a measurable space $\Omega$, $f : \Omega \to (\mathbb R^d \to \mathbb R^t)$ with $\omega \mapsto f_\omega(x)$ measurable for every $x$.
--   3. **Random subset** `IsRandomSubset C`: $C : \Omega \to$ `Finset β` with every event $\{\omega : x \in C_\omega\}$ measurable. A random subset "which may depend on $f$" is any such $C$ on the probability space carrying $f$.
--   4. **$\mu$-local ball-tail property** (Definition 2.4, p. 10) `HasLocalBallTail μ f X mu`: for every $y \in X$ and $r > 0$,
--   $$\Pr\big[\exists x \in X \cap B(y, r),\ \|f(x) - f(y)\| \ge 10 r\big] \le e^{-\mu},$$
--   with the closed ball $B(y, r)$ and probability $\mu.\mathrm{real}$ of the event (the parameter is written `mu`, the probability measure `μ`).
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 4 (PDF 4, Gaussian JL map), p. 10 (Definition 2.4), p. 13 (random subsets)

import Mathlib
import Definitions.Def_UnderstandingML_DimReduction
import Definitions.Def_MinSumDimRed_Doubling_Costs

open MeasureTheory ProbabilityTheory

namespace MinSumDimRed.Doubling

/-!
# The Gaussian JL map, random maps, random subsets and the local ball-tail property

Dallal, Krauthgamer, *Dimension Reduction and Coresets for Min-Sum k-Clustering*,
arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…): p. 4 ("a Gaussian JL map
f : ℝ^d → ℝ^t refers to a random linear map given by a matrix whose entries are independent
N(0, 1/t) random variables"), p. 10, Definition 2.4 (µ-local ball-tail property), p. 13
("random subset C ⊆ X which may depend on f").

**Formalization Note.** The Gaussian JL map is the matrix `W : Fin t → Fin d → ℝ` drawn from the
published `UnderstandingML.gaussianMatrixLaw t d (1/t)` (entries i.i.d. `gaussianReal 0 (1/t)`,
whose second argument is the **variance**), acting by `x ↦ W x`. A random map / random subset is a
function on one probability space `(Ω, μ)` that is a random variable: each `ω ↦ f ω x` is
measurable, each membership event `{ω | x ∈ C ω}` is measurable. Probabilities are `μ.real`. -/

/-- The linear map `x ↦ W x` of the `t × d` matrix `W`, as a map `ℝ^d → ℝ^t`. -/
noncomputable def jlMap {t d : ℕ} (W : Fin t → Fin d → ℝ) (x : Pt d) : Pt t :=
  WithLp.toLp 2 (Matrix.mulVec (Matrix.of W) (WithLp.ofLp x))

/-- The law of the Gaussian JL matrix: a `t × d` matrix with independent `N(0, 1/t)` entries. -/
noncomputable def gaussianJLLaw (t d : ℕ) : Measure (Fin t → Fin d → ℝ) :=
  UnderstandingML.gaussianMatrixLaw t d (t : NNReal)⁻¹

/-- A random map `f : ℝ^d → ℝ^t` on the sample space `Ω`: `ω ↦ f ω x` is measurable for each
`x`. -/
def IsRandomMap {Ω : Type*} [MeasurableSpace Ω] {d t : ℕ} (f : Ω → Pt d → Pt t) : Prop :=
  ∀ x : Pt d, Measurable (fun ω => f ω x)

/-- A random subset of the finite set `β` on the sample space `Ω`: every membership event
`{ω | x ∈ C ω}` is measurable. -/
def IsRandomSubset {Ω β : Type*} [MeasurableSpace Ω] (C : Ω → Finset β) : Prop :=
  ∀ x : β, MeasurableSet {ω | x ∈ C ω}

/-- Definition 2.4: the random map `f` (on `(Ω, μ)`) has the `µ`-local ball-tail property for
`X ⊆ ℝ^d`: for every `y ∈ X` and `r > 0`,
`Pr[∃ x ∈ X ∩ B(y, r), ‖f(x) - f(y)‖ ≥ 10 r] ≤ e^{-µ}` (closed ball). -/
def HasLocalBallTail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d t : ℕ}
    (f : Ω → Pt d → Pt t) (X : Set (Pt d)) (mu : ℝ) : Prop :=
  ∀ y ∈ X, ∀ r : ℝ, 0 < r →
    μ.real {ω | ∃ x ∈ X, dist x y ≤ r ∧ 10 * r ≤ ‖f ω x - f ω y‖} ≤ Real.exp (-mu)

end MinSumDimRed.Doubling


