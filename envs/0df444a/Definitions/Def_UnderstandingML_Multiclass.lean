-- Prove2me | Definitions.Def_UnderstandingML_Multiclass
-- name    : UnderstandingML_Multiclass
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T04:51:40.665894+00:00
-- url     : https://prove2.me/theorems/c864a2b4-4620-4d4c-83b9-2871fe4be684
-- title:
--   Chapter 17: argmax predictors for class-sensitive feature maps, the generalized hinge loss (17.3), the cost-sensitive loss, linear ranking predictors, the Kendall tau loss and its surrogate
-- statement:
--   Chapter 17 of Shalev-Shwartz and Ben-David. For a class-sensitive feature mapping $\Psi : X \times Y \to \mathbb{R}^d$ (finite nonempty $Y$) and $w$, an **argmax predictor** $h$ has $h(x) \in \operatorname{argmax}_y \langle w, \Psi(x,y)\rangle$ (`IsArgmaxPredictor`), with a canonical choice `argmaxPredict`. For a cost $\Delta : Y \times Y \to \mathbb{R}_+$, the **generalized hinge loss** (17.3) is $\ell(w,(x,y)) = \max_{y'}(\Delta(y',y) + \langle w, \Psi(x,y') - \Psi(x,y)\rangle)$ (`genHingeLoss`), with a canonical maximizer `genHingeArgmax` and the SGD direction $\Psi(x,\hat y) - \Psi(x,y)$ (`genHingeDirection`, §17.2.5); the cost-sensitive loss $\Delta(h_w(x), y)$ of the canonical predictor (`deltaLoss`). **Ranking (§17.4):** the linear ranking predictor $h_w(x_1,\dots,x_r) = (\langle w, x_1\rangle, \dots, \langle w, x_r\rangle)$ (`rankingPredict`), the **Kendall tau loss** $\frac{2}{r(r-1)}\sum_{i<j}\mathbb{1}[\operatorname{sign}(y'_i - y'_j) \ne \operatorname{sign}(y_i - y_j)]$ (`kendallTauLoss`, with the three-valued real sign), its hinge surrogate $\frac{2}{r(r-1)}\sum_{i<j}\max\{0, 1 - \operatorname{sign}(y_i - y_j)\langle w, x_i - x_j\rangle\}$ (`kendallTauSurrogate`), and the matrix inner product $\langle A, B\rangle = \sum_{ij}A_{ij}B_{ij}$ (`matrixInner`). Doubly stochastic and permutation matrices are Mathlib's.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §17.2 pp. 230-235 (HΨ,W, cost-sensitive loss, Equation (17.3), Multiclass SVM and SGD), §17.4 pp. 238-242 (Equation (17.6), Kendall tau loss and its hinge surrogate, ⟨A, B⟩)

import Definitions.Def_UnderstandingML_SGD
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Real.Sign

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 17:
# multiclass and ranking

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §17.2 and §17.4.

**Linear multiclass predictors (§17.2).** A class-sensitive feature mapping `Ψ : X × Y → ℝ^d`
and a vector `w` define the predictor `h_w(x) = argmax_{y ∈ Y} ⟨w, Ψ(x, y)⟩`. A cost-sensitive loss
`Δ : Y × Y → ℝ₊` with `Δ(y, y) = 0` gives the loss `Δ(h_w(x), y)`, and the **generalized hinge
loss** (17.3) is `ℓ(w, (x, y)) = max_{y' ∈ Y} (Δ(y', y) + ⟨w, Ψ(x, y') − Ψ(x, y)⟩)`. Multiclass SVM is
the RLM rule for `ℓ`; SGD for multiclass learning uses the directions `Ψ(x, ŷ) − Ψ(x, y)` with
`ŷ` a maximizer in (17.3).

**Ranking (§17.4).** A linear ranking predictor `h_w(x₁, …, x_r) = (⟨w, x₁⟩, …, ⟨w, x_r⟩)` (17.6);
the Kendall tau loss counts discordant pairs; permutations are encoded as vectors `v ∈ [r]^r`,
and the induced permutation `π(y)` maximizes `∑ vᵢ yᵢ` (17.7). Doubly stochastic and permutation
matrices are Mathlib's `doublyStochastic` and `Equiv.Perm.permMatrix`.

**Conventions.** `Y` is a finite nonempty type; maxima over `Y` are real suprema `⨆`, which are
attained. The argmax predictor and the maximizer in (17.3) are chosen canonically among the
maximizers (`Classical.choose`); every statement about them holds for any choice. Labels of a
ranking example are real vectors `y : Fin r → ℝ`, with `Real.sign` (three-valued) as the sign.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

section Multiclass

variable {d : ℕ} {X Y : Type*} [Fintype Y] [Nonempty Y]

/-- `h` is an **argmax predictor** for `(Ψ, w)`: `h(x) ∈ argmax_{y ∈ Y} ⟨w, Ψ(x, y)⟩` for every `x`
(§17.2). -/
def IsArgmaxPredictor (Ψ : X → Y → Vec d) (w : Vec d) (h : X → Y) : Prop :=
  ∀ x y, ⟪w, Ψ x y⟫_ℝ ≤ ⟪w, Ψ x (h x)⟫_ℝ

/-- A canonical argmax predictor `h_w(x) = argmax_{y ∈ Y} ⟨w, Ψ(x, y)⟩` (§17.2), with ties broken
by a fixed choice. -/
noncomputable def argmaxPredict (Ψ : X → Y → Vec d) (w : Vec d) (x : X) : Y :=
  Classical.choose (Finset.exists_max_image Finset.univ (fun y ↦ ⟪w, Ψ x y⟫_ℝ)
    Finset.univ_nonempty)

/-- The **generalized hinge loss** (17.3):
`ℓ(w, (x, y)) = max_{y' ∈ Y} (Δ(y', y) + ⟨w, Ψ(x, y') − Ψ(x, y)⟩)`. -/
noncomputable def genHingeLoss (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) :
    ℝ :=
  ⨆ y' : Y, (Δ y' z.2 + ⟪w, Ψ z.1 y' - Ψ z.1 z.2⟫_ℝ)

/-- A canonical maximizer `ŷ ∈ argmax_{y' ∈ Y} (Δ(y', y) + ⟨w, Ψ(x, y') − Ψ(x, y)⟩)` used by SGD for
multiclass learning (§17.2.5). -/
noncomputable def genHingeArgmax (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) :
    Y :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun y' ↦ Δ y' z.2 + ⟪w, Ψ z.1 y' - Ψ z.1 z.2⟫_ℝ) Finset.univ_nonempty)

/-- The subgradient direction `vₜ = Ψ(x, ŷ) − Ψ(x, y)` of SGD for multiclass learning (§17.2.5),
as an oracle for the SGD of Chapter 14. -/
noncomputable def genHingeDirection (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d)
    (z : X × Y) : Vec d :=
  Ψ z.1 (genHingeArgmax Δ Ψ w z) - Ψ z.1 z.2

/-- The cost-sensitive loss `Δ(h_w(x), y)` of the canonical argmax predictor (§17.2.2). -/
noncomputable def deltaLoss (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) : ℝ :=
  Δ (argmaxPredict Ψ w z.1) z.2

end Multiclass

/-! ### Ranking (§17.4) -/

section Ranking

variable {d r : ℕ}

/-- The linear ranking predictor `h_w(x₁, …, x_r) = (⟨w, x₁⟩, …, ⟨w, x_r⟩)` (17.6). -/
noncomputable def rankingPredict (w : Vec d) (xs : Fin r → Vec d) : Fin r → ℝ :=
  fun i ↦ ⟪w, xs i⟫_ℝ

/-- The **Kendall tau loss** between the score vectors `y'` and `y`: the fraction of pairs
`i < j` ordered differently, `(2/(r(r−1))) ∑_{i<j} 𝟙[sign(y'ᵢ − y'ⱼ) ≠ sign(yᵢ − yⱼ)]` (§17.4). -/
noncomputable def kendallTauLoss (y' y : Fin r → ℝ) : ℝ :=
  (2 / (r * (r - 1))) * ∑ i, ∑ j, if i < j then
    (if Real.sign (y' i - y' j) ≠ Real.sign (y i - y j) then 1 else 0) else 0

/-- The hinge surrogate for the Kendall tau loss (§17.4.1):
`(2/(r(r−1))) ∑_{i<j} max{0, 1 − sign(yᵢ − yⱼ)⟨w, xᵢ − xⱼ⟩}`. -/
noncomputable def kendallTauSurrogate (w : Vec d) (xs : Fin r → Vec d) (y : Fin r → ℝ) : ℝ :=
  (2 / (r * (r - 1))) * ∑ i, ∑ j, if i < j then
    max 0 (1 - Real.sign (y i - y j) * ⟪w, xs i - xs j⟫_ℝ) else 0

/-- The inner product `⟨A, B⟩ = ∑ᵢⱼ Aᵢⱼ Bᵢⱼ` of matrices (§17.4.1). -/
def matrixInner (A B : Matrix (Fin r) (Fin r) ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

end Ranking

end UnderstandingML


