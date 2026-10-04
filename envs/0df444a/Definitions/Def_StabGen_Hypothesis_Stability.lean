-- Prove2me | Definitions.Def_StabGen_Hypothesis_Stability
-- name    : StabGen_Hypothesis_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:48:35.666795+00:00
-- url     : https://prove2.me/theorems/e3ed1dfd-d775-4602-9957-2e32fd0c382a
-- title:
--   Hypothesis stability and pointwise hypothesis stability (Definitions 3 and 4)
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let $S = (z_1, \dots, z_m)$ be drawn from $D^m$ and let $z \sim D$ be independent of $S$. Write $\ell(f, z) = c(f(x), y)$ for the loss and $A_{S^{\setminus i}}$ for the hypothesis trained on $S$ with the $i$-th example removed.
--
--   1. (**Hypothesis stability**, Definition 3.) $A$ has hypothesis stability $\beta$ with respect to $\ell$ if
--   $$\forall i \in \{1, \dots, m\}, \quad \mathbb E_{S,z}\bigl[\,|\ell(A_S, z) - \ell(A_{S^{\setminus i}}, z)|\,\bigr] \le \beta .$$
--   2. (**Pointwise hypothesis stability**, Definition 4.) $A$ has pointwise hypothesis stability $\beta$ with respect to $\ell$ if
--   $$\forall i \in \{1, \dots, m\}, \quad \mathbb E_{S}\bigl[\,|\ell(A_S, z_i) - \ell(A_{S^{\setminus i}}, z_i)|\,\bigr] \le \beta .$$
--
--   The first measures the average change of the loss at a fresh point when one training example is removed; the second measures the change at the removed example itself. They are the hypotheses of the polynomial generalization bound, Theorem 11.
--
--   **Formalization Note** Both notions are stated for a fixed sample size $m$ and distribution $D$: `HypothesisStable D L A m β` and `PointwiseHypothesisStable D L A m β`. $\mathbb E_{S,z}$ is the integral against $D^m \otimes D$, $\mathbb E_S$ against $D^m$. Each clause also requires the integrand to be integrable, so that the expectation is a genuine one and not Lean's default value $0$ for non-integrable functions; under the bounded measurable losses of this mission this requirement holds automatically.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 503, Definition 3 (eq. (3)) and Definition 4 (eq. (4))

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_StabGen_Hypothesis_Setting

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

/-- **Hypothesis stability** (Bousquet & Elisseeff 2002, Definition 3, p. 503, eq. (3)).
An algorithm `A` has hypothesis stability `β` with respect to the loss `ℓ(f, (x, y)) = L (f x) y`
at sample size `m` and distribution `D` if for every `i ∈ {1, …, m}`
`E_{S,z} [|ℓ(A_S, z) − ℓ(A_{S^{\i}}, z)|] ≤ β`, where `S ∼ D^m` and `z ∼ D` is independent of `S`.
The pair `(S, z)` has law `D^m ⊗ D`. The integrand is required to be integrable, so that the
expectation is a genuine one and not Lean's default value `0`. -/
def HypothesisStable {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) (L : Y' → Y → ℝ) (A : LearningAlgorithm X Y Y') (m : ℕ) (β : ℝ) :
    Prop :=
  ∀ i : Fin m,
    Integrable (fun p : (Fin m → X × Y) × (X × Y) =>
        |Loss L (A (trainingSet p.1)) p.2 - Loss L (A (removeAt p.1 i)) p.2|)
      ((Measure.pi fun _ : Fin m => D).prod D) ∧
    ∫ p : (Fin m → X × Y) × (X × Y),
        |Loss L (A (trainingSet p.1)) p.2 - Loss L (A (removeAt p.1 i)) p.2|
      ∂((Measure.pi fun _ : Fin m => D).prod D) ≤ β

/-- **Pointwise hypothesis stability** (Bousquet & Elisseeff 2002, Definition 4, p. 503,
eq. (4)). An algorithm `A` has pointwise hypothesis stability `β` with respect to the loss `ℓ`
at sample size `m` and distribution `D` if for every `i ∈ {1, …, m}`
`E_S [|ℓ(A_S, z_i) − ℓ(A_{S^{\i}}, z_i)|] ≤ β`, where `S = (z_1, …, z_m) ∼ D^m`.
The integrand is required to be integrable. -/
def PointwiseHypothesisStable {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) (L : Y' → Y → ℝ) (A : LearningAlgorithm X Y Y') (m : ℕ) (β : ℝ) :
    Prop :=
  ∀ i : Fin m,
    Integrable (fun S : Fin m → X × Y =>
        |Loss L (A (trainingSet S)) (S i) - Loss L (A (removeAt S i)) (S i)|)
      (Measure.pi fun _ : Fin m => D) ∧
    ∫ S : Fin m → X × Y,
        |Loss L (A (trainingSet S)) (S i) - Loss L (A (removeAt S i)) (S i)|
      ∂(Measure.pi fun _ : Fin m => D) ≤ β

end StabGen.Hypothesis


