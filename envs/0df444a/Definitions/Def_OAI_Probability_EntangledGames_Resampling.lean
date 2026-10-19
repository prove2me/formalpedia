-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_Resampling
-- name    : OAI_Probability_EntangledGames_Resampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:09:29.161065+00:00
-- url     : https://prove2.me/theorems/7966b03f-f289-4452-97b2-f5fe09248ba9
-- title:
--   Resampling one player's question at a coordinate from its conditional law
-- statement:
--   Let $X$ and $Y$ be finite sets of questions for two players, $I$ a finite set of coordinates and $E$ a real vector space. A profile is a function $z:I\to X\times Y$, $z_i=(z_i^X,z_i^Y)$, assigning a question pair to every coordinate. Let $\mu$ be a probability law on $X\times Y$. Write $\mu(\cdot\mid y)$ for the conditional law of the first coordinate given that the second equals $y$, and $\mu(\cdot\mid x)$ for the conditional law of the second coordinate given that the first equals $x$; when the conditioning value has probability $0$, the conditional law is the point mass at a fixed default $x_0\in X$, respectively $y_0\in Y$.
--
--   1. **Updates.** $z[i\mapsto_X x]$ replaces the first entry of $z_i$ by $x$, and $z[i\mapsto_Y y]$ replaces the second entry of $z_i$ by $y$; all other entries are unchanged.
--   2. **One-coordinate resampling operators.** For $f:(X\times Y)^I\to E$ and $i\in I$,
--   $$(\mathcal L_if)(z)=\mathbb{E}_{x\sim\mu(\cdot\mid z_i^Y)}\,f\bigl(z[i\mapsto_X x]\bigr),\qquad(\mathcal R_if)(z)=\mathbb{E}_{y\sim\mu(\cdot\mid z_i^X)}\,f\bigl(z[i\mapsto_Y y]\bigr).$$
--   Thus $\mathcal L_i$ redraws Alice's question at coordinate $i$ from its conditional law given Bob's question there, and $\mathcal R_i$ does the same for Bob's question.
--   3. **Independence predicates.** $f$ ignores the left entry at $i$ if $f(z[i\mapsto_X x])=f(z)$ for all $z$ and $x$; symmetrically, $f$ ignores the right entry at $i$ if $f(z[i\mapsto_Y y])=f(z)$ for all $z$ and $y$.
--   4. **Iterated resampling.** For a list $l=(i_1,\dots,i_k)$ of coordinates, $\mathcal L_lf=\mathcal L_{i_1}\mathcal L_{i_2}\cdots\mathcal L_{i_k}f$ and $\mathcal R_lf=\mathcal R_{i_1}\mathcal R_{i_2}\cdots\mathcal R_{i_k}f$; for the empty list both equal $f$.
--
--   The file proves that iterated resampling is additive over finite sums: for every finite family $(f_r)_{r\in R}$ and every profile $z$,
--   $$\mathcal L_l\Bigl(\sum_rf_r\Bigr)(z)=\sum_r(\mathcal L_lf_r)(z),\qquad\mathcal R_l\Bigl(\sum_rf_r\Bigr)(z)=\sum_r(\mathcal R_lf_r)(z).$$
--
--   Under the product law $\mu^{\otimes I}$ of independent question pairs, redrawing one player's question from its conditional law leaves the joint distribution unchanged, so $\mathcal L_i$ and $\mathcal R_i$ preserve expectations under $\mu^{\otimes I}$. They are used to average operator-valued functions of the questions coordinate by coordinate, removing the dependence on one player's questions while leaving functions that ignore those entries untouched.
--
--   **Formalization Note** Profiles are `Profile I X Y := I → X × Y`; the operators are `left μ x₀ i f` and `right μ y₀ i f`, built from the conditional laws `givenSecond` and `givenFirst`, and the update maps are `updateLeft` and `updateRight`. `lefts` and `rights` are `List.foldr` of these operators, so the head of the list is the outermost operator. The predicates are `IgnoresLeft` and `IgnoresRight`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Resampling.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Resampling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_X u_Y u_I u_E u_F u_R

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [DecidableEq X] [DecidableEq Y] [AddCommMonoid E] [Module ℝ E]

abbrev Profile (I : Type u_I) (X : Type u_X) (Y : Type u_Y) := I → X × Y

def updateLeft (z : Profile I X Y) (i : I) (x : X) : Profile I X Y :=
  Function.update z i (x,(z i).2)
def updateRight (z : Profile I X Y) (i : I) (y : Y) : Profile I X Y :=
  Function.update z i ((z i).1,y)

def left (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E)
    (z : Profile I X Y) : E :=
  (μ.givenSecond x₀ (z i).2).avg (fun x => f (updateLeft z i x))
def right (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E)
    (z : Profile I X Y) : E :=
  (μ.givenFirst y₀ (z i).1).avg (fun y => f (updateRight z i y))

def IgnoresLeft (f : Profile I X Y → E) (i : I) : Prop :=
  ∀ z x, f (updateLeft z i x) = f z
def IgnoresRight (f : Profile I X Y → E) (i : I) : Prop :=
  ∀ z y, f (updateRight z i y) = f z

section Linear
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end Linear

section Folds

def lefts (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : Profile I X Y → E) :
    Profile I X Y → E := l.foldr (μ.left x₀) f

def rights (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : Profile I X Y → E) :
    Profile I X Y → E := l.foldr (μ.right y₀) f

variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end Folds

section FixedCoordinate
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end FixedCoordinate

section FoldLinear
variable {R : Type u_R} {F : Type u_F} [Fintype R] [AddCommMonoid F] [Module ℝ F]
omit [Fintype I] [DecidableEq Y] in
lemma lefts_sum (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : R → Profile I X Y → E)
    (z : Profile I X Y) :
    μ.lefts x₀ l (fun q => ∑ r, f r q) z = ∑ r, μ.lefts x₀ l (f r) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change (μ.givenSecond x₀ (z i).2).avg (fun x => μ.lefts x₀ l (fun q => ∑ r, f r q) (updateLeft z i x)) =
      ∑ r, (μ.givenSecond x₀ (z i).2).avg (fun x => μ.lefts x₀ l (f r) (updateLeft z i x))
    simp only [ih]
    exact avg_sum _ _
omit [Fintype I] [DecidableEq X] in
lemma rights_sum (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : R → Profile I X Y → E)
    (z : Profile I X Y) :
    μ.rights y₀ l (fun q => ∑ r, f r q) z = ∑ r, μ.rights y₀ l (f r) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change (μ.givenFirst y₀ (z i).1).avg (fun y => μ.rights y₀ l (fun q => ∑ r, f r q) (updateRight z i y)) =
      ∑ r, (μ.givenFirst y₀ (z i).1).avg (fun y => μ.rights y₀ l (f r) (updateRight z i y))
    simp only [ih]
    exact avg_sum _ _
end FoldLinear

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI


