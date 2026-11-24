-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:14:15.205308+00:00
-- url     : https://prove2.me/theorems/7fde268c-38b5-4545-a895-151c2865a726
-- title:
--   Coordinate Split Assoc Measure Preserving
-- statement:
--   Definitions and structural lemmas for Coordinate Split Assoc Measure Preserving, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSplitAssocMeasurePreserving.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
section B
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
def levelProduct (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) (i : ℕ) :
    SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')) :=
  if h : i < r then levelProduct L w (i + 1) * bTl L ⟨i, h⟩ w else 1
termination_by r - i
def levelIntegrand (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (i : Fin (r + 1)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ)
    (q : Cf r i × Mt k r) : ℂ :=
  ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
    topDens L st w (act (levelProduct L w i.val) x) (act (levelProduct L w i.val) y) (glue i c q.1) (Matrix.of q.2)
def coordinateSplitAssoc (l : Fin r) {β : Type} [MeasurableSpace β] : Cf r l.castSucc × β ≃ᵐ ℂ × (Cf r l.succ × β) :=
  ((coordinateSplit l).prodCongr (MeasurableEquiv.refl β)).trans MeasurableEquiv.prodAssoc
end B
section Main
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)} [SFinite μ]
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}
def LevelIntegralFormula (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (w : List (Letter ℂ S)) (i : Fin (P.r + 1)) :
    Prop :=
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → InK (K i) y → ∀ c ∈ OmX P.r,
    Integrable (levelIntegrand L st w i x y c) (volume.prod μ) ∧
      RRform L st μ i w x y c = ∫ q, levelIntegrand L st w i x y c q ∂(volume.prod μ)
end Main
end Formalism.FourierDecayAlt.P5


