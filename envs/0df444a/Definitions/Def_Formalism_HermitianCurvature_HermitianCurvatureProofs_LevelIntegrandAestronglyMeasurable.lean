-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:51:10.667876+00:00
-- url     : https://prove2.me/theorems/a30bb358-e8f4-426e-98da-29829e6543fa
-- title:
--   Level Integrand Aestrongly Measurable
-- statement:
--   Definitions and structural lemmas for Level Integrand Aestrongly Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
section Split
variable {r : ℕ}
def coordinateRestEquiv (l : Fin r) :
    {j : {j : Fin r // l.castSucc.val ≤ j.val} // ¬ (j.1 = l)} ≃ {j : Fin r // l.succ.val ≤ j.val} where
  toFun j := ⟨j.1.1, by
    have h1 := j.1.2; have h2 := j.2
    simp only [Fin.coe_castSucc, Fin.val_succ] at h1 ⊢
    rcases Nat.lt_or_ge l.val j.1.1.val with h | h
    · omega
    · exact absurd (Fin.ext (by omega)) h2⟩
  invFun j := ⟨⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩, by
    intro h; have := j.2; rw [h] at this; simp at this⟩
  left_inv j := rfl
  right_inv j := rfl
instance uniqueCoordinateAtLevel (l : Fin r) : Unique {j : {j : Fin r // l.castSucc.val ≤ j.val} // j.1 = l} where
  default := ⟨⟨l, by simp⟩, rfl⟩
  uniq j := Subtype.ext (Subtype.ext j.2)
def coordinateSplit (l : Fin r) : Cf r l.castSucc ≃ᵐ ℂ × Cf r l.succ :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {j : Fin r // l.castSucc.val ≤ j.val} => ℂ)
      (fun j => j.1 = l)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique _)
      (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (coordinateRestEquiv l)))
def coordinateExtension (i : Fin (r + 1)) (c : Fin r → ℂ) (a : Cf r i) : Cf r 0 := fun j => glue i c a j.1
end Split
section Top
variable {r : ℕ}
instance isEmptyCoordinatesFromLastLevel : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun j => by have h1 := j.2; have h2 := j.1.isLt; simp only [Fin.val_last] at h1; omega⟩
def lastLevelPoint (r : ℕ) : Cf r (Fin.last r) := isEmptyElim
end Top
section Dens
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
  (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
  (w : List (Letter ℂ S))
end Dens
section Meas
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}
end Meas
end Formalism.FourierDecayAlt.P5


