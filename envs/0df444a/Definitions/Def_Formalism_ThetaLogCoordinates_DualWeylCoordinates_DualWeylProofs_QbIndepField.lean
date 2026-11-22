-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:08.502092+00:00
-- url     : https://prove2.me/theorems/89be4129-e55d-4940-b27f-6c7b9a4abb7a
-- title:
--   Qb Indep Field
-- statement:
--   Definitions and structural lemmas for Qb Indep Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
def qb_ev (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) : M.ι → GLCoord F n :=
  Matrix.mulVec ((prMu M nu).map (Int.castRingHom (GLCoord F n)))
    (Matrix.mulVec (M.A.map (mapCoord F)) (fun i => algebraMap F (GLCoord F n) (x i)))
lemma qb_ev_apply (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) (i : M.ι) :
    qb_ev M F nu x i =
      ∑ k, (prMu M nu i k : GLCoord F n) * ∑ l, mapCoord F (M.A k l) * algebraMap F (GLCoord F n) (x l) := rfl
def qb_evL (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) : (M.ι → F) →ₗ[F] (M.ι → GLCoord F n) where
  toFun := qb_ev M F nu
  map_add' x y := by
    funext i
    simp only [qb_ev_apply, Pi.add_apply, map_add, mul_add, sum_add_distrib]
  map_smul' a x := by
    funext i
    simp only [qb_ev_apply, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, mul_sum]
    rw [Algebra.smul_def, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    ring
variable [NeZero n]
instance qb_fintypeStd (mu : Fin n → ℤ) : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
abbrev qb_Idx {M : GLMod n} (CF : ColFam M) := Σ j : CF.J, {I : TIdx (CF.mu j) // StdT I}
def qb_vecF {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] (x : qb_Idx CF) : M.ι → F :=
  fun i => (CF.vec x.1 x.2.1 i : F)
end Formalism.InvariantFactorPaths.ColumnFamilies


