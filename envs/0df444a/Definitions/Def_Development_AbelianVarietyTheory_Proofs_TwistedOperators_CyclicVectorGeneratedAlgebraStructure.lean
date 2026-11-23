-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:42.752185+00:00
-- url     : https://prove2.me/theorems/97fe78ab-8598-447d-bc17-0866b5bc7110
-- title:
--   Cyclic Vector Generated Algebra Structure
-- statement:
--   Definitions and structural lemmas for Cyclic Vector Generated Algebra Structure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
namespace GlobalTheory.RegSS.CycAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
def lowPoly (c : n → A) : A[X] :=
  ∑ j, c j • (X : A[X]) ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)
theorem coe_aeval_gen (M : Matrix n n A) (p : A[X]) :
    ((aeval (gen M) p : genAlg M) : Matrix n n A) = aeval M p :=
  (Polynomial.aeval_algHom_apply (genAlg M).val (gen M) p).symm
def actOn (M : Matrix n n A) (v : n → A) : genAlg M →ₗ[A] (n → A) where
  toFun l := (l : Matrix n n A) *ᵥ v
  map_add' a b := Matrix.add_mulVec _ _ _
  map_smul' c a := Matrix.smul_mulVec c (a : Matrix n n A) v
theorem aeval_gen_charpoly (M : Matrix n n A) : aeval (gen M) M.charpoly = 0 :=
  Subtype.ext (by rw [coe_aeval_gen, Matrix.aeval_self_charpoly]; rfl)
def toGen (M : Matrix n n A) : AdjoinRoot M.charpoly →ₐ[A] genAlg M :=
  AdjoinRoot.liftAlgHom M.charpoly (Algebra.ofId A _) (gen M) (aeval_gen_charpoly M)
end GlobalTheory.RegSS.CycAlg


