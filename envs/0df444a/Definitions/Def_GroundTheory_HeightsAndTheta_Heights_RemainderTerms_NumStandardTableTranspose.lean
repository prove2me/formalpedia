-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableTranspose
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableTranspose
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:47:10.583145+00:00
-- url     : https://prove2.me/theorems/4024382b-3f7d-455d-8328-af93c258389f
-- title:
--   Num Standard Table Transpose
-- statement:
--   Definitions and structural lemmas for Num Standard Table Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableTranspose.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_VandermondeEqVandermondeOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset FlagEq
noncomputable section
namespace DegreeValueAlt
variable (f : ℕ)
def toReal {N M : ℕ} (h : N = M) : RootRing f N →+* MvPolynomial (Fin f × Fin M) ℝ :=
  (MvPolynomial.map (algebraMap ℚ ℝ)).comp (rename (Prod.map id (Fin.cast h))).toRingHom
abbrev top (j k : ℕ) (τ : Fin f) (i : Fin j) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := X (τ, Fin.castAdd k i)
abbrev bot (j k : ℕ) (τ : Fin f) (i : Fin k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := X (τ, Fin.natAdd j i)
def fibTB (j k : ℕ) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  ∏ τ : Fin f, vandermondeOf (top f j k τ) * vandermondeOf (bot f j k τ)
def rectTranspose (a r : ℕ) :
    youngCells (fun _ : Fin a => r) ≃o youngCells (fun _ : Fin r => a) where
  toFun p := ⟨(⟨p.1.2, (YoungDiagramCombinatorics.mem_youngCells _ p.1).1 p.2⟩, (p.1.1 : ℕ)),
    (YoungDiagramCombinatorics.mem_youngCells _ _).2 p.1.1.2⟩
  invFun q := ⟨(⟨q.1.2, (YoungDiagramCombinatorics.mem_youngCells _ q.1).1 q.2⟩, (q.1.1 : ℕ)),
    (YoungDiagramCombinatorics.mem_youngCells _ _).2 q.1.1.2⟩
  left_inv p := rfl
  right_inv q := rfl
  map_rel_iff' := by
    rintro ⟨⟨i, c⟩, hp⟩ ⟨⟨i', c'⟩, hq⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Prod.mk_le_mk, Fin.le_def]
    exact and_comm
end DegreeValueAlt
end
end GroundTheory.Heights₂.Heights.RestTerms


