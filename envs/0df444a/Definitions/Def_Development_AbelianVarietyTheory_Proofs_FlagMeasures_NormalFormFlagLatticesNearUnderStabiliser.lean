-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:56.93798+00:00
-- url     : https://prove2.me/theorems/8bce719d-4f82-4284-93fb-edf597cb08e7
-- title:
--   Normal Form Flag Lattices Near Under Stabiliser
-- statement:
--   Definitions and structural lemmas for Normal Form Flag Lattices Near Under Stabiliser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegCnt.PosJ
section Weighted
open LaurentPolynomial
variable {K : Type} [Field K]
def gradedSub (I : ℤ → AddSubgroup K) (h1 : (1 : K) ∈ I 0)
    (hmul : ∀ m n x y, x ∈ I m → y ∈ I n → x * y ∈ I (m + n)) : Subring K[T;T⁻¹] where
  carrier := {f | ∀ n, f.coeff n ∈ I n}
  mul_mem' := by
    intro f g hf hg n
    rw [AddMonoidAlgebra.coeff_mul]
    refine AddSubgroup.sum_mem _ fun a _ => AddSubgroup.sum_mem _ fun b _ => ?_
    dsimp only
    split_ifs with h
    · exact h ▸ hmul _ _ _ _ (hf a) (hg b)
    · exact zero_mem _
  one_mem' := by
    intro n
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · exact h ▸ h1
    · exact zero_mem _
  add_mem' := by
    intro f g hf hg n
    simpa using add_mem (hf n) (hg n)
  zero_mem' := by
    intro n
    simp
  neg_mem' := by
    intro f hf n
    simpa using hf n
def sc {α β : Type} (M : Matrix α β K) (p : α → ℤ) (q : β → ℤ) : Matrix α β K[T;T⁻¹] :=
  Matrix.of fun a b => C (M a b) * T (p a + q b)
end Weighted
section Ipow
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K]
end Ipow
section Lat
open GlobalTheory.HL
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def vec {j : ℕ} (e : Fin j → V) (u : Matrix (Fin j) (Fin j) K) (a : Fin j) : V := ∑ b, u b a • e b
variable {H : HermSpace K V} {r : ℕ}
def ej (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (a : Fin j) : V := F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)
end Lat
section Isom
open GlobalTheory.HL Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) {j : ℕ}
variable {H} {r : ℕ}
end Isom
section Normal
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
variable (N : NF H r)
end Normal
section Final
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
end Final
end GlobalTheory.DegCnt.PosJ


