-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
-- name    : CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:04:39.845699+00:00
-- url     : https://prove2.me/theorems/17b33f27-f990-5d2e-a8ff-18ece7272b67
-- title:
--   Exists Den Fin
-- statement:
--   Definitions and structural lemmas for Exists Den Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/ExistsDenFin.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
namespace CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
variable (s : SplitPlace L)
def Sl (L : Type) [Field L] [NumberField L] [IsCMField L] {l : ℕ} (hl : l.Prime) : Subring (AL L) where
  carrier := {z | ∃ m : ℕ, ¬ l ∣ m ∧ (m : AL L) * z ∈ ALint L}
  mul_mem' := by
    rintro x y ⟨m, hm, h⟩ ⟨m', hm', h'⟩
    refine ⟨m * m', fun e => (hl.dvd_mul.1 e).elim hm hm', ?_⟩
    rw [Nat.cast_mul, mul_mul_mul_comm]
    exact Subring.mul_mem _ h h'
  add_mem' := by
    rintro x y ⟨m, hm, h⟩ ⟨m', hm', h'⟩
    refine ⟨m * m', fun e => (hl.dvd_mul.1 e).elim hm hm', ?_⟩
    rw [show ((m * m' : ℕ) : AL L) * (x + y) = m' * (m * x) + m * (m' * y) by push_cast; ring]
    exact Subring.add_mem _ (Subring.mul_mem _ (natCast_mem _ _) h) (Subring.mul_mem _ (natCast_mem _ _) h')
  one_mem' := ⟨1, hl.not_dvd_one, by simp⟩
  zero_mem' := ⟨1, hl.not_dvd_one, by simp⟩
  neg_mem' := by
    rintro x ⟨m, hm, h⟩
    exact ⟨m, hm, by rw [mul_neg]; exact Subring.neg_mem _ h⟩
end CompanionTheory.Split


