-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:31.14228+00:00
-- url     : https://prove2.me/theorems/1c66dede-065a-4fc0-9b00-61cff56c0e75
-- title:
--   Mod Princ Norm
-- statement:
--   Definitions and structural lemmas for Mod Princ Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModPrincNorm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KQ_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
namespace ReciprocityTheory.ChartRestriction.L1
theorem sqD_indep {d : ℕ} (hd : 0 < d) (u v : ℚ) (h : (u : ℂ) + v * sqD d = 0) : u = 0 ∧ v = 0 := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sqD] at hre him
  exact ⟨hre, him.resolve_right (by
    intro h0
    apply hs
    simpa using h0)⟩
theorem sqK_li {d : ℕ} (hd : 0 < d) : LinearIndependent ℚ ![(1 : KQ d), sqK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  apply sqD_indep hd
  have := congrArg (fun z : KQ d => (z : ℂ)) h
  simpa [sqK, Algebra.smul_def] using this
theorem sqK_decomp {d : ℕ} (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    z = p • (1 : KQ d) + q • sqK d := by
  apply Subtype.ext
  simp [sqK, Algebra.smul_def, h]
theorem sqK_span {d : ℕ} : ⊤ ≤ Submodule.span ℚ (Set.range ![(1 : KQ d), sqK d]) := by
  intro z _
  obtain ⟨u, v, h⟩ := (KQ_mem_iff d z).1 z.2
  rw [sqK_decomp z u v h]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
def bKQ {d : ℕ} (hd : 0 < d) : Module.Basis (Fin 2) ℚ (KQ d) := Module.Basis.mk (sqK_li hd) sqK_span
end ReciprocityTheory.ChartRestriction.L1


