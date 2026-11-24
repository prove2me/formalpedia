-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:33.270702+00:00
-- url     : https://prove2.me/theorems/72c007f0-45a1-4f3e-b21c-8a1a175ef573
-- title:
--   PExtension
-- statement:
--   Definitions and structural lemmas for PExtension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
def ofGens {ι : Type} [Fintype ι] (deg : ι → ℤ) (gen : ι → E) : FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S {z | ∃ (k : ι) (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧
    (e : ℤ) + deg k = c ∧ z = aeval x f • gen k}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span S
      {z | ∃ (k : ι) (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg k = c + d ∧
        z = aeval x f • gen k}) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨k, g, e, hg, he, rfl⟩
      exact Submodule.subset_span ⟨k, f * g, d + e, hf.mul hg, by push_cast; omega, by
        rw [map_mul, mul_smul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := ⟨Fintype.card ι, fun j => deg ((Fintype.equivFin ι).symm j),
    fun j => gen ((Fintype.equivFin ι).symm j),
    fun j => Submodule.subset_span ⟨(Fintype.equivFin ι).symm j, 1, 0, isHomogeneous_one _ _, by simp,
      by simp⟩,
    fun c => Submodule.span_mono fun z ⟨k, f, e, hf, he, hz⟩ =>
      ⟨Fintype.equivFin ι k, f, e, hf, by simpa using he, by simpa using hz⟩⟩
end ExtensionProof
end
end GroundTheory.Heights₂.Heights.Kleiman


