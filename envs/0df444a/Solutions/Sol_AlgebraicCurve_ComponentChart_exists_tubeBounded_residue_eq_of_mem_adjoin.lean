-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.exists_tubeBounded_residue_eq_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/cf94cb3e-d484-547e-a622-00323cb555d1

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_exists_tubeBounded_residue_eq_of_mem_adjoin

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (hrat : ∀ P ∈ C.dom, P.IsRational)
    {ι : Type*} (g : ι → F) (hg : ∀ i, g i ∈ C.integers) (hbd : ∀ i, C.tubeBounded (g i))
    (y : Fbar) (hy : y ∈ Algebra.adjoin (ResidueField A) (Set.range fun i => C.residue ⟨g i, hg i⟩)) :
    ∃ (f : F) (hf : f ∈ C.integers), C.tubeBounded f ∧ C.residue ⟨f, hf⟩ = y := by
  classical

  have tb_of_regular : ∀ (f : F) (hf : f ∈ C.integers), (∀ P ∈ C.dom, f ∈ P.toValuationSubring) →
      C.tubeBounded f := by
    intro f hf hreg P hP
    refine ⟨hreg P hP, ?_⟩
    obtain ⟨-, h, -⟩ := C.pointwise P hP (hrat P hP) f hf (fun w hw _ => hreg w hw)
    exact h

  let S : Subalgebra (ResidueField A) Fbar :=
    { carrier := {y | ∃ (f : F) (hf : f ∈ C.integers), C.tubeBounded f ∧ C.residue ⟨f, hf⟩ = y}
      mul_mem' := by
        rintro a b ⟨f₁, hf₁, hb₁, rfl⟩ ⟨f₂, hf₂, hb₂, rfl⟩
        refine ⟨f₁ * f₂, mul_mem hf₁ hf₂, ?_, ?_⟩
        · exact tb_of_regular _ (mul_mem hf₁ hf₂) fun P hP => mul_mem (hb₁ P hP).1 (hb₂ P hP).1
        · rw [← map_mul]; rfl
      add_mem' := by
        rintro a b ⟨f₁, hf₁, hb₁, rfl⟩ ⟨f₂, hf₂, hb₂, rfl⟩
        refine ⟨f₁ + f₂, add_mem hf₁ hf₂, ?_, ?_⟩
        · exact tb_of_regular _ (add_mem hf₁ hf₂) fun P hP => add_mem (hb₁ P hP).1 (hb₂ P hP).1
        · rw [← map_add]; rfl
      algebraMap_mem' := by
        intro r
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
        refine ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2, ?_, ?_⟩
        · exact tb_of_regular _ ((C.algebraMap_mem_iff a).mpr a.2) fun P _ => P.algebraMap_mem' (a : L)
        · exact C.residue_algebraMap a }
  have hle : Algebra.adjoin (ResidueField A) (Set.range fun i => C.residue ⟨g i, hg i⟩) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro y ⟨i, rfl⟩
    exact ⟨g i, hg i, hbd i, rfl⟩
  obtain ⟨f, hf, hb, he⟩ := hle hy
  exact ⟨f, hf, hb, he⟩

end S_AlgebraicCurve_ComponentChart_exists_tubeBounded_residue_eq_of_mem_adjoin
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_exists_tubeBounded_residue_eq_of_mem_adjoin (solution)
