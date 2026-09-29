-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/12ff29f5-c537-5327-beeb-94955274958a

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsQuasicoherent"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Hom IsQuasicoherent res obj"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section PModQC
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem eq_zero_of_forall_res_basicOpen_eq_zero {F : OModulePresheaf π} (hF : OModulePresheaf.IsQuasicoherent F)
    (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1)
    (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 := by
  choose n hn using fun j => (hF U (h j)).2 x (hx j)

  have hspan : Ideal.span (Set.range fun j => (h j) ^ (n j + 1)) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    exact (hcov.trans (iSup_mono fun j =>
        (V.basicOpen_pow (h j) (n j).succ_pos).ge)).trans
      (iSup_le fun j => le_iSup_of_le ⟨_, j, rfl⟩ le_rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : Γ(V, U.1)) ∈ Ideal.span _ from hspan ▸ Submodule.mem_top)
  calc x = (1 : Γ(V, U.1)) • x := (one_smul _ x).symm
    _ = (∑ j, c j * (h j) ^ (n j + 1)) • x := by rw [hc]
    _ = ∑ j, c j • ((h j) ^ (n j + 1) • x) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = 0 := Finset.sum_eq_zero fun j _ => by
        rw [pow_succ', mul_smul, hn j, smul_zero, smul_zero]

end PModQC

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1)) (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1) (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 :=
  AlgebraicGeometry.OModulePresheaf.G4T.eq_zero_of_forall_res_basicOpen_eq_zero hF U h hcov x hx

end S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero (solution)
