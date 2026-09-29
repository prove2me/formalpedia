-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fc70d010-44d2-5ad7-8209-e431b857300b

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Algebra.Category.Grp.Preadditive
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Fppf smallFppfTopology fppfCohomology fppfCohomologyMap fppfCohomologyMap_id"
namespace FppfTransfer
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"

section Transfer

p2m_open "CategoryTheory CategoryTheory.Abelian Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero.AlgebraicGeometry.Scheme"

universe v

variable (S : Scheme.{v}) (F : Sheaf (smallFppfTopology S) Ab.{v + 1})

theorem fppfCohomologyMap_add (G : Sheaf (smallFppfTopology S) Ab.{v + 1}) (φ ψ : F ⟶ G) (n : ℕ)
    (x : fppfCohomology S F n) :
    fppfCohomologyMap S (φ + ψ) n x = fppfCohomologyMap S φ n x + fppfCohomologyMap S ψ n x := by
  show Ext.comp x (Ext.mk₀ (φ + ψ)) (add_zero n) =
    Ext.comp x (Ext.mk₀ φ) (add_zero n) + Ext.comp x (Ext.mk₀ ψ) (add_zero n)
  rw [Ext.mk₀_add, Ext.comp_add]

theorem fppfCohomologyMap_zero (G : Sheaf (smallFppfTopology S) Ab.{v + 1}) (n : ℕ)
    (x : fppfCohomology S F n) :
    fppfCohomologyMap S (0 : F ⟶ G) n x = 0 := by
  show Ext.comp x (Ext.mk₀ (0 : F ⟶ G)) (add_zero n) = 0
  rw [Ext.mk₀_zero, Ext.comp_zero]

theorem fppfCohomologyMap_nsmul (G : Sheaf (smallFppfTopology S) Ab.{v + 1}) (φ : F ⟶ G) (k n : ℕ)
    (x : fppfCohomology S F n) :
    fppfCohomologyMap S (k • φ) n x = k • fppfCohomologyMap S φ n x := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, fppfCohomologyMap_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fppfCohomologyMap_add, ih]

theorem nsmul_id_eq_zero (k : ℕ) (hF : ∀ (U : S.Fppf) (s : F.1.obj (op U)), k • s = 0) :
    (k • 𝟙 F : F ⟶ F) = 0 := by
  apply Sheaf.hom_ext
  ext U s
  have h__af := hF U.unop s
  simp at h__af
  exact h__af

theorem nsmul_fppfCohomology_eq_zero (k : ℕ)
    (hF : ∀ (U : S.Fppf) (s : F.1.obj (op U)), k • s = 0) (n : ℕ) (x : fppfCohomology S F n) :
    k • x = 0 := by
  have h := fppfCohomologyMap_nsmul S F F (𝟙 F) k n x
  rw [fppfCohomologyMap_id, nsmul_id_eq_zero S F k hF, fppfCohomologyMap_zero] at h
  exact h.symm

end Transfer

end AlgebraicGeometry.Scheme.FppfTransfer

end

universe u in
open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme _root_.P2MW.S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero.AlgebraicGeometry.Scheme CategoryTheory in
theorem solution
    (S : Scheme.{u}) (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) (k : ℕ)
    (hF : ∀ (U : S.Fppf) (s : F.1.obj (Opposite.op U)), k • s = 0)
    (n : ℕ) (x : fppfCohomology S F n) :
    k • x = 0 :=
  AlgebraicGeometry.Scheme.FppfTransfer.nsmul_fppfCohomology_eq_zero S F k hF n x

end S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero (solution)
