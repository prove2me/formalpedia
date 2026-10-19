-- Prove2me | Definitions.Def_MazurTransfer_Order13FirstFiniteChartSections
-- name    : MazurTransfer_Order13FirstFiniteChartSections
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T05:58:49.339025+00:00
-- url     : https://prove2.me/theorems/addd3f7d-329e-40ee-809c-a915f8084752
-- title:
--   Structural sections and parameter of the actual first finite chart
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $U$ be the actual first finite chart of the order-thirteen curve, and let $B=R[T][p,q]$ be its actual finite coordinate algebra. The selected public affine presentation determines an isomorphism $E:\Gamma(U)\cong_R B$ and a section $f=E^{-1}(T)$. Its pullback to the ordinary chart is the literal parameter $t$. These are the structural section and parameter constructors needed to transport the rank-three polynomial basis to $U$.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Eleven closed structural declarations. The fresh affine presentation is selected from the already Proved public first-chart theorem; no equality with an older selected presentation is asserted. The new public affine-open R-algebra constructor supplies coefficient compatibility. The already Proved public restriction theorem supplies the actual ordinary-chart pullback. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers are the first-chart polynomial basis, finite free level sets, and unchanged actual FiniteMapData existence contract.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the selected actual first finite chart has its structural section R-algebra comparison and its literal parameter section. The actual Spec presentation comes from the already Proved public affine-complement theorem.
Named downstream consumers: the first-chart polynomial basis, finite free level sets and unchanged actual FiniteMapData existence contract. A fresh selected presentation is used; no equality with an older choice is asserted. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartFromPublicTheorem
import Definitions.Def_MazurTransfer_AffineOpenSectionsAlgEquiv
import Theorems.Thm_MazurTransfer_ActualAffineSectionRingRestrictionTransport_transportedSection_pullback
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open scoped MazurTransfer.Order13SingleSectionFiniteAlgebra
namespace MazurTransfer.Order13FirstFiniteChartFromPublicTheorem
variable (R : Type u) [CommRing R]

scoped instance candidateBaseAlgebra :
    Algebra R (Order13SingleSectionFiniteAlgebra.candidateAlgebra R) :=
  ((algebraMap (Polynomial R) (Order13SingleSectionFiniteAlgebra.candidateAlgebra R)).comp
    (Polynomial.C : R →+* Polynomial R)).toAlgebra

scoped instance candidateBaseTower :
    IsScalarTower R (Polynomial R) (Order13SingleSectionFiniteAlgebra.candidateAlgebra R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def parameterElement : Order13SingleSectionFiniteAlgebra.candidateAlgebra R :=
  algebraMap (Polynomial R) (Order13SingleSectionFiniteAlgebra.candidateAlgebra R) X

theorem parameterElement_value :
    (parameterElement R : CoordinateRing R) = Order13SingleSectionFiniteMapIdentities.t R := by
  change algebraMap (Polynomial R) (CoordinateRing R) X = _
  rw [Order13SingleSectionFiniteAlgebra.parameter_algebraMap, aeval_X]

theorem ordinary_le_preimage_chartOpen : ⊤ ≤ (ordinaryChartMap R) ⁻¹ᵁ chartOpen R := by
  intro x _
  change ordinaryChartMap R x ∈ Set.range (ordinaryChartMap R) ∨
    ordinaryChartMap R x ∈ Set.range (patchChartMap R)
  exact Or.inl ⟨x, rfl⟩

variable [IsDomain R] [IsNoetherianRing R]

theorem specIso_over_base (h104 : IsUnit (104 : R)) :
    (specIso R h104).hom ≫ (chartOpen R).ι ≫ curveToBase R =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Order13SingleSectionFiniteAlgebra.candidateAlgebra R))) := by
  calc
    _ = (specIso R h104).hom ≫
        (((specIso R h104).inv ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (Polynomial R) (Order13SingleSectionFiniteAlgebra.candidateAlgebra R)))) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
      rw [specIso_parameter_over]
    _ = Spec.map (CommRingCat.ofHom
          (algebraMap (Polynomial R) (Order13SingleSectionFiniteAlgebra.candidateAlgebra R))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [← Spec.map_comp]; rfl

def sectionsRingIso (h104 : IsUnit (104 : R)) :
    Γ(curveScheme R, chartOpen R) ≅
      CommRingCat.of (Order13SingleSectionFiniteAlgebra.candidateAlgebra R) :=
  ActualAffineSectionRingBasicOpenTransport.sectionsRingIso (chartOpen R) (specIso R h104)

def sectionsAlgEquiv (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
    Γ(curveScheme R, chartOpen R) ≃ₐ[R]
      Order13SingleSectionFiniteAlgebra.candidateAlgebra R :=
  ActualAffineSectionRingBasicOpenTransport.sectionsAlgEquiv_of_over R (curveToBase R)
    (chartOpen R) (Order13SingleSectionFiniteAlgebra.candidateAlgebra R)
    (specIso R h104) (specIso_over_base R h104)

def parameterSection (h104 : IsUnit (104 : R)) : Γ(curveScheme R, chartOpen R) :=
  ActualAffineSectionRingBasicOpenTransport.transportedSection (chartOpen R)
    (specIso R h104) (parameterElement R)

theorem sectionsAlgEquiv_parameter (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
    sectionsAlgEquiv R h104 (parameterSection R h104) = parameterElement R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
  exact (sectionsRingIso R h104).commRingCatIsoToRingEquiv.apply_symm_apply _

theorem parameterSection_ordinary_pullback (h104 : IsUnit (104 : R)) :
    (Scheme.ΓSpecIso (.of (CoordinateRing R))).hom
      ((ordinaryChartMap R).appLE (chartOpen R) ⊤
        (ordinary_le_preimage_chartOpen R) (parameterSection R h104)) =
      Order13SingleSectionFiniteMapIdentities.t R := by
  have hp := ActualAffineSectionRingRestrictionTransport.transportedSection_pullback
    (chartOpen R) (specIso R h104)
    (Order13SingleSectionFiniteAlgebra.candidateAlgebra R).val.toRingHom
    (parameterElement R)
    (show ⊤ ≤ (Spec.map (CommRingCat.ofHom
      (Order13SingleSectionFiniteAlgebra.candidateAlgebra R).val.toRingHom) ≫
      (specIso R h104).hom ≫ (chartOpen R).ι) ⁻¹ᵁ chartOpen R by
        rw [specIso_ordinary]; exact ordinary_le_preimage_chartOpen R)
  have hp' : (Scheme.ΓSpecIso (.of (CoordinateRing R))).hom
      ((ordinaryChartMap R).appLE (chartOpen R) ⊤
        (ordinary_le_preimage_chartOpen R) (parameterSection R h104)) =
      (Order13SingleSectionFiniteAlgebra.candidateAlgebra R).val.toRingHom
        (parameterElement R) := by
    simpa only [specIso_ordinary, parameterSection] using hp
  exact hp'.trans (parameterElement_value R)

end MazurTransfer.Order13FirstFiniteChartFromPublicTheorem
#print axioms MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.sectionsAlgEquiv
#print axioms MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.parameterSection_ordinary_pullback


