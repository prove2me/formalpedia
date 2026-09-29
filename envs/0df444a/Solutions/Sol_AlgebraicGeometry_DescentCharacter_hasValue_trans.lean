-- Prove2me | solution 1 for AlgebraicGeometry.DescentCharacter.hasValue_trans
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0d9e6d35-c36b-5bd0-98f2-a4d9de053fff

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_trans

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

namespace KcDescCharTrans

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

theorem translateIso_trans {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P) :
    translateIso h (β ≪≫ β') = translateIso h β ≪≫ translateIso h β' := by
  ext : 1
  simp [translateIso, Functor.mapIso_trans]

theorem translateIso_eq {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    translateIso h β = β ≪≫ discrepancy h β := by
  ext : 1
  simp [discrepancy]

theorem discrepancy_trans_hom {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P) :
    (discrepancy h (β ≪≫ β')).hom = β'.inv ≫ (discrepancy h β).hom ≫ β'.hom ≫ (discrepancy h β').hom := by
  have e1 : (discrepancy h (β ≪≫ β')).hom = β'.inv ≫ β.inv ≫ (translateIso h (β ≪≫ β')).hom := by
    simp [discrepancy]
  rw [e1, translateIso_trans, Iso.trans_hom, translateIso_eq h β, translateIso_eq h β']
  simp

theorem isBaseScalar_comp (f : X ⟶ Spec (CommRingCat.of R)) {M : X.Modules} {σ σ' : M ⟶ M} {c c' : R}
    (hσ : IsBaseScalar f σ c) (hσ' : IsBaseScalar f σ' c') : IsBaseScalar f (σ ≫ σ') (c * c') := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hσ U s, Scheme.Modules.Hom.app_smul, hσ' U,
    smul_smul, baseSection_mul, mul_comm]

theorem isBaseScalar_conj (f : X ⟶ Spec (CommRingCat.of R)) {M M' : X.Modules} (e : M ≅ M') {σ : M ⟶ M} {c : R}
    (hσ : IsBaseScalar f σ c) : IsBaseScalar f (e.inv ≫ σ ≫ e.hom) c := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, hσ U, Scheme.Modules.Hom.app_smul, ← CategoryTheory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

theorem isBaseScalar_id (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) : IsBaseScalar f (𝟙 M) 1 := by
  intro U s
  rw [Scheme.Modules.Hom.id_app, CategoryTheory.id_apply, baseSection_one, one_smul]

theorem hasValue_trans (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P)
    (c c' : R) (hβ : HasValue f h β c) (hβ' : HasValue f h β' c') :
    HasValue f h (β ≪≫ β') (c * c') := by
  unfold HasValue
  rw [discrepancy_trans_hom]
  have h1 : IsBaseScalar f (β'.inv ≫ (discrepancy h β).hom ≫ β'.hom) c := isBaseScalar_conj f β' hβ
  have h2 := isBaseScalar_comp f h1 hβ'
  simpa [Category.assoc] using h2

end KcDescCharTrans

theorem solution
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P)
    (c c' : R) (hβ : HasValue f h β c) (hβ' : HasValue f h β' c') :
    HasValue f h (β ≪≫ β') (c * c') :=
  KcDescCharTrans.hasValue_trans f h β β' c c' hβ hβ'

end S_AlgebraicGeometry_DescentCharacter_hasValue_trans
end P2MW
export P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_trans (solution)
