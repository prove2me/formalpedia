-- Prove2me | Definitions.Def_MazurTransfer_OriginalRelativeNormPreimagePointTorsorData20261020
-- name    : MazurTransfer_OriginalRelativeNormPreimagePointTorsorData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T00:59:17.865774+00:00
-- url     : https://prove2.me/theorems/dc8e0d6b-f601-46b5-8af7-67f62f3d85e6
-- title:
--   Original relative norm-preimage principal point action
-- statement:
--   Retain the original preimage point functor, kernel action, difference and principal-action equivalence, together with both original pullback maps and the intrinsic certificates constructing those data. All nine complete original types, six whole values, sixteen original context types, ten context values and six generated structural proof types are independently checked. The cocycle identity and naturality are separate theorem interfaces. Named downstream consumer: the actual integral nineteen norm-preimage torsor and its selected mu19 quotient.
-- source:
--   MazurTheorem RelativeNormPreimagePointTorsor by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL endomorphism preimage point functor has its
natural kernel action and principal-action equivalence over EVERY test
scheme. No point over every test scheme is assumed.
Named downstream consumer: the actual integral nineteen norm-preimage
fppf torsor and its previously selected normalized mu19 quotient.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020

noncomputable section
namespace MazurTransfer.RelativeNormPreimagePointTorsor
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLawFiniteFlatKernelHopf
universe u
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) (F : SchemeHomOver f f)
variable (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
  NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t)
variable (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
  NeronModelInfra.schemeHomOverComp (L.mul t x y) F =
    L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F))

abbrev preimagePoints {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a : SchemeHomOver t f) :=
  {y : SchemeHomOver t f // NeronModelInfra.schemeHomOverComp y F = a}

include hOne hMul in
theorem preserves_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.inv t x) F =
      L.inv t (NeronModelInfra.schemeHomOverComp x F) := by
  letI := L.pointGroup t
  let φ : SchemeHomOver t f →* SchemeHomOver t f :=
    { toFun := fun y => NeronModelInfra.schemeHomOverComp y F
      map_one' := hOne t
      map_mul' := hMul t }
  exact map_inv φ x

include hMul in
def act {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a : SchemeHomOver t f}
    (k : kernelPoints L F t) (y : preimagePoints F a) : preimagePoints F a :=
  ⟨L.mul t k.val y.val, by rw [hMul, k.property, y.property, L.one_mul]⟩

include hOne hMul in
def difference {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a : SchemeHomOver t f}
    (y z : preimagePoints F a) : kernelPoints L F t :=
  ⟨L.mul t y.val (L.inv t z.val), by
    rw [hMul, preserves_inv L F hOne hMul, y.property, z.property, L.mul_inv_cancel]⟩

include hOne hMul in
theorem act_difference {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a : SchemeHomOver t f}
    (y z : preimagePoints F a) : act L F hMul (difference L F hOne hMul y z) z = y := by
  letI := L.pointGroup t
  apply Subtype.ext
  change (y.val * z.val⁻¹) * z.val = y.val
  simp [mul_assoc]

include hOne hMul in
theorem difference_act {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a : SchemeHomOver t f}
    (k : kernelPoints L F t) (y : preimagePoints F a) :
    difference L F hOne hMul (act L F hMul k y) y = k := by
  letI := L.pointGroup t
  apply Subtype.ext
  change (k.val * y.val) * y.val⁻¹ = k.val
  simp [mul_assoc]

include hOne hMul in
def principalActionEquiv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a : SchemeHomOver t f) :
    kernelPoints L F t × preimagePoints F a ≃ preimagePoints F a × preimagePoints F a where
  toFun p := (act L F hMul p.1 p.2, p.2)
  invFun p := (difference L F hOne hMul p.1 p.2, p.2)
  left_inv p := Prod.ext (difference_act L F hOne hMul p.1 p.2) rfl
  right_inv p := Prod.ext (act_difference L F hOne hMul p.1 p.2) rfl



variable {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
variable {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')

/-- Precomposition retains the original endomorphism and point. -/
def precomposePreimage {a : SchemeHomOver t f} (y : preimagePoints F a) :
    preimagePoints F (GoodReductionJacobian.schemeHomOverComp ψ hψ a) :=
  ⟨GoodReductionJacobian.schemeHomOverComp ψ hψ y.val, by
    apply Subtype.ext
    change (ψ ≫ y.val.val) ≫ F.val = ψ ≫ a.val
    rw [Category.assoc]
    exact congrArg (fun b => ψ ≫ b.val) y.property⟩

def precomposeKernel (k : kernelPoints L F t) : kernelPoints L F t' :=
  ⟨GoodReductionJacobian.schemeHomOverComp ψ hψ k.val, by
    apply Subtype.ext
    change (ψ ≫ k.val.val) ≫ F.val = (L.one t').val
    rw [Category.assoc]
    have hk : k.val.val ≫ F.val = (L.one t).val := congrArg Subtype.val k.property
    rw [hk]
    exact congrArg Subtype.val (L.one_natural t t' ψ hψ)⟩





end MazurTransfer.RelativeNormPreimagePointTorsor
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.preimagePoints
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.preserves_inv
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.act
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.difference
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.act_difference
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.difference_act
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.principalActionEquiv
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.precomposePreimage
#print axioms MazurTransfer.RelativeNormPreimagePointTorsor.precomposeKernel


