-- Prove2me | Definitions.Def_HopfAlgebra_HopfIdealQuotient
-- name    : HopfAlgebra_HopfIdealQuotient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/29c5d5fe-f677-530b-a851-87d9abc4fb3f
-- title:
--   Hopf ideals and quotient Hopf algebras
-- statement:
--   Let $R$ be a commutative ring and $H$ a commutative Hopf $R$-algebra, with comultiplication $\Delta$, counit $\varepsilon$ and antipode $S$, and let $\pi\colon H\to H/I$ denote the quotient map attached to an ideal $I\subseteq H$. The class [`Ideal.IsHopfIdeal' R I`](../def/HopfAlgebra_HopfIdealQuotient.html#L79) is the predicate with three fields: $(\pi\otimes\pi)(\Delta x)=0$ in $(H/I)\otimes_R(H/I)$ for all $x\in I$, $\varepsilon(x)=0$ for all $x\in I$, and $S(x)\in I$ for all $x\in I$. The first field is the kernel form of the usual condition $\Delta(I)\subseteq I\otimes_R H+H\otimes_R I$, the image of the latter being the kernel of $\pi\otimes\pi$. The zero ideal is registered as a Hopf ideal. For a Hopf ideal $I$, the maps [`HopfAlgebra.HopfIdealQuotient.comul`](../def/HopfAlgebra_HopfIdealQuotient.html#L100), `counit` and `antipode` are the $R$-algebra maps $H/I\to (H/I)\otimes_R(H/I)$, $H/I\to R$, $H/I\to H/I$ obtained from $(\pi\otimes\pi)\circ\Delta$, $\varepsilon$ and $\pi\circ S$ by factoring through $I$; coassociativity, the two counit identities and the two antipode identities are proved for them, yielding `Bialgebra R (H ⧸ I)` and `HopfAlgebra R (H ⧸ I)`, so that $\Delta_{H/I}(\pi x)=(\pi\otimes\pi)(\Delta x)$, $\varepsilon_{H/I}(\pi x)=\varepsilon(x)$ and $S_{H/I}(\pi x)=\pi(Sx)$. Cocommutativity of $H$ passes to $H/I$. On the map side: `quotientBialgHom` is $\pi$ as a bialgebra homomorphism, `quotientFactorBialgHom` the bialgebra map $H/I\to H/J$ for $I\le J$ (both surjective, and compatible under composition); `quotientLiftPoint` and `quotientPointsEquiv` give the bijection between $R$-algebra maps $H/I\to A$ and $R$-algebra maps $H\to A$ vanishing on $I$, for $A$ a commutative $R$-algebra. Finite type and, for $I=\bot$ (where $H/\bot\cong H$ as $R$-algebras), flatness are inherited. A preliminary section treats the antipode as an algebra endomorphism of a commutative Hopf algebra and shows that for $\varphi\colon H\to A$ the elements $\varphi$ and $\varphi\circ S$ are mutually inverse for the convolution product, so every such $\varphi$ is a unit in the convolution monoid; `convCompMonoidHom` records that precomposition with a bialgebra map $H\to G$ is a monoid homomorphism for convolution.
--
--   **Relation to Mathlib.** Mathlib supplies `Bialgebra`, `HopfAlgebra`, `BialgHom` and the convolution monoid `WithConv` on algebra homomorphisms; the Hopf-ideal predicate [`Ideal.IsHopfIdeal'`](../def/HopfAlgebra_HopfIdealQuotient.html#L79) and the Hopf-algebra structure on the quotient by a Hopf ideal are added here.
--
--   **Where it is used.** Quotients of commutative Hopf algebras by Hopf ideals correspond to closed subgroup schemes of affine group schemes, and the point-lifting bijection describes the functor of points of such a quotient; this interface underlies the project's treatment of affine group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HopfAlgebra_HopfIdealQuotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

namespace HopfAlgebra

section AntipodeAlgHom

variable (R : Type*) [CommSemiring R] (H : Type*) [CommSemiring H] [HopfAlgebra R H]

theorem antipodeAlgHom_toLinearMap : (antipodeAlgHom R H).toLinearMap = antipode R := rfl

variable {R H}
variable {A : Type*} [CommSemiring A] [Algebra R A]

theorem lift_comp_antipodeAlgHom_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift φ (φ.comp (antipodeAlgHom R H)) (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).lTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem lift_antipodeAlgHom_comp_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (φ.comp (antipodeAlgHom R H)) φ (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).rTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem convMul_comp_antipodeAlgHom (φ : H →ₐ[R] A) :
    toConv φ * toConv (φ.comp (antipodeAlgHom R H)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv φ * toConv (φ.comp (antipodeAlgHom R H))) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_comp_antipodeAlgHom_apply, mul_antipode_lTensor_comul_apply, AlgHom.commutes]

theorem comp_antipodeAlgHom_convMul (φ : H →ₐ[R] A) :
    toConv (φ.comp (antipodeAlgHom R H)) * toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv (φ.comp (antipodeAlgHom R H)) * toConv φ) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_antipodeAlgHom_comp_apply, mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem isUnit_toConv_algHom (φ : H →ₐ[R] A) : IsUnit (toConv φ) :=
  isUnit_iff_exists.2 ⟨_, convMul_comp_antipodeAlgHom φ, comp_antipodeAlgHom_convMul φ⟩

end AntipodeAlgHom

section ConvComp

variable {R : Type*} [CommSemiring R] {H G : Type*} [CommSemiring H] [CommSemiring G]
  [Bialgebra R H] [Bialgebra R G]
variable (A : Type*) [CommSemiring A] [Algebra R A]

def convCompMonoidHom (π : H →ₐc[R] G) : WithConv (G →ₐ[R] A) →* WithConv (H →ₐ[R] A) where
  toFun f := toConv (f.ofConv.comp (π : H →ₐ[R] G))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    rw [AlgHom.convMul_comp_bialgHom_distrib]

@[simp] theorem convCompMonoidHom_apply (π : H →ₐc[R] G) (f : WithConv (G →ₐ[R] A)) :
    convCompMonoidHom A π f = toConv (f.ofConv.comp (π : H →ₐ[R] G)) := rfl

end ConvComp

end HopfAlgebra

section IsHopfIdeal'

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

class Ideal.IsHopfIdeal' (I : Ideal H) : Prop where
  map_mkₐ_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) x) = 0
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

instance Ideal.isHopfIdeal_bot : (⊥ : Ideal H).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  counit_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  antipode_mem x hx := by rw [(Ideal.mem_bot).1 hx]; simp

end IsHopfIdeal'

namespace HopfAlgebra

namespace HopfIdealQuotient

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]
variable (I : Ideal H) [hI : I.IsHopfIdeal' R]

def comul : H ⧸ I →ₐ[R] (H ⧸ I) ⊗[R] (H ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (comulAlgHom R H))
    (fun x hx => hI.map_mkₐ_comul_eq_zero x hx)

theorem comul_comp_mkₐ :
    (comul R I).comp (Ideal.Quotient.mkₐ R I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
        (comulAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem comul_mk (x : H) :
    comul R I (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

def counit : H ⧸ I →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (counitAlgHom R H) (fun x hx => hI.counit_eq_zero x hx)

theorem counit_comp_mkₐ : (counit R I).comp (Ideal.Quotient.mkₐ R I) = counitAlgHom R H :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem counit_mk (x : H) :
    counit R I (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

def antipode : H ⧸ I →ₐ[R] H ⧸ I :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom R H)) (fun x hx => by
    simp only [AlgHom.comp_apply, antipodeAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hI.antipode_mem x hx)

theorem antipode_comp_mkₐ :
    (antipode R I).comp (Ideal.Quotient.mkₐ R I) =
      (Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem antipode_mk (x : H) :
    antipode R I (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (HopfAlgebra.antipode R x) := rfl

private theorem map_apply_eq_linearMap {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := rfl

theorem rTensor_counit_comul :
    (Algebra.TensorProduct.map (counit R I) (.id R (H ⧸ I))).comp (comul R I) =
      (Algebra.TensorProduct.lid R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.lid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (counitAlgHom R H).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.lTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.rTensor H) from
      (LinearMap.lTensor_comp_rTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.rTensor H) (Coalgebra.comul x) = 1 ⊗ₜ x from
    Coalgebra.rTensor_counit_comul x]
  simp

theorem lTensor_counit_comul :
    (Algebra.TensorProduct.map (.id R (H ⧸ I)) (counit R I)).comp (comul R I) =
      (Algebra.TensorProduct.rid R R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.rid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap (counitAlgHom R H).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.rTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.lTensor H) from
      (LinearMap.rTensor_comp_lTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.lTensor H) (Coalgebra.comul x) = x ⊗ₜ 1 from
    Coalgebra.lTensor_counit_comul x]
  simp

private theorem assoc_map_map_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (z : (A ⊗[R] A) ⊗[R] A) :
    (Algebra.TensorProduct.assoc R R R B B B)
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f z) =
      Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)
        (Algebra.TensorProduct.assoc R R R A A A z) := by
  induction z with
  | zero => simp
  | tmul xy c =>
    induction xy with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coassoc :
    (Algebra.TensorProduct.assoc R R R (H ⧸ I) (H ⧸ I) (H ⧸ I)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I))).comp (comul R I)) =
      (Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I)).comp (comul R I) := by
  refine Ideal.Quotient.algHom_ext R ?_
  refine AlgHom.ext fun x => ?_
  set π := Ideal.Quotient.mkₐ R I

  have hL : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I)) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π
          (Algebra.TensorProduct.map (comulAlgHom R H) (.id R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hR : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (.id R H) (comulAlgHom R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx : comul R I (π x) = Algebra.TensorProduct.map π π (comulAlgHom R H x) := by
    simp [π, Ideal.Quotient.mkₐ_eq_mk]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, hx, hL, hR, assoc_map_map_apply]
  congr 1
  have hassoc : ∀ z : (H ⊗[R] H) ⊗[R] H,
      Algebra.TensorProduct.assoc R R R H H H z = TensorProduct.assoc R H H H z := by
    intro z
    induction z with
    | zero => simp
    | tmul xy c =>
      induction xy with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [map_apply_eq_linearMap, map_apply_eq_linearMap, hassoc]
  exact Coalgebra.coassoc_apply x

instance instBialgebra : Bialgebra R (H ⧸ I) :=
  Bialgebra.ofAlgHom (comul R I) (counit R I) (coassoc R I) (rTensor_counit_comul R I)
    (lTensor_counit_comul R I)

theorem comulAlgHom_eq : comulAlgHom R (H ⧸ I) = comul R I := rfl

theorem counitAlgHom_eq : counitAlgHom R (H ⧸ I) = counit R I := rfl

theorem coalgebra_comul_mk (x : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

theorem coalgebra_counit_mk (x : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private theorem lift_antipode_id_comp_map :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (antipodeAlgHom R H) (.id R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_id_antipode_comp_map :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_antipodeAlgHom_id_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (antipodeAlgHom R H) (.id R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  have h := lift_antipodeAlgHom_comp_apply (AlgHom.id R H) (Coalgebra.comul (R := R) x)
  simp only [AlgHom.id_comp] at h
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, h, mul_antipode_rTensor_comul_apply]
  simp [Algebra.ofId_apply]

private theorem lift_id_antipodeAlgHom_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  have h := lift_comp_antipodeAlgHom_apply (AlgHom.id R H) (Coalgebra.comul (R := R) x)
  simp only [AlgHom.id_comp] at h
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, h, mul_antipode_lTensor_comul_apply]
  simp [Algebra.ofId_apply]

theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_antipode_id_comp_map, AlgHom.comp_assoc, lift_antipodeAlgHom_id_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_id_antipode_comp_map, AlgHom.comp_assoc, lift_id_antipodeAlgHom_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

instance instHopfAlgebra : HopfAlgebra R (H ⧸ I) :=
  HopfAlgebra.ofAlgHom (antipode R I) (mul_antipode_rTensor_comul R I)
    (mul_antipode_lTensor_comul R I)

theorem hopf_antipode_mk (x : H) :
    HopfAlgebra.antipode R (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I (HopfAlgebra.antipode R x) := rfl

instance instIsCocomm [Coalgebra.IsCocomm R H] : Coalgebra.IsCocomm R (H ⧸ I) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.comp_apply, coalgebra_comul_mk]
    conv_rhs => rw [← Coalgebra.comm_comp_comul R H]
    rw [LinearMap.comp_apply]
    generalize Coalgebra.comul (R := R) x = z
    induction z with
    | zero => simp
    | tmul a b => simp
    | add z w hz hw => simp only [map_add, hz, hw]

end HopfIdealQuotient

section Maps

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

def quotientBialgHom (I : Ideal H) [I.IsHopfIdeal' R] : H →ₐc[R] H ⧸ I :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I) (HopfIdealQuotient.counit_comp_mkₐ R I)
    (HopfIdealQuotient.comul_comp_mkₐ R I).symm

@[simp] theorem quotientBialgHom_apply (I : Ideal H) [I.IsHopfIdeal' R] (x : H) :
    quotientBialgHom R I x = Ideal.Quotient.mk I x := rfl

theorem quotientBialgHom_toAlgHom (I : Ideal H) [I.IsHopfIdeal' R] :
    (quotientBialgHom R I : H →ₐ[R] H ⧸ I) = Ideal.Quotient.mkₐ R I := rfl

theorem quotientBialgHom_surjective (I : Ideal H) [I.IsHopfIdeal' R] :
    Function.Surjective (quotientBialgHom R I) :=
  Ideal.Quotient.mk_surjective

def quotientFactorBialgHom {I J : Ideal H} [I.IsHopfIdeal' R] [J.IsHopfIdeal' R] (hIJ : I ≤ J) :
    H ⧸ I →ₐc[R] H ⧸ J :=
  BialgHom.ofAlgHom (Ideal.Quotient.factorₐ R hIJ)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      rw [AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk,
        HopfIdealQuotient.counitAlgHom_eq, HopfIdealQuotient.counitAlgHom_eq,
        HopfIdealQuotient.counit_comp_mkₐ, HopfIdealQuotient.counit_comp_mkₐ])
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk,
        HopfIdealQuotient.comulAlgHom_eq, HopfIdealQuotient.comulAlgHom_eq,
        HopfIdealQuotient.comul_comp_mkₐ, HopfIdealQuotient.comul_comp_mkₐ,
        ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, Ideal.Quotient.factorₐ_comp_mk])

@[simp] theorem quotientFactorBialgHom_apply_mk {I J : Ideal H} [I.IsHopfIdeal' R]
    [J.IsHopfIdeal' R] (hIJ : I ≤ J) (x : H) :
    quotientFactorBialgHom R hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x := rfl

theorem quotientFactorBialgHom_toAlgHom {I J : Ideal H} [I.IsHopfIdeal' R] [J.IsHopfIdeal' R]
    (hIJ : I ≤ J) :
    (quotientFactorBialgHom R hIJ : H ⧸ I →ₐ[R] H ⧸ J) = Ideal.Quotient.factorₐ R hIJ := rfl

theorem quotientFactorBialgHom_comp {I J : Ideal H} [I.IsHopfIdeal' R] [J.IsHopfIdeal' R]
    (hIJ : I ≤ J) :
    (quotientFactorBialgHom R hIJ).comp (quotientBialgHom R I) = quotientBialgHom R J := by
  ext x; rfl

theorem quotientFactorBialgHom_comp_toAlgHom {I J : Ideal H} [I.IsHopfIdeal' R]
    [J.IsHopfIdeal' R] (hIJ : I ≤ J) :
    (quotientFactorBialgHom R hIJ : H ⧸ I →ₐ[R] H ⧸ J).comp
        (quotientBialgHom R I : H →ₐ[R] H ⧸ I) = (quotientBialgHom R J : H →ₐ[R] H ⧸ J) := by
  ext x; rfl

theorem quotientFactorBialgHom_surjective {I J : Ideal H} [I.IsHopfIdeal' R] [J.IsHopfIdeal' R]
    (hIJ : I ≤ J) : Function.Surjective (quotientFactorBialgHom R hIJ) :=
  Ideal.Quotient.factor_surjective hIJ

variable {A : Type*} [CommRing A] [Algebra R A]

def quotientLiftPoint (I : Ideal H) (f : H →ₐ[R] A) (hf : ∀ x ∈ I, f x = 0) : H ⧸ I →ₐ[R] A :=
  Ideal.Quotient.liftₐ I f hf

@[simp] theorem quotientLiftPoint_mk (I : Ideal H) (f : H →ₐ[R] A) (hf : ∀ x ∈ I, f x = 0)
    (x : H) : quotientLiftPoint R I f hf (Ideal.Quotient.mk I x) = f x := rfl

theorem quotientLiftPoint_comp_mkₐ (I : Ideal H) (f : H →ₐ[R] A) (hf : ∀ x ∈ I, f x = 0) :
    (quotientLiftPoint R I f hf).comp (Ideal.Quotient.mkₐ R I) = f :=
  Ideal.Quotient.liftₐ_comp _ _ _

theorem comp_mkₐ_apply_eq_zero (I : Ideal H) (g : H ⧸ I →ₐ[R] A) (x : H) (hx : x ∈ I) :
    g.comp (Ideal.Quotient.mkₐ R I) x = 0 := by
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

theorem comp_mkₐ_injective (I : Ideal H) :
    Function.Injective fun g : H ⧸ I →ₐ[R] A => g.comp (Ideal.Quotient.mkₐ R I) :=
  fun _ _ h => Ideal.Quotient.algHom_ext R h

theorem quotientLiftPoint_comp (I : Ideal H) (g : H ⧸ I →ₐ[R] A) :
    quotientLiftPoint R I (g.comp (Ideal.Quotient.mkₐ R I))
      (fun x hx => comp_mkₐ_apply_eq_zero R I g x hx) = g :=
  comp_mkₐ_injective R I (quotientLiftPoint_comp_mkₐ R I _ _)

def quotientPointsEquiv (I : Ideal H) :
    (H ⧸ I →ₐ[R] A) ≃ {f : H →ₐ[R] A // ∀ x ∈ I, f x = 0} where
  toFun g := ⟨g.comp (Ideal.Quotient.mkₐ R I), fun x hx => comp_mkₐ_apply_eq_zero R I g x hx⟩
  invFun f := quotientLiftPoint R I f.1 f.2
  left_inv g := quotientLiftPoint_comp R I g
  right_inv f := Subtype.ext (quotientLiftPoint_comp_mkₐ R I f.1 f.2)

instance finiteType_quotient (I : Ideal H) [Algebra.FiniteType R H] :
    Algebra.FiniteType R (H ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)

def quotientBotAlgEquiv : (H ⧸ (⊥ : Ideal H)) ≃ₐ[R] H :=
  (AlgEquiv.ofBijective (Ideal.Quotient.mkₐ R (⊥ : Ideal H))
    ⟨fun x y h => by
      simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] using h,
      Ideal.Quotient.mkₐ_surjective R _⟩).symm

instance flat_quotient_bot [Module.Flat R H] : Module.Flat R (H ⧸ (⊥ : Ideal H)) :=
  Module.Flat.of_linearEquiv (quotientBotAlgEquiv R (H := H)).toLinearEquiv

end Maps

end HopfAlgebra

end


