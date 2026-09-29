-- Prove2me | Definitions.Def_HopfAlgebra_CartierDualMap
-- name    : HopfAlgebra_CartierDualMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/763ac12d-a6d1-5b8f-ac0f-6440bdee76ce
-- title:
--   Functoriality of the Cartier dual of a bialgebra
-- statement:
--   Throughout, $R$ is a commutative ring and $A$, $B$, $C$ are commutative $R$-bialgebras that are finite and free as $R$-modules; [`CartierDual R A`](../def/HopfAlgebra_CartierDual.html#L12) denotes the $R$-module dual $A^{\vee}=\mathrm{Hom}_R(A,R)$ equipped with the bialgebra structure transposing that of $A$ (convolution product $\langle\varphi\psi,a\rangle=\langle\varphi\otimes\psi,\Delta a\rangle$ with unit the counit of $A$, comultiplication determined by $\langle\Delta\varphi,a\otimes b\rangle=\varphi(ab)$ and counit $\varphi\mapsto\varphi(1)$). Two things are defined. First, `pairing` presents evaluation $\langle\varphi,a\rangle=\varphi(a)$ as an $R$-linear map $A^{\vee}\to\mathrm{Hom}_R(A,R)$, i.e. the canonical identification of the Cartier dual with the linear dual, together with the evaluation formula `pairing_apply`.
--
--   Second, for a bialgebra homomorphism $f\colon A\to B$ (Mathlib's `A →ₐc[R] B`, an algebra map compatible with comultiplication and counit) the transpose $\varphi\mapsto\varphi\circ f$ is constructed in three stages: `mapLinear f` is the $R$-linear map $B^{\vee}\to A^{\vee}$ obtained from `LinearMap.dualMap` of $f$ through the identification above, with $(\mathrm{mapLinear}\,f\,\varphi)(a)=\varphi(f a)$; `mapAlgHom f` upgrades it to an $R$-algebra homomorphism, multiplicativity `mapLinear_mul` coming from compatibility of $f$ with the comultiplications and unitality `mapLinear_one` from compatibility with the counits; and `map f : CartierDual R B →ₐc[R] CartierDual R A` upgrades it further to a bialgebra homomorphism, the two remaining conditions being `counit_comp_mapAlgHom` (from $f(1)=1$) and `map_comp_comul_mapAlgHom` (from multiplicativity of $f$, checked against the pairing $\langle\Delta\varphi\circ f,a\otimes b\rangle=\varphi(f(a)f(b))$). Auxiliary lemmas `dualDistrib_map_map` and `dualDistrib_map_mapAlgHom` record the compatibility of the evaluation pairing on tensor squares with $f\otimes f$. The assignment is contravariantly functorial: `map_id` and `map_comp`, which states $\mathrm{map}(g\circ f)=\mathrm{map}(f)\circ\mathrm{map}(g)$ in the diagrammatic sense. Finally `congr e` turns a bialgebra isomorphism $e\colon A\simeq B$ into the bialgebra isomorphism $B^{\vee}\simeq A^{\vee}$ with inverse the transpose of $e^{-1}$, and `toDual_map`, `map_apply`, `congr_apply`, `congr_symm_apply` give the evaluation formulas.
--
--   **Relation to Mathlib.** Mathlib supplies the linear dual and its transpose (`Module.Dual`, `LinearMap.dualMap`) and the morphism classes `→ₐc[R]`, `≃ₐc[R]`; the Cartier dual bialgebra structure on the dual of a finite free bialgebra is the project's own, and this module adds its functoriality in the source bialgebra.
--
--   **Where it is used.** These transposes are the basic functoriality needed wherever Cartier duality is used for finite flat group schemes in the local analysis of the Galois representations attached to elliptic curves and modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HopfAlgebra_CartierDualMap.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

namespace CartierDual

noncomputable section

universe u v w x

section Pairing

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Bialgebra R A]

def pairing : CartierDual R A →ₗ[R] A →ₗ[R] R where
  toFun φ := toDual R A φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pairing_apply (φ : CartierDual R A) (a : A) : pairing R A φ a = φ a := rfl

end Pairing

section Map

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {B : Type w} [CommRing B] [Bialgebra R B] [Module.Finite R B] [Module.Free R B]
variable {C : Type x} [CommRing C] [Bialgebra R C] [Module.Finite R C] [Module.Free R C]

def mapLinear (f : A →ₐc[R] B) : CartierDual R B →ₗ[R] CartierDual R A :=
  (ofDual R A).toLinearMap ∘ₗ (f : A →ₗ[R] B).dualMap ∘ₗ (toDual R B).toLinearMap

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B] in
@[simp] theorem mapLinear_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    mapLinear f φ a = φ (f a) := rfl

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B] in

theorem dualDistrib_map_map (f : A →ₐc[R] B) (φ ψ : CartierDual R B) (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R B B (toDual R B φ ⊗ₜ[R] toDual R B ψ)
        (TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B) z) =
      TensorProduct.dualDistrib R A A (toDual R A (mapLinear f φ) ⊗ₜ[R] toDual R A (mapLinear f ψ)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mapLinear_mul (f : A →ₐc[R] B) (φ ψ : CartierDual R B) :
    mapLinear f (φ * ψ) = mapLinear f φ * mapLinear f ψ := by
  apply CartierDual.ext; intro a
  rw [mapLinear_apply, mul_apply, mul_apply, ← dualDistrib_map_map]
  congr 1
  exact (CoalgHomClass.map_comp_comul_apply f a).symm

theorem mapLinear_one (f : A →ₐc[R] B) : mapLinear f 1 = 1 := by
  apply CartierDual.ext; intro a
  rw [mapLinear_apply, one_apply, one_apply]
  exact CoalgHomClass.counit_comp_apply f a

def mapAlgHom (f : A →ₐc[R] B) : CartierDual R B →ₐ[R] CartierDual R A :=
  AlgHom.ofLinearMap (mapLinear f) (mapLinear_one f) (mapLinear_mul f)

@[simp] theorem mapAlgHom_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    mapAlgHom f φ a = φ (f a) := rfl

theorem dualDistrib_map_mapAlgHom (f : A →ₐc[R] B) (w : CartierDual R B ⊗[R] CartierDual R B) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap
          (TensorProduct.map (mapLinear f) (mapLinear f) w)) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R B B
        (TensorProduct.map (toDual R B).toLinearMap (toDual R B).toLinearMap w) (f a ⊗ₜ[R] f b) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul φ ψ => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem counit_comp_mapAlgHom (f : A →ₐc[R] B) :
    (Bialgebra.counitAlgHom R (CartierDual R A)).comp (mapAlgHom f) = Bialgebra.counitAlgHom R (CartierDual R B) := by
  apply AlgHom.ext; intro φ
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
  exact (counit_apply (mapAlgHom f φ)).trans ((congrArg φ (map_one f)).trans (counit_apply φ).symm)

theorem map_comp_comul_mapAlgHom (f : A →ₐc[R] B) :
    (Algebra.TensorProduct.map (mapAlgHom f) (mapAlgHom f)).comp (Bialgebra.comulAlgHom R (CartierDual R B)) =
      (Bialgebra.comulAlgHom R (CartierDual R A)).comp (mapAlgHom f) := by
  apply AlgHom.ext; intro φ
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply]
  have hmap : (Algebra.TensorProduct.map (mapAlgHom f) (mapAlgHom f)).toLinearMap =
      TensorProduct.map (mapLinear f) (mapLinear f) := TensorProduct.ext' fun _ _ => rfl
  rw [← AlgHom.toLinearMap_apply, hmap]
  apply tmul_eq_of_pairing_eq
  intro a b
  have h1 := dualDistrib_map_mapAlgHom f (Coalgebra.comul (R := R) φ) a b
  have h2 := comul_pairing (R := R) (A := B) φ (f a) (f b)
  have h3 := comul_pairing (R := R) (A := A) (mapAlgHom f φ) a b
  exact (h1.trans (h2.trans (congrArg φ (map_mul f a b).symm))).trans h3.symm

def map (f : A →ₐc[R] B) : CartierDual R B →ₐc[R] CartierDual R A :=
  BialgHom.ofAlgHom (mapAlgHom f) (counit_comp_mapAlgHom f) (map_comp_comul_mapAlgHom f)

@[simp] theorem map_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) : map f φ a = φ (f a) := rfl

theorem toDual_map (f : A →ₐc[R] B) (φ : CartierDual R B) :
    toDual R A (map f φ) = (f : A →ₗ[R] B).dualMap (toDual R B φ) := rfl

theorem map_id : map (BialgHom.id R A) = BialgHom.id R (CartierDual R A) := by
  apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a; rfl

theorem map_comp (g : B →ₐc[R] C) (f : A →ₐc[R] B) : map (g.comp f) = (map f).comp (map g) := by
  apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a; rfl

def congr (e : A ≃ₐc[R] B) : CartierDual R B ≃ₐc[R] CartierDual R A :=
  BialgEquiv.ofBialgHom (map (e : A →ₐc[R] B)) (map (e.symm : B →ₐc[R] A))
    (by apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a
        show φ (e.symm (e a)) = φ a
        rw [BialgEquiv.symm_apply_apply])
    (by apply BialgHom.ext; intro φ; apply CartierDual.ext; intro b
        show φ (e (e.symm b)) = φ b
        rw [BialgEquiv.apply_symm_apply])

@[simp] theorem congr_apply (e : A ≃ₐc[R] B) (φ : CartierDual R B) (a : A) : congr e φ a = φ (e a) := rfl

@[simp] theorem congr_symm_apply (e : A ≃ₐc[R] B) (φ : CartierDual R A) (b : B) :
    (congr e).symm φ b = φ (e.symm b) := rfl

end Map

end

end CartierDual


