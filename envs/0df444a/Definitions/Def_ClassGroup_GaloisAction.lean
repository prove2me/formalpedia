-- Prove2me | Definitions.Def_ClassGroup_GaloisAction
-- name    : ClassGroup_GaloisAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/c7bd2cff-1869-58d6-a310-18e9766fcf23
-- title:
--   Galois action on the mod-p class group of cyclotomic fields
-- statement:
--   The module assembles, for a number field $K$ that is a $p$-th cyclotomic extension of $\mathbb Q$, an action of $(\mathbb Z/p)^\times$ on $\mathrm{Cl}(\mathcal O_K)/p\,\mathrm{Cl}(\mathcal O_K)$, together with the functoriality of class groups that it rests on. First come transport lemmas along a ring isomorphism $g : R \simeq R'$ of domains: the fractional ideal attached to an integral ideal $I$ is carried by `FractionalIdeal.ringEquivOfRingEquiv` to the ideal $g(I)$; `ClassGroup.mulEquiv g` sends the class of a unit fractional ideal $I$ to that of $J$ whenever $g$ transports $I$ to $J$; [`Ideal.mapNonZero`](../def/ClassGroup_GaloisAction.html#L65) pushes a nonzero ideal (an element of the monoid of non-zero-divisors of $\mathrm{Ideal}\,R$) forward to $g(I)$, which is again nonzero by injectivity of $g$; and for Dedekind domains $\mathrm{ClassGroup.mulEquiv}$ sends the class of $P$ to the class of $g(P)$, acts as the identity for $g = \mathrm{id}$, and satisfies $\mathrm{mulEquiv}(h \circ g) = \mathrm{mulEquiv}(h) \circ \mathrm{mulEquiv}(g)$. Next, [`algAutToRingAut`](../def/ClassGroup_GaloisAction.html#L112) is the monoid homomorphism forgetting $A$-linearity, from $A$-algebra automorphisms of $B$ to ring automorphisms of $B$, and [`galRestrictionDatum`](../def/ClassGroup_GaloisAction.html#L126), in the standard setting of $B$ the integral closure of $A$ in an algebraic extension $L$ of the fraction field $K$ of $A$, is the resulting monoid homomorphism $(L \simeq_K L) \to (B \simeq B)$ restricting automorphisms to $B$.
--
--   In the `JacobiSumStickelberger` namespace, `clEndHom` upgrades the $\mathbb Z/p$-linear endomorphism `clEnd` of $\mathrm{ClGalModule}\,p\,R = \mathrm{Cl}(R)/p$ (the additive class group modulo its $p$-th multiples) to a monoid homomorphism from ring automorphisms of the Dedekind domain $R$ to $\mathrm{End}_{\mathbb Z/p}$, the two multiplicativity statements being exactly the functoriality lemmas above; `clEnd_clProj_mk0` records its effect on the class of an ideal $P$, namely the class of $g(P)$. For $K$ a number field with $K/\mathbb Q$ a $p$-th cyclotomic extension, `cycloGalEquiv` is the isomorphism $(K \simeq_{\mathbb Q} K) \simeq (\mathbb Z/p)^\times$ of Mathlib's `IsCyclotomicExtension.autEquivPow`, fed with irreducibility of the $p$-th cyclotomic polynomial over $\mathbb Q$; `clRingAction` composes its inverse with restriction to $\mathcal O_K$, giving $(\mathbb Z/p)^\times \to (\mathcal O_K \simeq \mathcal O_K)$; and `clGalAction` composes further with `clEndHom` to give the action $(\mathbb Z/p)^\times \to \mathrm{End}_{\mathbb Z/p}(\mathrm{Cl}(\mathcal O_K)/p)$. The final lemma states that $d \in (\mathbb Z/p)^\times$ sends the class of $P$ to the class of its image under `clRingAction p K d`.
--
--   **Relation to Mathlib.** Mathlib supplies `ClassGroup.mulEquiv`, `FractionalIdeal.ringEquivOfRingEquiv`, `galRestrict` and `IsCyclotomicExtension.autEquivPow`; the functoriality lemmas for `ClassGroup.mulEquiv` (identity, composition, effect on `mk0`), the pushforward [`Ideal.mapNonZero`](../def/ClassGroup_GaloisAction.html#L65) of a nonzero ideal, and the packaging of restriction to the integral closure as a monoid homomorphism ([`algAutToRingAut`](../def/ClassGroup_GaloisAction.html#L112), [`galRestrictionDatum`](../def/ClassGroup_GaloisAction.html#L126)) are the project's own.
--
--   **Where it is used.** These definitions provide the concrete $(\mathbb Z/p)^\times$-module $\mathrm{Cl}(\mathcal O_K)/p$ for the cyclotomic field $K = \mathbb Q(\zeta_p)$, on which the Jacobi-sum and Stickelberger arguments of the project's cyclotomic strand operate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ClassGroup_GaloisAction.lean

import Mathlib
import Definitions.Def_ClassGroup_ModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NumberField nonZeroDivisors
open Polynomial

section Fidl
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (L : Type*) [Field L] [Algebra R' L] [IsFractionRing R' L]

theorem FractionalIdeal.ringEquivOfRingEquiv_coeIdeal (g : R ≃+* R') (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K L g (I : FractionalIdeal R⁰ K) =
      ((I.map (g : R →+* R') : Ideal R') : FractionalIdeal R'⁰ L) := by
  ext x
  rw [← FractionalIdeal.mem_coe, ← FractionalIdeal.mem_coe,
    FractionalIdeal.ringEquivOfRingEquiv_apply, FractionalIdeal.coe_mk,
    FractionalIdeal.val_eq_coe]
  simp only [Submodule.mem_map, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨-, ⟨a, haI, rfl⟩, rfl⟩
    exact ⟨g a, Ideal.mem_map_of_mem _ haI,
      by rw [LinearEquiv.coe_coe, IsFractionRing.semilinearEquivOfRingEquiv_apply,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap]⟩
  · rintro ⟨b, hbI, rfl⟩
    obtain ⟨a, haI, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ g.surjective).mp hbI
    exact ⟨algebraMap R K a, ⟨a, haI, rfl⟩,
      by rw [LinearEquiv.coe_coe, IsFractionRing.semilinearEquivOfRingEquiv_apply,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap]⟩

end Fidl

section ClassGroupFunctoriality
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']

theorem ClassGroup.mulEquiv_mk_eq_mk (g : R ≃+* R')
    {I : (FractionalIdeal R⁰ (FractionRing R))ˣ}
    {J : (FractionalIdeal R'⁰ (FractionRing R'))ˣ}
    (hIJ : FractionalIdeal.ringEquivOfRingEquiv (FractionRing R) (FractionRing R') g
        (I : FractionalIdeal R⁰ (FractionRing R)) = (J : FractionalIdeal R'⁰ (FractionRing R'))) :
    ClassGroup.mulEquiv g (ClassGroup.mk _ I) = ClassGroup.mk _ J := by
  have hself : ∀ (J' : (FractionalIdeal R'⁰ (FractionRing R'))ˣ),
      ClassGroup.equiv (R := R') (FractionRing R') (ClassGroup.mk _ J') =
        QuotientGroup.mk' _ J' := by
    intro J'
    rw [ClassGroup.equiv_mk]
    congr 1
    rw [← Units.val_inj, Units.coe_mapEquiv]
    simp [FractionalIdeal.canonicalEquiv_self]
  rw [ClassGroup.mulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, ClassGroup.equiv_mk,
    show Units.mapEquiv (↑(FractionalIdeal.canonicalEquiv R⁰ (FractionRing R) (FractionRing R)))
        I = I by
      rw [← Units.val_inj, Units.coe_mapEquiv]
      simp [FractionalIdeal.canonicalEquiv_self],
    QuotientGroup.congr_mk']
  rw [MulEquiv.symm_apply_eq, hself]
  congr 1
  rw [← Units.val_inj, Units.coe_mapEquiv]
  exact hIJ

def Ideal.mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) : (Ideal R')⁰ :=
  ⟨(P : Ideal R).map (g : R →+* R'), by
    have hinj : Function.Injective ((g : R →+* R') : R → R') := g.injective
    refine mem_nonZeroDivisors_iff_ne_zero.mpr fun hbot => ?_
    refine mem_nonZeroDivisors_iff_ne_zero.mp P.2 ?_
    rw [Ideal.zero_eq_bot] at hbot ⊢
    exact (Ideal.map_eq_bot_iff_of_injective hinj).mp hbot⟩

@[simp] lemma Ideal.coe_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    (Ideal.mapNonZero g P : Ideal R') = (P : Ideal R).map (g : R →+* R') := rfl

variable [IsDedekindDomain R] [IsDedekindDomain R']

theorem ClassGroup.mulEquiv_mk0 (g : R ≃+* R') (P : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 P) = ClassGroup.mk0 (Ideal.mapNonZero g P) := by
  show ClassGroup.mulEquiv g (ClassGroup.mk _ (FractionalIdeal.mk0 (FractionRing R) P)) =
    ClassGroup.mk _ (FractionalIdeal.mk0 (FractionRing R') (Ideal.mapNonZero g P))
  refine ClassGroup.mulEquiv_mk_eq_mk g ?_
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0,
    FractionalIdeal.ringEquivOfRingEquiv_coeIdeal, Ideal.coe_mapNonZero]

theorem ClassGroup.mulEquiv_refl_apply (C : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) C = C := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0]
  congr 1
  refine Subtype.ext ?_
  rw [Ideal.coe_mapNonZero,
    show ((RingEquiv.refl R : R ≃+* R) : R →+* R) = RingHom.id R from RingHom.ext fun _ => rfl,
    Ideal.map_id]

theorem ClassGroup.mulEquiv_trans_apply {R'' : Type*} [CommRing R''] [IsDomain R'']
    [IsDedekindDomain R''] (g : R ≃+* R') (h : R' ≃+* R'') (C : ClassGroup R) :
    ClassGroup.mulEquiv (g.trans h) C = ClassGroup.mulEquiv h (ClassGroup.mulEquiv g C) := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0, ClassGroup.mulEquiv_mk0, ClassGroup.mulEquiv_mk0]
  congr 1
  refine Subtype.ext ?_
  rw [Ideal.coe_mapNonZero, Ideal.coe_mapNonZero, Ideal.coe_mapNonZero,
    show ((g.trans h : R ≃+* R'') : R →+* R'') = (h : R' →+* R'').comp (g : R →+* R') from
      RingHom.ext fun _ => rfl,
    ← Ideal.map_map]

end ClassGroupFunctoriality

section GalRestrict

def algAutToRingAut (A B : Type*) [CommSemiring A] [Semiring B] [Algebra A B] :
    (B ≃ₐ[A] B) →* (B ≃+* B) where
  toFun := AlgEquiv.toRingEquiv
  map_one' := RingEquiv.ext fun _ => rfl
  map_mul' _ _ := RingEquiv.ext fun _ => rfl

@[simp] lemma algAutToRingAut_apply {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (e : B ≃ₐ[A] B) (x : B) : algAutToRingAut A B e x = e x := rfl

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

noncomputable def galRestrictionDatum : (L ≃ₐ[K] L) →* (B ≃+* B) :=
  (algAutToRingAut A B).comp (galRestrict A K L B).toMonoidHom

@[simp] lemma galRestrictionDatum_apply (g : L ≃ₐ[K] L) (x : B) :
    galRestrictionDatum A K L B g x = galRestrict A K L B g x := rfl

end GalRestrict

namespace JacobiSumStickelberger

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]

section DedekindAction

variable (R : Type*) [CommRing R] [IsDomain R]

variable {R} in
variable [IsDedekindDomain R] in

theorem clEnd_clProj_mk0 (g : R ≃+* R) (P : (Ideal R)⁰) :
    clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p R (Additive.ofMul (ClassGroup.mk0 (Ideal.mapNonZero g P))) := by
  rw [clEnd_clProj, ClassGroup.mulEquiv_mk0]

variable {R} in
variable [IsDedekindDomain R] in

noncomputable def clEndHom : (R ≃+* R) →* Module.End (ZMod p) (ClGalModule p R) where
  toFun := clEnd p
  map_one' := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨C, rfl⟩ := clProj_surjective p R a
    rw [Module.End.one_apply]
    show clProj p R (Additive.ofMul (ClassGroup.mulEquiv (RingEquiv.refl R) C.toMul)) =
      clProj p R C
    rw [ClassGroup.mulEquiv_refl_apply]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨C, rfl⟩ := clProj_surjective p R a
    rw [Module.End.mul_apply]
    show clProj p R (Additive.ofMul (ClassGroup.mulEquiv (h.trans g) C.toMul)) =
      clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mulEquiv h C.toMul)))
    rw [clEnd_clProj, ClassGroup.mulEquiv_trans_apply]

end DedekindAction

section Cyclotomic

variable (K : Type*) [Field K] [NumberField K]

noncomputable def cycloGalEquiv [IsCyclotomicExtension {p} ℚ K] :
    (K ≃ₐ[ℚ] K) ≃* (ZMod p)ˣ :=
  IsCyclotomicExtension.autEquivPow K
    (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne p)))

noncomputable def clRingAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* ((𝓞 K) ≃+* (𝓞 K)) :=
  (galRestrictionDatum ℤ ℚ K (𝓞 K)).comp (cycloGalEquiv p K).symm.toMonoidHom

noncomputable def clGalAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* Module.End (ZMod p) (ClGalModule p (𝓞 K)) :=
  (clEndHom p).comp (clRingAction p K)

theorem clGalAction_clProj_mk0 [IsCyclotomicExtension {p} ℚ K] (d : (ZMod p)ˣ)
    (P : (Ideal (𝓞 K))⁰) :
    clGalAction p K d (clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0
        (Ideal.mapNonZero (clRingAction p K d) P))) :=
  clEnd_clProj_mk0 p (clRingAction p K d) P

end Cyclotomic

end ClassGroupCarrier

end JacobiSumStickelberger


