-- Prove2me | Definitions.Def_M4aHerbrand_AdeleBaseChange
-- name    : M4aHerbrand_AdeleBaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/d4a6f139-8cb1-5a0f-9272-de9338810675
-- title:
--   Adele base change data and the induced Galois action
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $E$, $S$ a Dedekind domain with fraction field $F$, and $F$ is an $E$-algebra; $\mathbb{A}_E =$ `AdeleRing R E` and $\mathbb{A}_F =$ `AdeleRing S F` are Mathlib's adele rings. Given an algebra structure of $\mathbb{A}_F$ over $\mathbb{A}_E$ and an $\mathbb{A}_E$-algebra equivalence $te : \mathbb{A}_E \otimes_E F \to \mathbb{A}_F$, `actOf` sends $\sigma \in \operatorname{Aut}_E(F)$ to the ring automorphism $te \circ (\mathrm{id} \otimes \sigma) \circ te^{-1}$ of $\mathbb{A}_F$. The accompanying lemmas record that this assignment sends $1$ to $1$ and respects multiplication, and that, provided $te(1 \otimes f)$ is the principal adele of $f$ for all $f \in F$, `actOf` of $\sigma$ carries the principal adele of $f$ to that of $\sigma f$.
--
--   The structure `AdeleBaseChange R E S F` packages such a comparison as data: a ring homomorphism $\beta : \mathbb{A}_E \to \mathbb{A}_F$; the condition that $\beta$ followed by nothing agrees with $E \to F \to \mathbb{A}_F$ on principal adeles of $E$; an $\mathbb{A}_E$-algebra equivalence $\mathbb{A}_E \otimes_E F \simeq \mathbb{A}_F$ for the algebra structure determined by $\beta$; and the normalisation $1 \otimes f \mapsto$ the principal adele of $f$. No continuity is part of the structure. From such a datum $B$ are defined: `adelicNorm`, the multiplicative map $\mathbb{A}_F \to \mathbb{A}_E$ given by Mathlib's `Algebra.norm` for the algebra structure determined by $\beta$; `idelicNorm`, its effect on unit groups; `actHom`, the monoid homomorphism $\operatorname{Aut}_E(F) \to \operatorname{RingAut}(\mathbb{A}_F)$ assembled from `actOf`; and `toIdeleGaloisDescent`, which, given as an extra hypothesis the continuity of each of these automorphisms, produces an `IdeleGaloisDescent S E F`, i.e. a continuous action of $\operatorname{Aut}_E(F)$ on $\mathbb{A}_F$ by ring automorphisms compatible with the principal embedding of $F$. Finally `selfBaseChange` is the datum at $R = S$, $E = F$, with $\beta$ the identity and the equivalence $\mathbb{A}_E \otimes_E E \simeq \mathbb{A}_E$. Existence of such a datum for a nontrivial extension is not asserted here.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring `AdeleRing` but no base-change comparison or Galois action on it; `AdeleBaseChange`, `actOf` and the derived norm and descent maps are the project's own, with the comparison isomorphism $\mathbb{A}_E \otimes_E F \simeq \mathbb{A}_F$ carried as data rather than proved.
--
--   **Where it is used.** These definitions provide the vocabulary in which the Galois action on the ideles of $F$ over $E$, and the adelic and idelic norm maps, are expressed, feeding the idele class group constructions (`IdeleGaloisDescent`, `ideleClassNorm`, `ideleClassDerive`) of the class field theory layer of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_AdeleBaseChange.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField TensorProduct

namespace M4aHerbrand

noncomputable section

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

def actOf [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (σ : F ≃ₐ[E] F) : AdeleRing S F ≃+* AdeleRing S F :=
  (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te)).toRingEquiv

theorem actOf_algebraMap [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (hte : ∀ f : F, te (1 ⊗ₜ[E] f) = algebraMap F (AdeleRing S F) f)
    (σ : F ≃ₐ[E] F) (f : F) :
    actOf R E S F te σ (algebraMap F (AdeleRing S F) f) =
      algebraMap F (AdeleRing S F) (σ f) := by
  show te ((Algebra.TensorProduct.congr AlgEquiv.refl σ) (te.symm (algebraMap F _ f))) = _
  rw [← hte f, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  exact hte (σ f)

theorem actOf_one [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) :
    actOf R E S F te 1 = 1 := by
  have h1 : (1 : F ≃ₐ[E] F) = AlgEquiv.refl := rfl
  ext x
  show te ((Algebra.TensorProduct.congr AlgEquiv.refl 1) (te.symm x)) = x
  rw [h1, Algebra.TensorProduct.congr_refl]
  exact te.apply_symm_apply x

theorem actOf_mul [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (σ τ : F ≃ₐ[E] F) :
    actOf R E S F te (σ * τ) = actOf R E S F te σ * actOf R E S F te τ := by
  ext x
  show te ((Algebra.TensorProduct.congr AlgEquiv.refl (σ * τ)) (te.symm x)) =
    te ((Algebra.TensorProduct.congr AlgEquiv.refl σ)
      (te.symm (te ((Algebra.TensorProduct.congr AlgEquiv.refl τ) (te.symm x)))))
  rw [AlgEquiv.symm_apply_apply]
  have hmul : (σ * τ : F ≃ₐ[E] F) = τ.trans σ := rfl
  have key : Algebra.TensorProduct.congr
      (AlgEquiv.refl : AdeleRing R E ≃ₐ[AdeleRing R E] _) (σ * τ) =
    (Algebra.TensorProduct.congr AlgEquiv.refl τ).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl σ) := by
    rw [hmul]
    exact Algebra.TensorProduct.congr_trans AlgEquiv.refl AlgEquiv.refl τ σ
  rw [key, AlgEquiv.trans_apply]

structure AdeleBaseChange where
  β : AdeleRing R E →+* AdeleRing S F
  β_compat : ∀ e : E, β (algebraMap E (AdeleRing R E) e) =
    algebraMap F (AdeleRing S F) (algebraMap E F e)
  tensorEquiv : letI := β.toAlgebra
    ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F
  tensorEquiv_one_tmul : ∀ f : F,
    letI := β.toAlgebra
    tensorEquiv ((1 : AdeleRing R E) ⊗ₜ[E] f) = algebraMap F (AdeleRing S F) f

namespace AdeleBaseChange

variable {R E S F}

def adelicNorm (B : AdeleBaseChange R E S F) : AdeleRing S F →* AdeleRing R E :=
  letI := B.β.toAlgebra
  Algebra.norm (AdeleRing R E)

def idelicNorm (B : AdeleBaseChange R E S F) :
    (AdeleRing S F)ˣ →* (AdeleRing R E)ˣ :=
  Units.map B.adelicNorm

def actHom (B : AdeleBaseChange R E S F) :
    (F ≃ₐ[E] F) →* RingAut (AdeleRing S F) where
  toFun σ := letI := B.β.toAlgebra; actOf R E S F B.tensorEquiv σ
  map_one' := by letI := B.β.toAlgebra; exact actOf_one R E S F B.tensorEquiv
  map_mul' σ τ := by letI := B.β.toAlgebra; exact actOf_mul R E S F B.tensorEquiv σ τ

def toIdeleGaloisDescent (B : AdeleBaseChange R E S F)
    (hcont : ∀ σ : F ≃ₐ[E] F,
      letI := B.β.toAlgebra; Continuous (actOf R E S F B.tensorEquiv σ)) :
    IdeleGaloisDescent S E F where
  act := B.actHom
  compat g x := by
    letI := B.β.toAlgebra
    show (actOf R E S F B.tensorEquiv g) (algebraMap F (AdeleRing S F) x) = _
    exact actOf_algebraMap R E S F B.tensorEquiv B.tensorEquiv_one_tmul g x
  continuous_act := hcont

end AdeleBaseChange

section SelfInhabitant

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]

def selfBaseChange : AdeleBaseChange R E R E where
  β := RingHom.id _
  β_compat e := rfl
  tensorEquiv := letI := (RingHom.id (AdeleRing R E)).toAlgebra
    Algebra.TensorProduct.rid E (AdeleRing R E) (AdeleRing R E)
  tensorEquiv_one_tmul f := by
    letI := (RingHom.id (AdeleRing R E)).toAlgebra
    show (f • (1 : AdeleRing R E)) = algebraMap E (AdeleRing R E) f
    exact (Algebra.algebraMap_eq_smul_one f).symm

end SelfInhabitant

end

end M4aHerbrand


