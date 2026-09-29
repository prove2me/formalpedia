-- Prove2me | Definitions.Def_M4aHerbrand_GenuineDescent
-- name    : M4aHerbrand_GenuineDescent
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/5a93b48d-9ec0-5dc8-afb2-d3bf67de8230
-- title:
--   Adelic base change and Galois descent data for number fields
-- statement:
--   Throughout, $A$ is a Dedekind domain with fraction field $K$ a number field, free and finite as a $\mathbb{Z}$-module, likewise $B'$ with fraction field $L$, and $L$ is a $K$-algebra. The input datum is the project structure `AdeleBaseChange A K B' L`: a ring homomorphism $\beta\colon \mathbb{A}_{A,K}\to\mathbb{A}_{B',L}$ between adele rings compatible with the structure maps from $K$ and $L$, together with an isomorphism $\mathbb{A}_{A,K}\otimes_K L\simeq\mathbb{A}_{B',L}$ of $\mathbb{A}_{A,K}$-algebras (scalars acting through $\beta$) sending $1\otimes l$ to the image of $l$. For such a $B$ and each $\sigma\in\operatorname{Aut}_K(L)$, `actOf` is the ring automorphism of $\mathbb{A}_{B',L}$ obtained by transporting $\mathrm{id}\otimes\sigma$ through that isomorphism. The first result, `hcont_of_continuous_β`, asserts that if $\beta$ is continuous then every such automorphism is continuous, by the module-topology statement `continuous_conjAct_of_continuous_of_free`. Hence `descentOfContinuousβ` produces an `IdeleGaloisDescent B' K L`, i.e. a monoid homomorphism $\operatorname{Aut}_K(L)\to\operatorname{RingAut}(\mathbb{A}_{B',L})$ extending the action on principal adeles and valued in continuous automorphisms; `descentOfContinuousβ_act` identifies its action with `actOf`. A helper, `continuous_β_of_prodMap`, gives continuity of $\beta$ when it is the product of a continuous map on infinite adeles and a continuous map on finite adeles.
--
--   For rings of integers, `genuineDescent` is the same construction with $A=\mathcal{O}_K$, $B'=\mathcal{O}_L$. Given any $\mathbb{A}_K$-algebra isomorphism $\mathbb{A}_K\otimes_K L\simeq\mathbb{A}_L$ over the conorm map `genuineβ` (the product of the archimedean conorm and `finiteConorm`) which sends $1\otimes l$ to $l$, `bgenOfTensorEquiv` assembles the base-change datum and `genuineDescentOfTensorEquiv` the resulting descent datum, continuity of `genuineβ` being supplied by `continuous_genuineβ`; `genuineDescentOfTensorEquiv_act` records the action. Finally `genuineBaseChange` and `genuineDescentDatum` instantiate these with `genuineTensorEquiv`, with `genuineBaseChange_β` identifying the underlying homomorphism as `genuineβ` and `genuineDescentDatum_act` its action as `actOf` at `genuineTensorEquiv`.
--
--   **Relation to Mathlib.** Mathlib provides the adele, finite adele and infinite adele rings used here; the structures `AdeleBaseChange` and `IdeleGaloisDescent`, packaging a base-change isomorphism $\mathbb{A}_K\otimes_K L\simeq\mathbb{A}_L$ and a continuous Galois action on $\mathbb{A}_L$, are the project's own.
--
--   **Where it is used.** The descent datum `genuineDescentDatum K L` is what makes $\operatorname{Gal}(L/K)$ act on $\mathbb{A}_L^\times$ and on the idèle class group, via `IdeleGaloisDescent.classAct`, `ideleClassNorm` and `ideleClassDerive`; these are the inputs to the Herbrand-quotient computations in the class-field-theoretic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_GenuineDescent.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_M4aHerbrand_GenuineTensorEquiv
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace M4aHerbrand.GenuineDescent

open NumberField TensorProduct IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge

section AnyProducer

variable {A K B' L : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [NumberField K] [Algebra A K]
  [IsFractionRing A K] [Module.Free ℤ A] [Module.Finite ℤ A]
  [CommRing B'] [IsDedekindDomain B'] [Field L] [NumberField L] [Algebra B' L] [IsFractionRing B' L]
  [Module.Free ℤ B'] [Module.Finite ℤ B'] [Algebra K L]

theorem hcont_of_continuous_β (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) :
    ∀ σ : L ≃ₐ[K] L, letI := B.β.toAlgebra; Continuous (actOf A K B' L B.tensorEquiv σ) := by
  letI := B.β.toAlgebra
  intro σ
  exact continuous_conjAct_of_continuous_of_free A K B' L hβ B.tensorEquiv σ

def descentOfContinuousβ (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) : IdeleGaloisDescent B' K L :=
  B.toIdeleGaloisDescent (hcont_of_continuous_β B hβ)

theorem descentOfContinuousβ_act (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) (g : L ≃ₐ[K] L) :
    (descentOfContinuousβ B hβ).act g = letI := B.β.toAlgebra; actOf A K B' L B.tensorEquiv g := rfl

omit [NumberField K] [Module.Free ℤ A] [Module.Finite ℤ A] [NumberField L] [Module.Free ℤ B'] [Module.Finite ℤ B'] in

theorem continuous_β_of_prodMap (B : AdeleBaseChange A K B' L)
    (βi : InfiniteAdeleRing K →+* InfiniteAdeleRing L) (βf : FiniteAdeleRing A K →+* FiniteAdeleRing B' L)
    (h : B.β = RingHom.prodMap βi βf) (hinf : Continuous βi) (hfin : Continuous βf) : Continuous B.β := by
  rw [h]; exact Continuous.prodMap hinf hfin

end AnyProducer
section RingOfIntegers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def genuineDescent (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (hβ : Continuous B.β) : IdeleGaloisDescent (𝓞 L) K L :=
  descentOfContinuousβ B hβ

end RingOfIntegers

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def bgenOfTensorEquiv
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) :
    AdeleBaseChange (𝓞 K) K (𝓞 L) L where
  β := genuineβ K L
  β_compat := genuineβ_compat K L
  tensorEquiv := te
  tensorEquiv_one_tmul := hte

def genuineDescentOfTensorEquiv
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) :
    IdeleGaloisDescent (𝓞 L) K L :=
  genuineDescent (bgenOfTensorEquiv K L te hte) (continuous_genuineβ K L)

theorem genuineDescentOfTensorEquiv_act
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) (g : L ≃ₐ[K] L) :
    (genuineDescentOfTensorEquiv K L te hte).act g =
      letI := (genuineβ K L).toAlgebra; actOf (𝓞 K) K (𝓞 L) L te g := rfl

end Genuine

section Construction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def genuineBaseChange : AdeleBaseChange (𝓞 K) K (𝓞 L) L :=
  bgenOfTensorEquiv K L (genuineTensorEquiv K L) (genuineTensorEquiv_one_tmul K L)

theorem genuineBaseChange_β : (genuineBaseChange K L).β = genuineβ K L := rfl

def genuineDescentDatum : IdeleGaloisDescent (𝓞 L) K L :=
  genuineDescentOfTensorEquiv K L (genuineTensorEquiv K L) (genuineTensorEquiv_one_tmul K L)

theorem genuineDescentDatum_act (g : L ≃ₐ[K] L) :
    (genuineDescentDatum K L).act g =
      letI := (genuineβ K L).toAlgebra; actOf (𝓞 K) K (𝓞 L) L (genuineTensorEquiv K L) g := rfl

end Construction

end M4aHerbrand.GenuineDescent

end


