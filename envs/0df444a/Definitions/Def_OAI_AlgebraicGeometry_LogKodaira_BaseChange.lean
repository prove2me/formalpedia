-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
-- name    : OAI_AlgebraicGeometry_LogKodaira_BaseChange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:46:27.696736+00:00
-- url     : https://prove2.me/theorems/8064b859-fd48-4eed-aae8-1da7a7314aac
-- title:
--   Exterior and tensor powers under change of rings, and the induced maps of canonical and pluricanonical differentials
-- statement:
--   This file builds the maps between modules of differential forms of top degree and of pluricanonical forms that are induced by ring homomorphisms. For a homomorphism of commutative rings $R\to A$ write $\Omega_{A/R}$ for the module of Kähler differentials, $d\colon A\to\Omega_{A/R}$ for the universal derivation, $\Omega^n_{A/R}:=\bigwedge^n_A\Omega_{A/R}$ for its $n$-th exterior power and $(\Omega^n_{A/R})^{\otimes m}$ for the $m$-fold tensor product of $\Omega^n_{A/R}$ over $A$.
--
--   1. **Change of rings for exterior and tensor powers.** Let $A\to B$ be a homomorphism of commutative rings, $M$ an $A$-module and $N$ a $B$-module, regarded also as an $A$-module through $A\to B$. Every $A$-linear map $\varphi\colon M\to N$ induces $A$-linear maps
--   $$\textstyle\bigwedge^n\varphi\colon\bigwedge^n_A M\to\bigwedge^n_B N,\qquad x_1\wedge\cdots\wedge x_n\mapsto\varphi(x_1)\wedge\cdots\wedge\varphi(x_n),$$
--   and $\varphi^{\otimes m}\colon M^{\otimes_A m}\to N^{\otimes_B m}$, $x_1\otimes\cdots\otimes x_m\mapsto\varphi(x_1)\otimes\cdots\otimes\varphi(x_m)$. The first is built from the wedge map $N^n\to\bigwedge^n_B N$, regarded as an alternating $A$-multilinear map.
--   2. **Canonical and pluricanonical modules.** For $R\to A$ and $n,m\in\mathbb{N}$: the module of $n$-forms $\Omega^n_{A/R}$ (the canonical module when $n$ is the relative dimension) and the module of pluricanonical forms $(\Omega^n_{A/R})^{\otimes m}$.
--   3. **Maps induced by a commutative square.** Let $R\to A\to B$ and $R\to S\to B$ be ring homomorphisms forming a commutative square. The map of differentials $\Omega_{A/R}\to\Omega_{B/S}$, $da\mapsto d\bar a$ (with $\bar a$ the image of $a$ in $B$), induces the $A$-linear map
--   $$\Omega^n_{A/R}\to\Omega^n_{B/S},\qquad da_1\wedge\cdots\wedge da_n\mapsto d\bar a_1\wedge\cdots\wedge d\bar a_n,$$
--   and, by item 1, its $m$-th tensor power $(\Omega^n_{A/R})^{\otimes m}\to(\Omega^n_{B/S})^{\otimes m}$.
--
--   These maps are the means of transporting differential forms between rings: from the coordinate ring of an affine chart of a variety to its function field (with $S=R$), and from the coordinate ring of a chart of the total space of a fibration to the function field of a fibre (with $S$ the residue field of a point of the base).
--
--   **Formalization Note** Item 1 consists of `alternatingRestriction`, `exteriorScalarMap` with its computation rule `exteriorScalarMap_wedge`, and `tensorScalarMap`; item 2 is `Canonical R A n` and `Pluricanonical R A n m`; item 3 is `exteriorDifferentialMap R S A B n` and `pluricanonicalMap R S A B n m`, built from Mathlib's `KaehlerDifferential.map R S A B`. Tensor powers are `PiTensorProduct` over `Fin m`, and commutativity of the square is expressed by the scalar-tower instances for $R\to A\to B$ and $R\to S\to B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/BaseChange.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/BaseChange.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LogKodairaFiberNegative mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
open scoped TensorProduct
namespace ReverseLogKodaira.DifferentialBaseChange

section Linear
variable (A B M N : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

def alternatingRestriction (n : ℕ) : N [⋀^Fin n]→ₗ[A] (⋀[B]^n N) where
  toMultilinearMap := (exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' := (exteriorPower.ιMulti B n).map_eq_zero_of_eq

def exteriorScalarMap (f : M →ₗ[A] N) (n : ℕ) : (⋀[A]^n M) →ₗ[A] (⋀[B]^n N) :=
  exteriorPower.alternatingMapLinearEquiv
    ((alternatingRestriction A B N n).compLinearMap f)

def tensorScalarMap (f : M →ₗ[A] N) (m : ℕ) : (⨂[A]^m M) →ₗ[A] (⨂[B]^m N) :=
  PiTensorProduct.lift (((PiTensorProduct.tprod B).restrictScalars A).compLinearMap
    fun _ : Fin m => f)

end Linear

section Differentials
variable (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

abbrev Canonical (n : ℕ) := ⋀[A]^n (KaehlerDifferential R A)
abbrev Pluricanonical (n m : ℕ) := ⨂[A]^m (Canonical R A n)

def exteriorDifferentialMap (n : ℕ) : Canonical R A n →ₗ[A] Canonical S B n :=
  exteriorScalarMap A B _ _ (KaehlerDifferential.map R S A B) n

def pluricanonicalMap (n m : ℕ) : Pluricanonical R A n m →ₗ[A] Pluricanonical S B n m :=
  tensorScalarMap A B _ _ (exteriorDifferentialMap R S A B n) m

end Differentials

section LinearProofs
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

@[simp] lemma exteriorScalarMap_wedge (f : M →ₗ[A] N) (n : ℕ) (v : Fin n → M) :
    exteriorScalarMap A B M N f n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (f ∘ v) := by
  simp only [exteriorScalarMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

end LinearProofs

section DifferentialProofs
variable (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

 

end DifferentialProofs

end ReverseLogKodaira.DifferentialBaseChange

end
end

end OAI


