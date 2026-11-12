-- Prove2me | Definitions.Def_QuantumGroupCodes836_Addressability_ClassFields
-- name    : QuantumGroupCodes836_Addressability_ClassFields
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T17:08:28.631143+00:00
-- url     : https://prove2.me/theorems/f5a51851-cb26-47b4-9c2e-aaf1a08e7c0f
-- title:
--   Intrinsic Hilbert class field and rational-place divisor classes
-- statement:
--   Fix a separable closure of a function field $F$ and a rational place $P$. Admissible finite intermediate fields are exactly the unramified abelian extensions in which $P$ splits completely. No unchanged-constant condition is built into admissibility.
--
--   $$\operatorname{Hil}_P(F)=\sup\{K:K/F\text{ is finite, unramified, abelian and }P\text{ splits}\}.$$
--
--   Existence as a maximum, finiteness and unchanged constants remain theorem content. Maximality also covers algebraic extensions through their finite subextensions. The degree-zero Picard group is the actual divisor group modulo principal divisors, with $[Q-P]$ formed from the two rational places. These definitions supply the class-field correspondence without assuming it.
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Proposition 4.2 and Theorem 4.3, p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Mathlib
import Definitions.Def_QuantumGroupCodes836_Addressability_FunctionFields

set_option autoImplicit false
noncomputable section

namespace QuantumGroupCodes836.Addressability
open AlgebraicCurve

/-- Place restriction and ramification are intrinsic valuation-ring conditions. -/
def rawAbove {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    (ι : F →+* E) (Q : Place k E) (P : Place k F) : Prop :=
  ∀ f, ι f ∈ Q.toValuationSubring ↔ f ∈ P.toValuationSubring

def rawUnramified {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    (ι : F →+* E) : Prop :=
  ∀ Q : Place k E, ∀ P : Place k F, rawAbove ι Q P →
    Q.ord (ι ((IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose : F)) = 1

def rawSplits {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    (ι : F →+* E) (P : Place k F) : Prop :=
  letI := ι.toAlgebra
  Nat.card {Q : Place k E // rawAbove ι Q P} = Module.finrank F E

/-- Intermediate fields of a fixed closure are the objects of class-field correspondence. -/
def AdmissibleClassField {k Ω : Type} [Field k] (F : FunctionFieldData k)
    [Field Ω] [Algebra F.carrier Ω] (P : Places F)
    (K : IntermediateField F.carrier Ω) : Prop :=
  letI : Algebra k K := ((algebraMap F.carrier K).comp (algebraMap k F.carrier)).toAlgebra
  Module.Finite F.carrier K ∧ IsGalois F.carrier K ∧
  (∀ σ τ : K ≃ₐ[F.carrier] K, σ * τ = τ * σ) ∧
  rawUnramified (k := k) (algebraMap F.carrier K) ∧ rawSplits (algebraMap F.carrier K) P

/-- Canonical supremum; existence/maximum/unchanged constants remain theorem content. -/
def hilbertClassField {k Ω : Type} [Field k] (F : FunctionFieldData k)
    [Field Ω] [Algebra F.carrier Ω] (P : Places F) : IntermediateField F.carrier Ω :=
  sSup {K | AdmissibleClassField F P K}

/-- The difference class of two rational places is formed in the actual degree-zero Picard group. -/
def differenceClass {k : Type} [Field k] {F : FunctionFieldData k}
    (P Q : Places F) (hP : P.deg = 1) (hQ : Q.deg = 1) : Pic0 k F.carrier :=
  Pic0.mk ⟨Finsupp.single Q 1 - Finsupp.single P 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hP, hQ]
    simp⟩

end QuantumGroupCodes836.Addressability


