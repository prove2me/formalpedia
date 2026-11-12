-- Prove2me | Definitions.Def_QuantumGroupCodes836_Addressability_FunctionFields
-- name    : QuantumGroupCodes836_Addressability_FunctionFields
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T17:07:30.04375+00:00
-- url     : https://prove2.me/theorems/ac156649-adbb-4086-a0b3-56fe1b2df098
-- title:
--   Intrinsic function fields, evaluation codes and divisor transport
-- statement:
--   Let $k$ be a finite field and $F/k$ a one-variable function field with full constant field $k$. Places are nontrivial discrete valuation rings, and divisors have finite integer support. Evaluation at a rational place is the actual residue map identified with $k$.
--
--   $$L(D)=\{0\}\cup\{f:(f)+D\ge0\},\qquad C_L(P,D)=\{(f(P_i))_i:f\in L(D)\}.$$
--
--   The genus is the dimension of everywhere regular Kähler differentials. The conorm uses valuation-ring restriction and ramification indices, including when the constant field changes. Simple-pole residues are computed in local uniformizer coordinates. These definitions impose no separating-chart hypothesis and contain no existence assertion for a lifted family.
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), §2.2, pp.6–8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_QuantumGroupCodes836_Addressability_Linear

set_option autoImplicit false
noncomputable section

namespace QuantumGroupCodes836.Addressability

open AlgebraicCurve KaehlerDifferential

/-- No separability of a chosen rational parameter is assumed. -/
structure FunctionFieldData (k : Type) [Field k] where
  carrier : Type
  field : Field carrier
  algebra : Algebra k carrier
  oneVariable : ∃ z : carrier, Transcendental k z ∧
    FiniteDimensional (IntermediateField.adjoin k ({z} : Set carrier)) carrier
  fullConstants : ∀ x : carrier, IsAlgebraic k x → ∃ a : k, algebraMap k carrier a = x

attribute [instance] FunctionFieldData.field FunctionFieldData.algebra

abbrev Places {k : Type} [Field k] (F : FunctionFieldData k) := Place k F.carrier
def localParameter {k : Type} [Field k] {F : FunctionFieldData k} (P : Places F) : F.carrier :=
  ((IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose : F.carrier)

abbrev Divisors {k : Type} [Field k] (F : FunctionFieldData k) := Divisor k F.carrier

def effective {k : Type} [Field k] {F : FunctionFieldData k} (D : Divisors F) : Prop :=
  ∀ P, 0 ≤ D P

def rrSpace {k : Type} [Field k] {F : FunctionFieldData k} (D : Divisors F) :
    Submodule k F.carrier :=
  Submodule.span k {f | f = 0 ∨ ∀ P : Places F, -D P ≤ P.ord f}

/-- The genus is the dimension of the space of everywhere regular differentials. -/
def genus {k : Type} [Field k] (F : FunctionFieldData k) : ℕ :=
  Module.finrank k (Submodule.span k {ω : Ω[F.carrier⁄k] |
    ω = 0 ∨ ∀ P : Places F, 0 ≤ P.ordDifferential ω})

def finiteDivisor {I : Type*} (f : I → ℤ) : I →₀ ℤ := by
  classical
  exact if h : (Function.support f).Finite then Finsupp.ofSupportFinite f h else 0

def differentialDivisor {k : Type} [Field k] {F : FunctionFieldData k}
    (ω : Ω[F.carrier⁄k]) : Divisors F := finiteDivisor fun P => P.ordDifferential ω

structure EvaluationData {k : Type} [Field k] (F : FunctionFieldData k) where
  n : ℕ
  places : Fin n → Places F
  distinct : Function.Injective places
  rational : ∀ i, (places i).deg = 1

/-- Evaluation takes place in the actual residue field; rationality identifies it with k. -/
def rationalValue {k : Type} [Field k] {F : FunctionFieldData k}
    (P : Places F) (f : F.carrier) : k := by
  classical
  exact if h : ∃ a : k, ∃ hf : f ∈ P.toValuationSubring,
    IsLocalRing.residue P.toValuationSubring ⟨f, hf⟩ = algebraMap k P.ResidueField a
    then h.choose else 0

def evaluationDivisor {k : Type} [Field k] {F : FunctionFieldData k}
    (P : EvaluationData F) : Divisors F := ∑ i, Finsupp.single (P.places i) 1

def agCode {k : Type} [Field k] {F : FunctionFieldData k}
    (P : EvaluationData F) (D : Divisors F) : Code k (Fin P.n) :=
  Submodule.span k {v | ∃ f ∈ rrSpace D, v = fun i => rationalValue (P.places i) f}

def simplePoleResidue {k : Type} [Field k] {F : FunctionFieldData k}
    (P : Places F) (ω : Ω[F.carrier⁄k]) : k :=
  rationalValue P (localParameter P * P.differentialCoeff ω)

/-- Extension data contain only field embeddings, not lifting or splitting conclusions. -/
structure FieldExtension {k l : Type} [Field k] [Field l] [Algebra k l]
    (F : FunctionFieldData k) (E : FunctionFieldData l) where
  inclusion : F.carrier →+* E.carrier
  constants : ∀ a : k, inclusion (algebraMap k F.carrier a) =
    algebraMap l E.carrier (algebraMap k l a)
  finite : letI := inclusion.toAlgebra; Module.Finite F.carrier E.carrier

/-- The valuation-ring definition of lying above works across a change of constants. -/
def LiesAbove {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E)
    (Q : Places E) (P : Places F) : Prop :=
  ∀ f, T.inclusion f ∈ Q.toValuationSubring ↔ f ∈ P.toValuationSubring

def ramificationIndex {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E)
    (Q : Places E) (P : Places F) : ℕ := (Q.ord (T.inclusion (localParameter P))).natAbs

def Unramified {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E) : Prop :=
  ∀ Q P, LiesAbove T Q P → ramificationIndex T Q P = 1

def extensionDegree {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E) : ℕ :=
  letI := T.inclusion.toAlgebra
  Module.finrank F.carrier E.carrier

def SplitsCompletely {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E)
    (P : Places F) : Prop := Nat.card {Q : Places E // LiesAbove T Q P} = extensionDegree T

def conorm {k l : Type} [Field k] [Field l] [Algebra k l]
    {F : FunctionFieldData k} {E : FunctionFieldData l} (T : FieldExtension F E)
    (D : Divisors F) : Divisors E :=
  letI := Classical.propDecidable
  finiteDivisor fun Q => ∑ P ∈ D.support,
    if LiesAbove T Q P then (ramificationIndex T Q P : ℤ) * D P else 0

end QuantumGroupCodes836.Addressability


