-- Prove2me | Definitions.Def_APF_B01_DeclaredInput
-- name    : APF_B01_DeclaredInput
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-06T20:53:55.975987+00:00
-- url     : https://prove2.me/theorems/46883303-9331-4021-b473-9c09354c6ee0
-- title:
--   Declared input — B01 — Continuation identity
-- statement:
--   A physical object is its admissible continuation profile. Physical facts are fixed by that structure.
-- source:
--   APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-10-04.1; SHA-256 bb3b59f6011dd70c5d34c9c830ab65aad0a224b11e26d4d438c4e1ab2ad445c4; declared input B01.

import Init

/-!
Declared input B01, FOUNDATION_INPUTS revision 2026-10-04.1.
"A physical object is its admissible continuation profile. Physical facts are
fixed by that structure."

Source vocabulary: one original context; X is its raw substrate; Process is
its original finite-continuation domain; profile is the ORIGINAL admissible
continuation profile. This module does not construct profile or attach laws to
an arbitrary use relation. Supplement v9.27 lines 1220-1254.

PhysicalFact indexes ALL original physical propositions, with truth their
original semantics, never a chosen tested/held subset. ReadoutFact, ResultFact,
and AdmissionFact index ALL propositions about original readouts, result
relations (including their full arguments), and admission, respectively. Their
truth families below make these required parts of the full clause explicit;
they are not extra premises on a structure. A physical-valued observation is
covered by all propositions about its value, not a chosen finite test family.
The full PhysicalFact family remains present alongside those named families.
Supplement 1063-1065 and author direction item4a fix this interpretation.

The data's physical interpretation is source vocabulary to be cold-reviewed,
not a theorem about every arbitrary instantiation. In particular, substituting
an empty or selected fact family does not instantiate the approved B01.
-/
set_option autoImplicit false
universe uX uP uF uR uO uA

namespace APFB01

/-- The source quotient by equality of full admissible continuation profiles.
`Quot` uses the same relation as the existing `Quotient (continuationSetoid ...)`;
its ordinary equivalence proof is unnecessary to declare this quotient type.
This is the first B01 sentence, not a proof of its physical applicability. -/
def PhysicalState {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) : Type uX :=
  Quot (fun x y : X => profile x = profile y)

/-- The original raw representative's class; Supplement 1303-1309. -/
def physicalClass {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (x : X) : PhysicalState profile :=
  Quot.mk _ x

/-- Exact quotient descent of a physical proposition, in the source's
factorization form (Supplement 1312-1322). No descent is asserted here. -/
def Descends {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (fact : X → Prop) : Prop :=
  ∃ descended : PhysicalState profile → Prop,
    ∀ x : X, fact x ↔ descended (physicalClass profile x)

end APFB01

/-- The designated full B01 INPUT PREDICATE. It is defined, not proved or
postulated by a Lean axiom. The first conjunct is over ALL physical facts;
the other conjuncts explicitly retain the author's named readout/result/
admission scope. Those named families are already physical at the source
interpretation, so their explicit inclusion does not add a physical input.
No consequence T/C/naming law or held-source premise is part of this module. -/
def APF_B01_DeclaredInput
    {X : Type uX} {Process : Type uP} {PhysicalFact : Type uF}
    {ReadoutFact : Type uR} {ResultFact : Type uO} {AdmissionFact : Type uA}
    (profile : X → Process → Prop)
    (truth : PhysicalFact → X → Prop)
    (readoutTruth : ReadoutFact → X → Prop)
    (resultTruth : ResultFact → X → Prop)
    (admissionTruth : AdmissionFact → X → Prop) : Prop :=
  (∀ f : PhysicalFact, APFB01.Descends profile (truth f)) ∧
  (∀ f : ReadoutFact, APFB01.Descends profile (readoutTruth f)) ∧
  (∀ f : ResultFact, APFB01.Descends profile (resultTruth f)) ∧
  (∀ f : AdmissionFact, APFB01.Descends profile (admissionTruth f))


