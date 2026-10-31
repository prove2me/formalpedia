-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66
-- name    : QAlgorithms_Papers_Independent_Intake100_P66
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:11:39.292121+00:00
-- url     : https://prove2.me/theorems/1814dd26-2137-407a-b7fd-4054e39cd6e8
-- title:
--   Definitions for Infinitely many constrained inequalities for the von Neumann entropy
-- statement:
--   The objects the formalized statements of *Infinitely many constrained inequalities for the von Neumann entropy* (arXiv:1107.0624) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `entropyParty`: PDF pp.3,7: distinct labels a,b,c,x_1,...,x_n.
--   - `entropyLabelA`: PDF p.3: label A.
--   - `b`: PDF p.3: label B.
--   - `c`: PDF p.3: label C.
--   - `x`: PDF p.3: the i-th X label (Lean indices start at zero).
--   - `entropyProductBasis`: PDF pp.1,3: product computational basis for arbitrary finite local dimensions.
--   - `entropySubsystemBasis`: PDF p.1: basis of a subsystem.
--   - `entropyJoinBasis`: PDF p.1: assemble kept and discarded tensor coordinates without identification.
--   - `entropyMarginal`: PDF p.1, S(J)=S(rho_J): the actual partial trace over complementary factors. The same discarded coordinate occurs in both matrix indices.
--   - `entropyOfSubset`: PDF p.1: marginal von Neumann entropy in bits; the normalized empty coordinate is zero. For a density matrix the empty marginal is the one-dimensional trace-one matrix.
--   - `Form`: PDF p.3, (5): coefficient vector on the nonempty entropy coordinates. It is stored on all subsets with the empty coordinate identically zero.
--   - `entropyAtom`: PDF pp.1,3: the coordinate S(U); S(empty)=0 is eliminated syntactically.
--   - `evaluateEntropyForm`: PDF p.3, (5): evaluation of a coefficient vector on a real set function.
--   - `cmiForm`: PDF pp.1--3: coefficient vector of I(U:V|W).
--   - `miForm`: PDF p.2, (2): mutual information, with disjoint grouped subsystems.
--   - `wmoForm`: PDF p.1: weak monotonicity S(UV)+S(UW)-S(V)-S(W).
--   - `DisjointTriple`: PDF pp.2,7: pairwise disjoint substitutions; empty subsets are allowed.
--   - `DisjointInstance`: PDF p.3: all p+3 substituted parties are disjoint, without requiring exhaustion.
--   - `familyForm`: PDF p.3, (10), and p.8, (37): C_p residual, right side minus left side. The subtraction p-1 is REAL subtraction, including when this definition is used at p=0.
--   - `primeForm`: PDF p.9, (46): purified variant, still a statement about arbitrary mixed states.
--   - `cAsXForm`: PDF p.10, (47): C is additionally permitted as an X party.
--   - `cAsXPrimeForm`: PDF p.10, (48): purified C-as-X variant. The subtraction is S(AB), and its mutual-information coefficient is p+1.
--   - `IsSubmodular`: PDF p.2: submodularity on every pair of subsets, equivalent to all disjoint SSA instances.
--   - `QuantumBasic`: PDF pp.1--3: every quantum basic-inequality instance on this fixed ground set.
--   - `ClassicalBasic`: PDF p.2: classical basic inequalities use monotonicity in place of WMO.
--   - `MatchingInstance`: PDF p.3: a constrained instance is eligible only if each of its nontrivial zero constraints is one of the target constraints. An identically zero form imposes no constraint. This is coefficient equality, not vanishing at a witness.
--   - `Derivable`: PDF p.3: finite nonnegative combination of eligible inequalities, plus an arbitrary real combination of the zero constraints. Equality is of coefficients.
--   - `constraints`: PDF pp.3,9: the two fixed-label zero-CMI constraints.
--   - `standardX`: PDF p.3: the standard X singleton substitution.
--   - `standardFamily`: PDF p.3: the standard instance of C_n.
--   - `OtherFamily`: PDF pp.6--9: other family instances whose constraints match the target pair.
--   - `specialPart`: PDF p.7: the K part of a subset M=JK.
--   - `xCount`: PDF p.7: |J|, the number of X labels in M.
--   - `clwTheta`: PDF p.7, (29): the entire theta table, including its outer factor n+1.
--   - `clwLambda`: PDF p.7, (30): the entire lambda table is negated.
--   - `clwMu`: PDF p.7, (31)--(32): mu is supported on the EXACT subsets {a} and {a,b}.
--   - `separatingF`: PDF p.7, (28): the explicitly constructed function f, not an arbitrary polymatroid.
--   - `oldWitness`: PDF p.10: the explicit four-party table e, in the same label convention with D=x_1.
--   - `oldForm`: PDF p.10: old Linden--Winter residual I(C:D)-I(AB:C), with labels fixed.
--   - `NewFourParty`: PDF p.10: exactly the three new fixed-label four-party comparison forms.
--   - `oldConstraints`: PDF p.10: all three constraints of the old inequality, including I(A:B|D)=0.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, https://arxiv.org/abs/1107.0624v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Cadney--Linden--Winter, arXiv:1107.0624v1. Finite nonzero local complex
Hilbert spaces, actual partial traces, and entropy in bits. The algebraic
independence statements use normalized real set functions, not entropy vectors
of states. Proposition 2 is recorded as accepted-library reuse in items.json.
The density predicate, entropy in bits, and partial trace are imported from the
frozen library. Remaining wrappers and coefficient tables are paper-specific.
Compilation is pending handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators
open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3,7: distinct labels a,b,c,x_1,...,x_n. -/
abbrev entropyParty (n : ℕ) := Fin 3 ⊕ Fin n

/-- PDF p.3: label A. -/
def entropyLabelA {n : ℕ} : entropyParty n := Sum.inl 0

/-- PDF p.3: label B. -/
def b {n : ℕ} : entropyParty n := Sum.inl 1

/-- PDF p.3: label C. -/
def c {n : ℕ} : entropyParty n := Sum.inl 2

/-- PDF p.3: the i-th X label (Lean indices start at zero). -/
def x {n : ℕ} (i : Fin n) : entropyParty n := Sum.inr i

/-- PDF pp.1,3: product computational basis for arbitrary finite local dimensions. -/
abbrev entropyProductBasis {n : ℕ} (d : entropyParty n → ℕ) := (j : entropyParty n) → Fin (d j)

/-- PDF p.1: basis of a subsystem. -/
abbrev entropySubsystemBasis {n : ℕ} (d : entropyParty n → ℕ) (S : Finset (entropyParty n)) :=
  (j : S) → Fin (d j.1)

/-- PDF p.1: assemble kept and discarded tensor coordinates without identification. -/
def entropyJoinBasis {n : ℕ} {d : entropyParty n → ℕ} {S : Finset (entropyParty n)}
    (u : entropySubsystemBasis d S) (z : entropySubsystemBasis d Sᶜ) : entropyProductBasis d :=
  fun j => if hj : j ∈ S then u ⟨j, hj⟩ else z ⟨j, by simpa using hj⟩

/-- PDF p.1, S(J)=S(rho_J): the actual partial trace over complementary factors.
The same discarded coordinate occurs in both matrix indices. -/
def entropyMarginal {n : ℕ} (d : entropyParty n → ℕ)
    (rho : Matrix (entropyProductBasis d) (entropyProductBasis d) ℂ) (S : Finset (entropyParty n)) :
    Matrix (entropySubsystemBasis d S) (entropySubsystemBasis d S) ℂ :=
  QAlgorithms.traceLeft
    (fun u v : entropySubsystemBasis d Sᶜ × entropySubsystemBasis d S =>
      rho (entropyJoinBasis u.2 u.1) (entropyJoinBasis v.2 v.1))

/-- PDF p.1: marginal von Neumann entropy in bits; the normalized empty coordinate is zero.
For a density matrix the empty marginal is the one-dimensional trace-one matrix. -/
def entropyOfSubset {n : ℕ} (d : entropyParty n → ℕ)
    (rho : Matrix (entropyProductBasis d) (entropyProductBasis d) ℂ) (S : Finset (entropyParty n)) : ℝ :=
  if S = ∅ then 0 else vnEntropy (entropyMarginal d rho S)

example {n : ℕ} (d : entropyParty n → ℕ) (rho : Matrix (entropyProductBasis d) (entropyProductBasis d) ℂ) :
    entropyOfSubset d rho ∅ = 0 := by simp [entropyOfSubset]

example {n : ℕ} {d : entropyParty n → ℕ} {S : Finset (entropyParty n)}
    (u : entropySubsystemBasis d S) (z : entropySubsystemBasis d Sᶜ) (j : entropyParty n) (hj : j ∈ S) :
    entropyJoinBasis u z j = u ⟨j, hj⟩ := by simp [entropyJoinBasis, hj]

section LinearForms

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- PDF p.3, (5): coefficient vector on the nonempty entropy coordinates.
It is stored on all subsets with the empty coordinate identically zero. -/
abbrev Form (P : Type*) := Finset P → ℝ

/-- PDF pp.1,3: the coordinate S(U); S(empty)=0 is eliminated syntactically. -/
def entropyAtom (U : Finset P) : Form P :=
  if U = ∅ then 0 else fun V => if V = U then 1 else 0

/-- PDF p.3, (5): evaluation of a coefficient vector on a real set function. -/
def evaluateEntropyForm (L : Form P) (h : Finset P → ℝ) : ℝ := ∑ U, L U * h U

/-- PDF pp.1--3: coefficient vector of I(U:V|W). -/
def cmiForm (U V W : Finset P) : Form P :=
  entropyAtom (U ∪ W) + entropyAtom (V ∪ W) - entropyAtom W - entropyAtom (U ∪ V ∪ W)

/-- PDF p.2, (2): mutual information, with disjoint grouped subsystems. -/
def miForm (U V : Finset P) : Form P := entropyAtom U + entropyAtom V - entropyAtom (U ∪ V)

/-- PDF p.1: weak monotonicity S(UV)+S(UW)-S(V)-S(W). -/
def wmoForm (U V W : Finset P) : Form P :=
  entropyAtom (U ∪ V) + entropyAtom (U ∪ W) - entropyAtom V - entropyAtom W

/-- PDF pp.2,7: pairwise disjoint substitutions; empty subsets are allowed. -/
def DisjointTriple (U V W : Finset P) : Prop :=
  Disjoint U V ∧ Disjoint U W ∧ Disjoint V W

/-- PDF p.3: all p+3 substituted parties are disjoint, without requiring exhaustion. -/
def DisjointInstance {p : ℕ} (U V W : Finset P) (alpha : Fin p → Finset P) : Prop :=
  DisjointTriple U V W ∧
    (∀ i, Disjoint (alpha i) (U ∪ V ∪ W)) ∧
    (∀ i j, i ≠ j → Disjoint (alpha i) (alpha j))

/-- PDF p.3, (10), and p.8, (37): C_p residual, right side minus left side.
The subtraction p-1 is REAL subtraction, including when this definition is used at p=0. -/
def familyForm {p : ℕ} (U V W : Finset P) (alpha : Fin p → Finset P) : Form P :=
  (∑ i, cmiForm U V (alpha i)) + (∑ i, entropyAtom (alpha i)) -
    entropyAtom (Finset.univ.biUnion alpha) - ((p : ℝ) - 1) • miForm (U ∪ V) W

/-- PDF p.9, (46): purified variant, still a statement about arbitrary mixed states. -/
def primeForm {p : ℕ} (U V W : Finset P) (alpha : Fin p → Finset P) : Form P :=
  (∑ i, cmiForm U V (alpha i)) + (∑ i, entropyAtom (alpha i)) +
    cmiForm U V (W ∪ Finset.univ.biUnion alpha) +
    entropyAtom (U ∪ V ∪ W ∪ Finset.univ.biUnion alpha) - entropyAtom (U ∪ V ∪ W) -
    (p : ℝ) • miForm (U ∪ V) W

/-- PDF p.10, (47): C is additionally permitted as an X party. -/
def cAsXForm {p : ℕ} (U V W : Finset P) (alpha : Fin p → Finset P) : Form P :=
  (∑ i, cmiForm U V (alpha i)) + (∑ i, entropyAtom (alpha i)) + cmiForm U V W +
    entropyAtom W - entropyAtom (W ∪ Finset.univ.biUnion alpha) - (p : ℝ) • miForm (U ∪ V) W

/-- PDF p.10, (48): purified C-as-X variant. The subtraction is S(AB), and
its mutual-information coefficient is p+1. -/
def cAsXPrimeForm {p : ℕ} (U V W : Finset P) (alpha : Fin p → Finset P) : Form P :=
  (∑ i, cmiForm U V (alpha i)) + (∑ i, entropyAtom (alpha i)) +
    cmiForm U V (W ∪ Finset.univ.biUnion alpha) +
    entropyAtom (U ∪ V ∪ W ∪ Finset.univ.biUnion alpha) + cmiForm U V W + entropyAtom W -
    entropyAtom (U ∪ V) - ((p : ℝ) + 1) • miForm (U ∪ V) W

/-- PDF p.2: submodularity on every pair of subsets, equivalent to all disjoint SSA instances. -/
def IsSubmodular (h : Finset P → ℝ) : Prop :=
  ∀ U V, h (U ∪ V) + h (U ∩ V) ≤ h U + h V

/-- PDF pp.1--3: every quantum basic-inequality instance on this fixed ground set. -/
def QuantumBasic (L : Form P) : Prop :=
  ∃ U V W, DisjointTriple U V W ∧ (L = cmiForm U V W ∨ L = wmoForm U V W)

/-- PDF p.2: classical basic inequalities use monotonicity in place of WMO. -/
def ClassicalBasic (L : Form P) : Prop :=
  (∃ U V W, DisjointTriple U V W ∧ L = cmiForm U V W) ∨
    (∃ U V, U ⊆ V ∧ L = entropyAtom V - entropyAtom U)

/-- PDF p.3: a constrained instance is eligible only if each of its nontrivial
zero constraints is one of the target constraints. An identically zero form
imposes no constraint. This is coefficient equality, not vanishing at a witness. -/
def MatchingInstance {p : ℕ} (Z : Finset (Form P))
    (U V W : Finset P) (alpha : Fin p → Finset P) : Prop :=
  DisjointInstance U V W alpha ∧
    (cmiForm U W V = 0 ∨ cmiForm U W V ∈ Z) ∧
    (cmiForm V W U = 0 ∨ cmiForm V W U ∈ Z)

/-- PDF p.3: finite nonnegative combination of eligible inequalities, plus
an arbitrary real combination of the zero constraints. Equality is of coefficients. -/
def Derivable (allowed : Set (Form P)) (Z : Finset (Form P)) (target : Form P) : Prop :=
  ∃ (k : ℕ) (L : Fin k → Form P) (w : Fin k → ℝ) (r : Z → ℝ),
    (∀ i, L i ∈ allowed) ∧ (∀ i, 0 ≤ w i) ∧
      target = (∑ i, w i • L i) + ∑ z : Z, r z • z.1

example : entropyAtom (∅ : Finset P) = 0 := by simp [entropyAtom]

example (h : Finset P → ℝ) : evaluateEntropyForm (0 : Form P) h = 0 := by simp [evaluateEntropyForm]

example (U V : Finset P) : DisjointTriple U V ∅ ↔ Disjoint U V := by
  simp [DisjointTriple]

end LinearForms

/-- PDF pp.3,9: the two fixed-label zero-CMI constraints. -/
def constraints (n : ℕ) : Finset (Form (entropyParty n)) :=
  {cmiForm {entropyLabelA} {c} {b}, cmiForm {b} {c} {entropyLabelA}}

/-- PDF p.3: the standard X singleton substitution. -/
def standardX {n : ℕ} (i : Fin n) : Finset (entropyParty n) := {x i}

/-- PDF p.3: the standard instance of C_n. -/
def standardFamily (n : ℕ) : Form (entropyParty n) := familyForm {entropyLabelA} {b} {c} standardX

/-- PDF pp.6--9: other family instances whose constraints match the target pair. -/
def OtherFamily (n : ℕ) (L : Form (entropyParty n)) : Prop :=
  ∃ (p : ℕ) (U V W : Finset (entropyParty n)) (alpha : Fin p → Finset (entropyParty n)),
    2 ≤ p ∧ p ≠ n ∧ MatchingInstance (constraints n) U V W alpha ∧
      L = familyForm U V W alpha

/-- PDF p.7: the K part of a subset M=JK. -/
def specialPart {n : ℕ} (M : Finset (entropyParty n)) : Finset (Fin 3) :=
  Finset.univ.filter (fun j => Sum.inl j ∈ M)

/-- PDF p.7: |J|, the number of X labels in M. -/
def xCount {n : ℕ} (M : Finset (entropyParty n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ∈ M)).card

/-- PDF p.7, (29): the entire theta table, including its outer factor n+1. -/
def clwTheta (n : ℕ) (K : Finset (Fin 3)) : ℝ :=
  let t : ℝ := n
  (t + 1) *
    (if 0 ∈ K then
      if 1 ∈ K then 2*t^3 + 8*t^2 + 4*t - 1
      else if 2 ∈ K then 2*t^3 + 5*t^2 + 2*t else 2*t^3 + 5*t^2
    else if 1 ∈ K then
      if 2 ∈ K then 6*t^2 + 4*t - 1 else 4*t^2 + 2*t - 1
    else if 2 ∈ K then 3*t^2 + t else 0)

/-- PDF p.7, (30): the entire lambda table is negated. -/
def clwLambda (n : ℕ) (K : Finset (Fin 3)) : ℝ :=
  let t : ℝ := n
  let tableValue : ℝ :=
    if 0 ∈ K then
      if 1 ∈ K then 2*t^3 + 8*t^2 + 4*t - 1
      else 2*t^3 + 5*t^2 + 2*t
    else if 1 ∈ K then
      if 2 ∈ K then 6*t^2 + 4*t - 1 else 4*t^2 + 2*t - 1
    else if 2 ∈ K then 4*t^2 + 2*t - 1 else t^2
  Neg.neg tableValue

/-- PDF p.7, (31)--(32): mu is supported on the EXACT subsets {a} and {a,b}. -/
def clwMu {n : ℕ} (M : Finset (entropyParty n)) : ℝ :=
  if M = {entropyLabelA} then 2*(n : ℝ)^2*((n : ℝ)+1)
  else if M = {entropyLabelA,b} then 2*(n : ℝ)*((n : ℝ)+1)^2 else 0

/-- PDF p.7, (28): the explicitly constructed function f, not an arbitrary polymatroid. -/
def separatingF (n : ℕ) (M : Finset (entropyParty n)) : ℝ :=
  clwTheta n (specialPart M) + (xCount M : ℝ) * clwLambda n (specialPart M) - clwMu M

example (n : ℕ) : separatingF n ∅ = 0 := by
  have hAB : (∅ : Finset (entropyParty n)) ≠ {entropyLabelA, b} :=
    Ne.symm (Finset.insert_ne_empty _ _)
  simp [separatingF, clwTheta, clwLambda, specialPart, xCount, clwMu, hAB]

example (n : ℕ) : clwTheta n ∅ = 0 := by simp [clwTheta]

example (n : ℕ) : clwLambda n ∅ = -(n : ℝ)^2 := by simp [clwLambda]

/-- PDF p.10: the explicit four-party table e, in the same label convention with D=x_1. -/
def oldWitness (M : Finset (entropyParty 1)) : ℝ :=
  if entropyLabelA ∈ M then
    if b ∈ M then
      if c ∈ M then (if x 0 ∈ M then 4 else 6) else 6
    else if c ∈ M then 5 else (if x 0 ∈ M then 5 else 5)
  else if b ∈ M then
    if c ∈ M then 5 else (if x 0 ∈ M then 5 else 5)
  else if c ∈ M then (if x 0 ∈ M then 6 else 2)
  else if x 0 ∈ M then 4 else 0

/-- PDF p.10: old Linden--Winter residual I(C:D)-I(AB:C), with labels fixed. -/
def oldForm : Form (entropyParty 1) := miForm {c} {x 0} - miForm {entropyLabelA,b} {c}

/-- PDF p.10: exactly the three new fixed-label four-party comparison forms. -/
def NewFourParty (L : Form (entropyParty 1)) : Prop :=
  L = primeForm {entropyLabelA} {b} {c} standardX ∨ L = cAsXForm {entropyLabelA} {b} {c} standardX ∨
    L = cAsXPrimeForm {entropyLabelA} {b} {c} standardX

/-- PDF p.10: all three constraints of the old inequality, including I(A:B|D)=0. -/
def oldConstraints : Finset (Form (entropyParty 1)) :=
  insert (cmiForm {entropyLabelA} {b} {x 0}) (constraints 1)

example : oldWitness ∅ = 0 := by simp [oldWitness]

example : oldWitness ({c} : Finset (entropyParty 1)) = 2 := by
  simp [oldWitness, entropyLabelA, b, c, x, Fin.ext_iff]

end QAlgorithms.Papers.Independent.Intake100.P66


