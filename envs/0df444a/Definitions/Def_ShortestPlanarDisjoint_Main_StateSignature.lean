-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_StateSignature
-- name    : ShortestPlanarDisjoint_Main_StateSignature
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:56.764753+00:00
-- url     : https://prove2.me/theorems/de221b87-6e73-41b4-89c5-6215c40525f0
-- title:
--   Glued disk components, leading exponents and block substitution
-- statement:
--   Fix a disk layout, a budget and a return-free noncrossing matching D. Each seam pairs its two endpoint lists either in equal or reversed boundary order. Alternating the matching with these fixed identifications extracts every terminal path and one traversal of every closed component. A bound exceeding the endpoint count stops the finite traversal; canonical representatives prevent orientation or starting-point multiplicities. The signature is the actual product of path brackets and cycle traces in the characteristic-two Laurent algebra.
--
--   Its proposed top exponent records q_s in each seam variable, the side-opening counts in side variables and a terminal exponent one exactly at opening terminals. A leading-exponent predicate requires a nonzero coefficient and absence of any larger supported exponent, in the stated seam-first lexicographic order. Leading-term claims are not assumed.
--
--   A cap joins two terminals of one block. Surviving states have no cap in an inactive block. Substitution identifies all terminal variables of such a block with its first terminal variable, used as the independent name x_j. Exponents of identified variables are added. Empty blocks make no substitution. Both boundary-order identifications are available, including the planar reversed convention.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Sections 5.1–5.2 and 5.6, p. 18 (PDF p. 20)

import Definitions.Def_ShortestPlanarDisjoint_Main_DiskState
import Definitions.Def_ShortestPlanarDisjoint_Main_SignatureAlgebra

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
noncomputable section

/-- false reverses boundary order (the planar convention); true preserves it. -/
def glueEndpoint {k r : ℕ} {q : Fin r → ℕ} (sameOrder : Fin r → Bool) :
    DiskEndpoint k r q → DiskEndpoint k r q
  | .inl i => .inl i
  | .inr ⟨s, e, j⟩ => .inr ⟨s, !e,
      if sameOrder s then j else ⟨q s - 1 - j.val, by omega⟩⟩

namespace DiskState
variable {k f r b : ℕ} {L : DiskLayout k f r}

/-- Follow a strand, then its seam identification. Stop at a terminal or on
return to the starting endpoint. The fuel is larger than the endpoint set. -/
def follow (D : DiskState L b) (sameOrder : Fin r → Bool)
    (start : DiskEndpoint k r D.q) :
    ℕ → DiskEndpoint k r D.q → List (Fin r × Bool) × Option (Fin (2 * k))
  | 0, _ => ([], none)
  | t + 1, current =>
    match D.mate current with
    | .inl i => ([], some i)
    | .inr ⟨s, e, j⟩ =>
      let next := glueEndpoint sameOrder (.inr ⟨s, e, j⟩ : DiskEndpoint k r D.q)
      if next = start then ([(s, e)], none)
      else let result := D.follow sameOrder start t next
           ((s,e) :: result.1, result.2)

def traceFrom (D : DiskState L b) (sameOrder : Fin r → Bool)
    (p : DiskEndpoint k r D.q) :=
  D.follow sameOrder p (2 * k + 2 * ∑ s, D.q s + 1) p

/-- Connectedness under strand matching and seam identification, including both
traversal directions; this selects one representative per closed component. -/
def Connected (D : DiskState L b) (sameOrder : Fin r → Bool)
    (p u : DiskEndpoint k r D.q) : Prop :=
  Relation.ReflTransGen (fun x y => D.mate x = y ∨ glueEndpoint sameOrder x = y) p u

def cycleRepresentatives (D : DiskState L b) (sameOrder : Fin r → Bool) :
    List (DiskEndpoint k r D.q) := by
  classical
  exact (L.endpoints D.q).filter fun p =>
    (∀ i, ¬ D.Connected sameOrder p (.inl i)) ∧
    ∀ u, D.Connected sameOrder p u → L.rank p ≤ L.rank u

/-- These are extracted component words, rather than independent supplied data. -/
def words (D : DiskState L b) (sameOrder : Fin r → Bool) : CurveWords k r := by
  classical
  exact {
    paths := (List.finRange (2 * k)).filterMap fun i =>
      let result := D.traceFrom sameOrder (.inl i)
      match result.2 with
      | none => none
      | some j => if i < j then some (i, j, result.1) else none
    cycles := (D.cycleRepresentatives sameOrder).map fun p => (D.traceFrom sameOrder p).1 }

def signature (D : DiskState L b) (sameOrder : Fin r → Bool) : SignatureRing k r :=
  curveSignature (D.words sameOrder)

/-- Exponent vector in equation (6), computed from the state alone. -/
def topExponent (D : DiskState L b) : SignatureVariable k r → ℤ
  | .inl s => D.q s
  | .inr (.inl i) => if D.Opens (.inl i) then 1 else 0
  | .inr (.inr (s,e)) => D.sideOpenCount s e

end DiskState

/-- Exactly the lexicographic priority in §5.2: all seams, then boundary variables. -/
def DiskLayout.variableOrder {k f r : ℕ} (L : DiskLayout k f r) :
    List (SignatureVariable k r) :=
  (List.finRange r).map Sum.inl ++ L.sideOrder.flatMap (fun side => match side with
    | .inl j => (L.block j).map fun i => .inr (.inl i)
    | .inr (s,e) => [.inr (.inr (s,e))])

def ExponentLexLT {α : Type*} (order : List α) (a b : α → ℤ) : Prop :=
  ∃ before x after, order = before ++ x :: after ∧
    (∀ y ∈ before, a y = b y) ∧ a x < b x

/-- A leading exponent is used only with a nonzero polynomial, explicitly in each
statement. No extremum of an empty or unbounded real set is involved. -/
def IsLeadingExponent {k f r : ℕ} (L : DiskLayout k f r)
    (p : SignatureRing k r) (a : SignatureVariable k r → ℤ) : Prop :=
  p.coeff a ≠ 0 ∧ ∀ c, p.coeff c ≠ 0 → ¬ ExponentLexLT L.variableOrder a c

/-- A cap is a matching edge between two terminals of the same boundary block. -/
def DiskState.HasCap {k f r b : ℕ} {L : DiskLayout k f r}
    (D : DiskState L b) (j : Fin f) : Prop :=
  ∃ i ∈ L.block j, ∃ u ∈ L.block j, D.mate (.inl i) = .inl u

def DiskState.Survives {k f r b : ℕ} {L : DiskLayout k f r}
    (D : DiskState L b) (active : Fin f → Bool) : Prop :=
  ∀ j, active j = false → ¬ D.HasCap j

/-- Inactive terminal variables become the first terminal variable of their block.
This uses existing independent Laurent variables as the x_j, including empty
blocks which have no variables to substitute. Seam and side variables are fixed. -/
def substitutedVariable {k f r : ℕ} (L : DiskLayout k f r) (active : Fin f → Bool)
    (x : SignatureVariable k r) : SignatureVariable k r := by
  classical
  exact match x with
  | .inl s => .inl s
  | .inr (.inr e) => .inr (.inr e)
  | .inr (.inl i) =>
    let block := (List.finRange f).find? (fun j => i ∈ L.block j)
    match block with
    | none => x
    | some j => if active j then x else .inr (.inl ((L.block j).headD i))

/-- Laurent substitution sums exponents at identified variables. -/
def substitutedExponent {k f r : ℕ} (L : DiskLayout k f r) (active : Fin f → Bool)
    (a : SignatureVariable k r → ℤ) : SignatureVariable k r → ℤ :=
  fun y => ∑ x, if substitutedVariable L active x = y then a x else 0

def substituteSignature {k f r : ℕ} (L : DiskLayout k f r) (active : Fin f → Bool)
    (p : SignatureRing k r) : SignatureRing k r :=
  p.coeff.sum fun a c => AddMonoidAlgebra.single (substitutedExponent L active a) c

end
end ShortestPlanarDisjoint.Main


