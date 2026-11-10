-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_Witness
-- name    : StudentTeacher976_Adaptivity_Witness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:11:47.661808+00:00
-- url     : https://prove2.me/theorems/823c1b43-87c8-49ed-8380-f4f76c86ad0f
-- title:
--   Bounded witnesses, auxiliary tuple search, and operational normalization
-- statement:
--   Fix a language $L$ with a bounded existential presentation by a predicate $\varphi\in\Delta_{i+1}^p$ and a polynomial witness length $a$:
--
--   $$
--   x\in L\ \Longleftrightarrow\ \exists y\in\{0,1\}^{a(|x|)}\;\varphi(x,y).
--   $$
--
--   Write $U=\{x:|x|=n\ \text{and}\ x\in L\}$. On a tuple $X=(x_1,\ldots,x_k)$, the auxiliary relation asks for a tuple $Y$ of witnesses for every positive coordinate; negative coordinates impose no witness-validity requirement. Its refutation predicate tests, at a selected coordinate $j$,
--
--   $$
--   \varphi(x_j,z_j)\ \Longrightarrow\ \varphi(x_j,y_j).
--   $$
--
--   Candidate and refutation tuples have explicit lengths. A tuple student is realized by one finite polynomial-time oracle transducer. Its success is the full universal-history disjunction with the specified round and parallel-query counts.
--
--   Operational normalization replaces each coordinate by the first valid witness available among previous reply tuples and the current batch, if any; otherwise it retains the original guess. Thus witnesses can be combined across parallel candidates. The operation does not assume success or bound the number of replies. These definitions give the precise language, relation, and normalized-student context of Claim 3.1. Exact witness lengths are a padding representation of bounded witnesses.
-- source:
--   Ondřej Ježil, Dimitrios Tsintsilidas, STOC 2027 submission #976 (October 2026), §3.1, displayed sentence Φ and relation R, p.19 (PDF p.19); normalization preamble, p.20 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Game

open QAdvFew.PoQOracle

namespace StudentTeacher976.Adaptivity

/-- A bounded existential Δᵖᵢ₊₁ presentation of the language L, as in §3.1 p.19.
Witnesses have one exact polynomial length by padding; no hardness is included.
The standard Σᵖᵢ₊₁ representation bridge is proof work, not a hypothesis of the goal. -/
structure WitnessPresentation (i : ℕ) (L : Language) where
  length : Polynomial ℕ
  test : Word → Word → Prop
  efficient : {s | ∃ x y, s = tup [x, y] ∧ test x y} ∈ Delta i
  represents : ∀ x, x ∈ L ↔ ∃ y, y.length = length.eval x.length ∧ test x y

/-- The bounded witness predicate φ from §3.1. -/
def ValidWitness {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (x y : Word) : Prop := y.length = W.length.eval x.length ∧ W.test x y

/-- U is exactly the positive n-bit instances, including n=0. §3.1 p.20. -/
def positiveInputs {i : ℕ} {L : Language} (W : WitnessPresentation i L) (n : ℕ) : Set Word :=
  {x | x.length = n ∧ ∃ y, ValidWitness W x y}

/-- Full auxiliary refutations (index, witness tuple). The fixed teacher later uses
one witness and fixed zero fillers, but students must win against every legal refutation. -/
abbrev TupleReply := ℕ × List Word
abbrev TupleStudent := List Word → ℕ → List (List TupleReply) → List (List Word)

/-- Legal tuples, including empty tuples when k=0. -/
def TupleShape (n k : ℕ) (X : List Word) : Prop :=
  X.length = k ∧ ∀ x ∈ X, x.length = n

/-- Auxiliary search relation: supply a witness for every positive coordinate, without
requiring any witness for negative coordinates. §3.1 p.19, the displayed sentence Φ. -/
def TupleRelation {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (X Y : List Word) : Prop :=
  Y.length = X.length ∧ (∀ j < X.length,
    (Y.getD j []).length = W.length.eval (X.getD j []).length) ∧
  ∀ j < X.length, (∃ z, ValidWitness W (X.getD j []) z) →
    ValidWitness W (X.getD j []) (Y.getD j [])

/-- Legal refutations have an in-range index and a full tuple of exact-length strings. -/
def ReplyShape {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (n k : ℕ) (z : TupleReply) : Prop :=
  z.1 < k ∧ TupleShape (W.length.eval n) k z.2

/-- All prior batches, with q replies in each batch. -/
def TupleHistoryShape {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (n k q t : ℕ) (H : List (List TupleReply)) : Prop :=
  H.length = t ∧ ∀ B ∈ H, B.length = q ∧ ∀ z ∈ B, ReplyShape W n k z

/-- The refutable predicate φ′(x_j,y_j,z_j) = (φ(x_j,z_j) → φ(x_j,y_j)),
with explicit output shape. Out-of-range indices give a vacuous implication;
legal histories also enforce every refutation-tuple length. Malformed candidate tuples
fail the shape clauses. §3.1 p.19. -/
def TupleTest {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (X Y : List Word) (z : TupleReply) : Prop :=
  Y.length = X.length ∧ (∀ j < X.length,
    (Y.getD j []).length = W.length.eval (X.getD j []).length) ∧
  (z.1 < X.length →
    ValidWitness W (X.getD z.1 []) (z.2.getD z.1 []) →
    ValidWitness W (X.getD z.1 []) (Y.getD z.1 []))

/-- Refutation serialization; indices are unary. Tuple delimiters affect the machine's
running time, never the raw block input length m=n*k or its resource count. -/
def encodeReply (z : TupleReply) : Word :=
  tup [List.replicate z.1 true, tup z.2]

/-- One uniform oracle transducer for all structured inputs. No per-length machine. -/
def UniformTupleStudent (i : ℕ) (f : TupleStudent) : Prop :=
  ∃ F : Word → Word, InFP i F ∧ ∀ X t H,
    F (tup [tup X, List.replicate (t + 1) true,
      tup (H.map fun B => tup (B.map encodeReply))]) = tup ((f X t H).map tup)

/-- A k-round, q-query tuple student's permitted outputs on every legal history.
The exact witness lengths make the original polynomial answer bound explicit. -/
def TupleStudentShape {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (n k q : ℕ) (f : TupleStudent) : Prop :=
  (∀ X t H, TupleShape n k X → t < k → TupleHistoryShape W n k q t H →
    (f X t H).length = q ∧ ∀ Y ∈ f X t H, TupleShape (W.length.eval n) k Y) ∧
  ∀ X t H, TupleShape n k X → k ≤ t → f X t H = []

/-- Actual normalization: for each coordinate, take the first valid witness among
previous reply tuples and the current simultaneous guesses, if one exists; otherwise
keep the original guess. Verification uses the same Δ predicate. No success or bound
on the number of teacher replies is built into normalization. §3.1 p.20. -/
noncomputable def normalize {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (f : TupleStudent) : TupleStudent := by
  classical
  exact fun X t H =>
    let guesses := f X t H
    guesses.map fun Y => Y.mapIdx fun j y =>
      let pool := (H.flatten.map fun z => z.2.getD j []) ++
        (guesses.map fun Z => Z.getD j [])
      (pool.find? fun w => decide (ValidWitness W (X.getD j []) w)).getD y

/-- The source lower-round solvability assumption, expressed as the full universal-history
disjunction, not as a promise about the particular fixed-teacher execution. -/
def TupleStudentWins {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (n k q : ℕ) (f : TupleStudent) : Prop :=
  ∀ X H, TupleShape n k X → TupleHistoryShape W n k q k H →
    ∃ t, t < k ∧ ∃ j, j < q ∧
      TupleTest W X ((f X t (H.take t)).getD j []) ((H.getD t []).getD j (0, []))

end StudentTeacher976.Adaptivity


