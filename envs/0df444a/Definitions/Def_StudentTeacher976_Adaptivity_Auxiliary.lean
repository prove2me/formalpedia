-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary
-- name    : StudentTeacher976_Adaptivity_Auxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-17T23:29:34.967571+00:00
-- url     : https://prove2.me/theorems/d5d6238d-3bd8-4043-87ce-7597ed87f748
-- title:
--   Canonical raw certificates and witness-retaining upper student
-- statement:
--   The raw auxiliary relation is tested using a padded certificate of length
--
--   $$
--   m+p(m),
--   $$
--
--   where $m$ is the original input length and $p$ is the witness-length polynomial. The first $m$ bits encode a coordinate in unary; the remaining bits contain a witness, truncated to that coordinate's exact witness length. Candidate tuples are parsed with the published self-delimiting tuple code. Malformed candidate encodings fail, while an out-of-range certificate coordinate gives a vacuous implication.
--
--   The upper student makes one query per round, retaining every valid coordinate witness found in previous replies and filling other coordinates by zero strings. It rejects at the exact $r(m)+1$ budget. At raw lengths without block decoding it proposes the unique easy answer.
--
--   These are the concrete predicate and student used to implement the construction on p.19. Their efficiency, representation, output shape, and winning properties remain separate proof obligations.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), §3.1 p.19, upper-round witness retention construction; Definitions 1.1–1.2 pp.6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_InputConversion

open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

/-- Read one component in the published tuple code; malformed pairs fail. -/
def readComponent : Word → Option (Word × Word)
  | false :: false :: rest => some ([], rest)
  | true :: b :: rest => (readComponent rest).map fun p => (b :: p.1, p.2)
  | _ => none

/-- Bounded structural parser for a tuple. -/
def decodeTupleFuel : ℕ → Word → Option (List Word)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, s@(_ :: _) => (readComponent s).bind fun p =>
      (decodeTupleFuel fuel p.2).map (p.1 :: ·)

/-- A tuple contains at most as many components as encoded bits. -/
def decodeTuple (s : Word) : Option (List Word) := decodeTupleFuel s.length s

/-- A bounded raw certificate gives a unary coordinate index and a padded witness. -/
def rawIndex (x z : Word) : ℕ := ((z.take x.length).takeWhile id).length

def rawWitness {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (x a z : Word) : Word := (z.drop x.length).take (W.length.eval a.length)

/-- Canonical refutable predicate for the raw auxiliary relation. -/
def auxiliaryTest {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x y z : Word) : Prop :=
  match blockInput r x with
  | none => y = []
  | some X => match decodeTuple y with
    | none => False
    | some Y =>
      Y.length = X.length ∧
      (∀ j < X.length, (Y.getD j []).length = W.length.eval (X.getD j []).length) ∧
      (rawIndex x z < X.length →
        ValidWitness W (X.getD (rawIndex x z) [])
          (rawWitness W x (X.getD (rawIndex x z) []) z) →
        ValidWitness W (X.getD (rawIndex x z) []) (Y.getD (rawIndex x z) []))

/-- Preserve every valid witness seen in a previous raw refutation. -/
noncomputable def auxiliaryCandidate {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (x : Word) (X : List Word) (H : List (List Word)) : List Word := by
  classical
  exact X.map fun a =>
    ((H.flatten.map fun z => rawWitness W x a z).find? fun w => decide (ValidWitness W a w)).getD
      (List.replicate (W.length.eval a.length) false)

/-- A single-query student with the exact upper-round budget and terminal rejection. -/
noncomputable def auxiliaryStudent {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) : Student := fun x t H =>
  if t < resource (fun m => r m + 1) x.length then
    [match blockInput r x with
      | none => []
      | some X => tup (auxiliaryCandidate W x X H)]
  else []

end StudentTeacher976.Adaptivity


