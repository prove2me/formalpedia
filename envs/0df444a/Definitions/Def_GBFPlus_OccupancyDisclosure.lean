-- Prove2me | Definitions.Def_GBFPlus_OccupancyDisclosure
-- name    : GBFPlus_OccupancyDisclosure
-- status  : Definition
-- author  : @queelius
-- created : 2026-10-23T18:32:01.844407+00:00
-- url     : https://prove2.me/theorems/ee573e02-5b12-44ad-b2db-bf7c006126e2
-- title:
--   GBFPlus occupied cells, residual updates and honest histories
-- statement:
--   A configuration has $m$ cells, $1\le\kappa\le m$ selected cells per insertion, positive prefix width $p$ and positive suffix width $\ell$; the full word width is $\lambda=p+\ell$, so $0<\ell<\lambda$. Words are pairs of bit-coordinate vectors over $\mathbb Z/2\mathbb Z$, with addition equal to XOR. Concatenation places the prefix coordinates first and suffix coordinates last. A snapshot maps each cell to either empty or an occupied word; an occupied zero remains occupied.
--
--   A row has a set of exactly $\kappa$ distinct cells, an arbitrary prefix and an adjacent-domain identifier. An attempted insertion specifies the row, either an empty selected pivot or a request for failure, and arbitrary words for free cells. On success, previously occupied words are reused, other empty selected cells receive their free words, and the pivot receives the target word XOR the other selected words. Cells outside the selected set are unchanged. A failure request is admissible only when all selected cells are occupied and leaves the state unchanged.
--
--   An honest history starts from an empty array and consists of admissible attempts evaluated in order. The successful rows, in order, are derived from those attempts, including no failed attempts. Public recovery XORs exactly the occupied cells and returns the suffix. Its inputs are the snapshot and public configuration; it receives no row, prefix, identifier, history, secret or token. The model imposes no distribution on free words and does not model ledger access, authentication or timeout policy; those remain premises of the source's disclosure interpretation.
-- source:
--   Alexander Richard Towell, Adjacent-Domain Disclosure from Public Occupancy in GBFPlus, archival preprint v1.0.0, 20 October 2026, Section 2, DOI 10.5281/zenodo.23497466. Original analyzed protocol: Qin, Zhou, Dai, Sun and Qiang, Entropy 28 (2026), 947, DOI 10.3390/e28090947, Algorithm 4 and Sections 5.1–5.2. The source note is CC-BY-4.0; this new Lean formalization retains attribution and is prepared for the platform public-contribution terms. Definition layer: construction preceding Eq.(1), Propositions 1–2, and source-premises supplement.

import Mathlib

namespace GBFPlus.OccupancyDisclosure

structure Config where
  cells : ℕ
  shares : ℕ
  prefixBits : ℕ
  suffixBits : ℕ
  shares_pos : 1 ≤ shares
  shares_le : shares ≤ cells
  prefix_pos : 1 ≤ prefixBits
  suffix_pos : 1 ≤ suffixBits

abbrev Word (C : Config) :=
  (Fin C.prefixBits → ZMod 2) × (Fin C.suffixBits → ZMod 2)
abbrev Identifier (C : Config) := Fin C.suffixBits → ZMod 2
abbrev Snapshot (C : Config) := Fin C.cells → Option (Word C)

def wordBits {C : Config} (w : Word C) : Fin (C.prefixBits + C.suffixBits) → ZMod 2 :=
  Fin.addCases w.1 w.2

def empty (C : Config) : Snapshot C := fun _ => none

structure Row (C : Config) where
  support : Finset (Fin C.cells)
  support_card : support.card = C.shares
  hashPrefix : Fin C.prefixBits → ZMod 2
  identifier : Identifier C

def Row.target {C : Config} (r : Row C) : Word C := (r.hashPrefix, r.identifier)

structure Attempt (C : Config) where
  row : Row C
  pivot : Option (Fin C.cells)
  free : Fin C.cells → Word C

def admissible {C : Config} (A : Snapshot C) (e : Attempt C) : Prop :=
  match e.pivot with
  | none => ∀ i ∈ e.row.support, A i ≠ none
  | some p => p ∈ e.row.support ∧ A p = none

instance {C : Config} (A : Snapshot C) : (e : Attempt C) → Decidable (admissible A e)
  | ⟨r, none, _⟩ => inferInstanceAs (Decidable (∀ i ∈ r.support, A i ≠ none))
  | ⟨r, some p, _⟩ => inferInstanceAs (Decidable (p ∈ r.support ∧ A p = none))

def fillWord {C : Config} (A : Snapshot C) (free : Fin C.cells → Word C)
    (i : Fin C.cells) : Word C := (A i).getD (free i)

def insert {C : Config} (A : Snapshot C) (r : Row C) (p : Fin C.cells)
    (free : Fin C.cells → Word C) : Snapshot C := fun i =>
  if i ∈ r.support then
    some (if i = p then r.target + ∑ j ∈ r.support.erase p, fillWord A free j
      else fillWord A free i)
  else A i

def step {C : Config} (A : Snapshot C) (e : Attempt C) : Snapshot C :=
  match e.pivot with
  | none => A
  | some p => insert A e.row p e.free

def run {C : Config} (A : Snapshot C) : List (Attempt C) → Snapshot C
  | [] => A
  | e :: es => run (step A e) es

def Honest {C : Config} (A : Snapshot C) : List (Attempt C) → Prop
  | [] => True
  | e :: es => admissible A e ∧ Honest (step A e) es

def honestDecidable {C : Config} : (A : Snapshot C) → (es : List (Attempt C)) → Decidable (Honest A es)
  | _, [] => isTrue trivial
  | A, e :: es => @instDecidableAnd (admissible A e) (Honest (step A e) es)
      inferInstance (honestDecidable (step A e) es)

instance {C : Config} (A : Snapshot C) (es : List (Attempt C)) : Decidable (Honest A es) := honestDecidable A es

def successful {C : Config} (es : List (Attempt C)) : List (Row C) :=
  es.filterMap fun e => e.pivot.map fun _ => e.row

def finalSnapshot {C : Config} (es : List (Attempt C)) : Snapshot C := run (empty C) es

def occupied {C : Config} (A : Snapshot C) : Finset (Fin C.cells) :=
  Finset.univ.filter fun i => (A i).isSome

def payload {C : Config} (A : Snapshot C) (i : Fin C.cells) : Word C := (A i).getD 0

def rowXor {C : Config} (A : Snapshot C) (r : Row C) : Word C :=
  ∑ i ∈ r.support, payload A i

def recover {C : Config} (A : Snapshot C) : Identifier C :=
  (∑ i ∈ occupied A, payload A i).2

def supportUnion {C : Config} (rs : List (Row C)) : Finset (Fin C.cells) :=
  rs.foldl (fun U r => U ∪ r.support) ∅

def identifierXor {C : Config} (rs : List (Row C)) : Identifier C :=
  (rs.map Row.identifier).sum

end GBFPlus.OccupancyDisclosure


