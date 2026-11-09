-- Prove2me | Definitions.Def_QuadraticProbe717_Insertion_probing
-- name    : QuadraticProbe717_Insertion_probing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:33.093932+00:00
-- url     : https://prove2.me/theorems/47f18127-3f40-4c34-9bb2-657eafae33eb
-- title:
--   First-empty probing and the quadratic insertion process
-- statement:
--   Let $n>0$ and identify the slots with $\mathbb Z/n\mathbb Z$. For an occupied set $A$ and any finite probe list, insert into its first entry outside $A$; if none exists, leave $A$ unchanged. Applying this rule successively defines the occupied set from a list of hashes.
--
--   For quadratic probing, let $\pi$ be a permutation of the offsets, fixed before any randomness is sampled. The probe list is
--   $$
--   0^2,1^2,\ldots,(n-1)^2,\quad\text{then the offsets of }\pi\text{ that did not occur among those squares}.
--   $$
--   Translate the whole list by the hash. The cost is the index of the first vacant entry plus one, counting repeated entries. A full table has cost $2n$, and insertions into it are no-ops. For $m+1$ hashes, $T_m$ is the next insertion cost after applying the first $m$ hashes to the empty table; $\varepsilon=1-m/n$.
--
--   This interface separates the general first-empty operation from the paper's specific offset sequence. Key identities are represented by insertion times, since distinct keys have independent hashes and no other effect on occupancy.
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Section 2 and footnote 4; Lemma 2.4, p. 5, p. 4 (PDF p. 4)

import Mathlib

set_option autoImplicit false

namespace QuadraticProbe717.Insertion

/-- First-empty insertion for an arbitrary finite probe list. Full or exhausted lists are no-ops. -/
def insertAlong {α : Type*} [DecidableEq α] (A : Finset α) (probes : List α) : Finset α :=
  match probes.find? (fun x => decide (x ∉ A)) with
  | none => A
  | some x => insert x A

/-- The occupied set after a prefix of a common list of future probe sequences. -/
def runFrom {α : Type*} [DecidableEq α] (A : Finset α)
    (sequences : List (List α)) (t : ℕ) : Finset α :=
  (sequences.take t).foldl insertAlong A

/-- Repeated square offsets, followed by previously unprobed offsets in a fixed permutation. -/
def probeOffsets (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) : List (ZMod n) :=
  let squares := (List.range n).map (fun i => (i : ZMod n) ^ 2)
  squares ++ ((List.ofFn (fun i : Fin n => π (i.val : ZMod n))).filter
    (fun x => decide (x ∉ squares)))

def probeList (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) (h : ZMod n) : List (ZMod n) :=
  (probeOffsets n π).map (h + ·)

/-- Cost counts list entries, including repeated probes. Full tables have prescribed cost 2n. -/
def insertionCost (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (A : Finset (ZMod n)) (h : ZMod n) : ℕ :=
  if A = Finset.univ then 2 * n
  else (probeList n π h).findIdx (fun x => decide (x ∉ A)) + 1

def occupied (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (hashes : List (ZMod n)) : Finset (ZMod n) :=
  hashes.foldl (fun A h => insertAlong A (probeList n π h)) ∅

/-- The sample contains the first m hashes and an independent next-key hash. -/
def fixedTime (n m : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (hashes : Fin (m + 1) → ZMod n) : ℕ :=
  insertionCost n π (occupied n π ((List.ofFn hashes).take m)) (hashes (Fin.last m))

noncomputable def vacancyFraction (n m : ℕ) : ℝ := 1 - (m : ℝ) / n

end QuadraticProbe717.Insertion


