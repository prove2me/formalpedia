-- Prove2me | Definitions.Def_DirKECC1549_Impl_SccBfs
-- name    : DirKECC1549_Impl_SccBfs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-16T06:02:35.788195+00:00
-- url     : https://prove2.me/theorems/e36d3d8e-b2f6-4004-abac-464a41d5db73
-- title:
--   Kosaraju's algorithm: the reverse searches
-- statement:
--   The in-edge block start `its`, the reverse search state `BState`, its scanned-prefix predicate `BPart` and the labelling state `LState` (labels of a set closed under strong connectivity, one label per component).
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

/-- `#{e : head e < v}`: the start of the in-edges of `v` in the head-sorted order. -/
def its (D : Fin m → Fin n × Fin n) (v : ℕ) : ℕ := (univ.filter (fun e => ((D e).2 : ℕ) < v)).card

/-- The state of the reverse search of one round: the queue `q` (all labelled), of which the first
`h` are processed (all their in-neighbours are assigned or queued), over the vertices outside the
assigned set `A`. -/
structure BState (D : Fin m → Fin n × Fin n) (A : Finset (Fin n)) (v : Fin n) (q : List (Fin n))
    (h : ℕ) : Prop where
  nd : q.Nodup
  hd : q ≠ [] ∧ q.head? = some v
  disj : ∀ u ∈ q, u ∉ A
  reach : ∀ u ∈ q, Reach D u v
  hle : h ≤ q.length
  closed : ∀ i (hi : i < h), ∀ e : Fin m, (D e).2 = q[i]'(by omega) → (D e).1 ∈ A ∨ (D e).1 ∈ q

/-- Scanning the in-edges of `x = q[h]`: positions `[its x, j)` done. -/
def BPart (D : Fin m → Fin n × Fin n) (τ : Equiv.Perm (Fin m)) (A : Finset (Fin n))
    (q : List (Fin n)) (x : Fin n) (j : ℕ) : Prop :=
  ∀ j' : Fin m, its D x ≤ j' → (j' : ℕ) < j → (D (τ j')).1 ∈ A ∨ (D (τ j')).1 ∈ q

/-- The labels of the assigned vertices `A` after some rounds: `A` is a union of strong components,
labels are equal exactly on strongly connected pairs, and `c` labels are in use. -/
structure LState (D : Fin m → Fin n × Fin n) (A : Finset (Fin n)) (lab : Fin n → ℕ) (c : ℕ) :
    Prop where
  closed : ∀ a b, StronglyConn D a b → a ∈ A → b ∈ A
  iff : ∀ a ∈ A, ∀ b ∈ A, lab a = lab b ↔ StronglyConn D a b
  lt : ∀ a ∈ A, lab a < c
  used : ∀ j < c, ∃ a ∈ A, lab a = j
  card : c ≤ A.card

end DirKECC1549.Asm


