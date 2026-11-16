-- Prove2me | Definitions.Def_SubmodMDP_Policies_Supplement_Algorithm5
-- name    : SubmodMDP_Policies_Supplement_Algorithm5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:28:21.804691+00:00
-- url     : https://prove2.me/theorems/a9168609-c397-4862-a2d3-eda92ef572bf
-- title:
--   Algorithm 5: recursive dynamic program with optional paths
-- statement:
--   Let $G$ be the published layered graph representation. For a block of $d^r$ consecutive layers, start and end subsets $S,T$, and a rational value oracle $f$, Algorithm 5 returns an optional path. At depth zero it compares the singleton paths in $S\cap T$. At positive depth it maintains one best prefix for each boundary vertex, recursively extending prefixes through the next block using the full-prefix marginal
--
--   $$f(X\mid P)=f(X\cup V(P))-f(V(P)).$$
--
--   Missing entries propagate failure, denoted by $\bot$. Updates use strict improvement of the total reward, retaining the previous entry on a tie. Vertex loops use increasing indices. The final loop compares the entries whose endpoints belong to $T$.
--
--   This is the literal recursion of Algorithm 5, with a layer offset representing induced consecutive blocks. It has no optimization primitive and no time-bound field. Lemma 14 asks for a deterministic implementation in the published RAM and proves its runtime as part of the conclusion.
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Algorithm 5 and Lemma 14, p. 24 (PDF p. 25)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Layered
import Definitions.Def_SubmodMDP_Policies_Supplement_Orienteering

namespace SubmodMDP.Policies.Supplement

/-- Strict improvement, with the old entry retained on ties, as in Algorithm 5, line 12. -/
def improve {N : ℕ} (f : Finset (Fin N) → ℚ)
    (old candidate : Option (List (Fin N))) : Option (List (Fin N)) :=
  match old, candidate with
  | none, q => q
  | p, none => p
  | some p, some q => if f p.toFinset < f q.toFinset then some q else some p

/-- Finite maximum by comparisons of oracle values; this is a loop, not an optimization oracle. -/
def best {N : ℕ} (f : Finset (Fin N) → ℚ)
    (L : List (Option (List (Fin N)))) : Option (List (Fin N)) :=
  L.foldl (improve f) none

/-- One DP row, Algorithm 5 lines 8–13. `sub` is the recursive procedure on this block;
its oracle is the marginal with respect to the entire stored acc. -/
def dpRow (G : LGraph) (f : Finset (Fin G.N) → ℚ) (off blk i : ℕ)
    (sub : ℕ → Finset (Fin G.N) → Finset (Fin G.N) →
      (Finset (Fin G.N) → ℚ) → Option (List (Fin G.N)))
    (prev : Fin G.N → Option (List (Fin G.N))) : Fin G.N → Option (List (Fin G.N)) :=
  fun v => if G.layer v = off + i * blk then
    best f ((List.finRange G.N).map (fun u =>
      if G.layer u = off + (i - 1) * blk then
        match prev u with
        | none => none
        | some acc =>
          let S := Finset.univ.filter (fun z => G.arc u z = true ∧
            G.layer z = off + (i - 1) * blk + 1)
          match sub (off + (i - 1) * blk) S {v}
            (fun X => f (X ∪ acc.toFinset) - f acc.toFinset) with
          | none => none
          | some suffix => some (acc ++ suffix)
      else none))
  else none

/-- Algorithm 5 on the consecutive block off+1,…,off+d^r. Every finite maximum is evaluated
by a left-to-right loop over increasing vertex indices. Outside a block no vertex is used.
This definition has no optimal path selector and no assumed cost field. -/
def alg5 (G : LGraph) (d : ℕ) : ℕ → ℕ → Finset (Fin G.N) → Finset (Fin G.N) →
    (Finset (Fin G.N) → ℚ) → Option (List (Fin G.N))
  | 0, off, S, T, f =>
    best f (((List.finRange G.N).filter (fun v =>
      G.layer v = off + 1 ∧ v ∈ S ∧ v ∈ T)).map (fun v => some [v]))
  | h + 1, off, S, T, f =>
    let blk := d ^ h
    let first := fun v => if G.layer v = off + blk then
      alg5 G d h off S {v} f else none
    let last := (List.range (d - 1)).foldl
      (fun prev j => dpRow G f off blk (j + 2) (alg5 G d h) prev) first
    best f (((List.finRange G.N).filter (fun v => v ∈ T)).map last)

/-- Endpoint-restricted layer-spanning path. -/
def STPath (G : LGraph) (S T : Finset (Fin G.N)) (P : List (Fin G.N)) : Prop :=
  IsLSPath G P ∧ (∃ s ∈ S, P.head? = some s) ∧ (∃ t ∈ T, P.getLast? = some t)

/-- Algorithm 5 input uses the published graph format, then d,r and the two endpoint bitmaps. -/
def encDP (G : LGraph) (d r : ℕ) (S T : Finset (Fin G.N)) : List ℤ :=
  encGraph G ++ [(d : ℤ), (r : ℤ)] ++
    (List.finRange G.N).map (fun v => if v ∈ S then 1 else 0) ++
    (List.finRange G.N).map (fun v => if v ∈ T then 1 else 0)

/-- Failure ⊥ is encoded as [-1]; a successful path has the encWalk format. -/
def encOptionalWalk {n : ℕ} : Option (List (Fin n)) → List ℤ
  | none => [-1]
  | some P => encWalk P

end SubmodMDP.Policies.Supplement


