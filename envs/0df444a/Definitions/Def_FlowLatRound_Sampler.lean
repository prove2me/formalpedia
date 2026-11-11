-- Prove2me | Definitions.Def_FlowLatRound_Sampler
-- name    : FlowLatRound_Sampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:58:59.89413+00:00
-- url     : https://prove2.me/theorems/358a451b-4696-4fa2-bfb4-ee7aa3806599
-- title:
--   Lemma C.6 and Theorem 1.1 — the exact sampler of (P1)–(P3) and the basis sampler
-- statement:
--   `sampleProcess` simulates (P1)–(P3) on fair bits: (P1) draw $n-2$ distinct slots, each uniform among the remaining ones, and decode their vertex labels as a Prüfer code; (P2) attach each tree edge at each vertex to a uniform unused half-edge; (P3) repeatedly pair the least unmatched residual half-edge with a uniform other one. It outputs the pairing and the planted tree $T$.
--
--   `sampleBasis d` runs it with the $4$-regular sequence on $n=d-1$ vertices and outputs $\pi$ with the fundamental-cycle matrix $C_T$ of $G(\pi)$ (a basis of $\Lambda_{G(\pi)}$), as in the proof of Theorem 1.1 (p.9).
--
--   **Formalization Note** Every uniform choice is made by rejection sampling from fair bits; the order of the draws is fixed as above.
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma C.6, p.26 (PDF 28); slots and Prüfer codes, p.9 (PDF 11); proof of Theorem 1.1, p.9 (PDF 11)

import Mathlib
import Definitions.Def_FlowLatRound_TiltedModel
import Definitions.Def_FlowLatRound_FundCycles

namespace FlowLatRound

/-! # The exact sampler of Lemma C.6 and the basis sampler of Theorem 1.1

Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027
submission, sha256 35bd3e4b…aeac), §3.4 (P1)–(P3), p.8 (PDF 10); slots and Prüfer codes, p.9
(PDF 11) and Appendix C.4, p.26 (PDF 28); Lemma C.6, p.26; proof of Theorem 1.1, p.9 ("The
fundamental cycles of T give a basis of Λ_G, the pair (π, T) is sampled exactly in expected
polynomial time (Lemma C.6)"); computational model, Appendix B, pp.18–19.

**Formalization Note.** `sampleProcess g` is the program of Lemma C.6, in this order:
1. (P1) draw `n − 2` distinct slots, each uniform among the slots not drawn yet (vertex `i` has
   `aᵢ = gᵢ − 1` slots, listed vertex by vertex), and decode their vertex labels as a Prüfer code;
2. (P2) for each vertex `i = 0, 1, …` and each tree edge at `i` (in the decoder's order), attach
   it to a uniform half-edge of `i` not used yet;
3. (P3) repeatedly pair the least unmatched residual half-edge with a uniform other one;
4. output the pairing (as a map on half-edges) and the set `T` of edges of `G(π)` carrying tree
   edges.
Every uniform choice is `uniformBelow` (rejection sampling from fair bits, at most `fuel`
retries). `sampleBasis d` runs it with the `4`-regular sequence on `n = d − 1` vertices, writes
`G(π)` into arrays, and computes the fundamental-cycle matrix `C_T` (`fundMatrixC`), reindexed to
`d` columns (`m + 1 − n = d` for `d ≥ 1`). Evaluations of the list-backed pairing map are charged
by the length of the scan. -/

namespace DegSeq

variable {n : ℕ} (g : DegSeq n)

/-- All slots, vertex by vertex. -/
def slotList : List g.Slot :=
  (List.finRange n).flatMap (fun i => (List.finRange (g.a i)).map (fun j => ⟨i, j⟩))

/-- All half-edges in increasing order (`finSigmaFinEquiv`). -/
def heList : List g.HalfEdge := (List.finRange (∑ i, g.g i)).map finSigmaFinEquiv.symm

/-- (P1): `k` draws of distinct slots, each uniform among the remaining ones `avail`. -/
def drawSlots (fuel : ℕ) : ℕ → List g.Slot → RProg (List g.Slot)
  | 0, _ => pure []
  | k + 1, avail => do
      let r ← uniformBelow fuel avail.length
      rcharge (2 * avail.length + 1)
      match avail[r]? with
      | some s => do
          let rest ← drawSlots fuel k (avail.erase s)
          pure (s :: rest)
      | none => outOfFuel

/-- (P2) at vertex `i`: attach the tree edges with indices `ks` to distinct uniform half-edges
of `i` among `avail`; returns (tree-edge index, half-edge) pairs. -/
def attachAt (fuel : ℕ) (i : Fin n) : List ℕ → List (Fin (g.g i)) → RProg (List (ℕ × g.HalfEdge))
  | [], _ => pure []
  | k :: ks, avail => do
      let r ← uniformBelow fuel avail.length
      rcharge (2 * avail.length + 1)
      match avail[r]? with
      | some h => do
          let rest ← attachAt fuel i ks (avail.erase h)
          pure ((k, ⟨i, h⟩) :: rest)
      | none => outOfFuel

/-- (P3): a uniform perfect matching of `rest`, pairing the least half-edge with a uniform other
one, at most `k` rounds. -/
def matchResid (fuel : ℕ) : ℕ → List g.HalfEdge → RProg (List (g.HalfEdge × g.HalfEdge))
  | 0, _ => pure []
  | _ + 1, [] => pure []
  | k + 1, h :: rest => do
      let r ← uniformBelow fuel rest.length
      rcharge (2 * rest.length + 1)
      match rest[r]? with
      | some h' => do
          let more ← matchResid fuel k (rest.erase h')
          pure ((h, h') :: more)
      | none => outOfFuel

/-- The map on half-edges given by a list of pairs (identity off the pairs). -/
def pairFun (ps : List (g.HalfEdge × g.HalfEdge)) (h : g.HalfEdge) : g.HalfEdge :=
  match ps.find? (fun p => decide (p.1 = h) || decide (p.2 = h)) with
  | some p => if p.1 = h then p.2 else p.1
  | none => h

/-- The program of Lemma C.6: simulate (P1)–(P3) and output `(π, T)`. -/
def sampleProcess (fuel : ℕ) : RProg ((g.HalfEdge → g.HalfEdge) × Finset (Fin g.m)) := do
  let N := ∑ i, g.g i
  -- (P1)
  rcharge (g.alpha + n + 1)
  let seq ← g.drawSlots fuel (n - 2) g.slotList
  rcharge (seq.length + 1)
  let edges ← liftC (pruferEdgesC n (seq.map (·.1)))
  -- (P2)
  let idx := edges.zipIdx
  let att ← (List.finRange n).foldlM (fun (acc : List (ℕ × g.HalfEdge)) i => do
      rcharge (idx.length * (2 * opCost n n + 2) + acc.length + 1)
      let inc := (idx.filter (fun p => decide (p.1.1 = i) || decide (p.1.2 = i))).map (·.2)
      let r ← g.attachAt fuel i inc (List.finRange (g.g i))
      pure (acc ++ r)) []
  rcharge (idx.length * (att.length + 1) * (opCost N N + 2))
  let treePairs : List (g.HalfEdge × g.HalfEdge) := idx.filterMap (fun p =>
    match att.filter (fun q => decide (q.1 = p.2)) with
    | [q1, q2] => some (q1.2, q2.2)
    | _ => none)
  -- (P3)
  let attached := att.map (·.2)
  rcharge (N * (attached.length + 1) * (opCost N N + 2))
  let resid := g.heList.filter (fun h => decide (h ∉ attached))
  let mpairs ← g.matchResid fuel resid.length resid
  let ps := treePairs ++ mpairs
  let f := g.pairFun ps
  -- the planted tree as edge indices of `G(π)`: `N` evaluations of `f` for the smaller
  -- half-edges, then `m` membership tests
  rcharge (N * (ps.length + 2) * (2 * opCost N N + 2) +
    g.m * (N + attached.length + 2) * (opCost N N + 2))
  let T := ((List.finRange g.m).filter (fun k => decide ((g.pairOf f k).1 ∈ attached))).toFinset
  pure (f, T)

/-- Write `G(f)` into arrays: the smaller half-edges and their partners' vertices. -/
def materializeC (f : g.HalfEdge → g.HalfEdge) (npairs : ℕ) : Counted (MGraph n g.m) := do
  let N := ∑ i, g.g i
  charge (N * (npairs + 2) * (2 * opCost N N + 2) + 2 * g.m * (N + npairs + 2) + 1)
  let L := g.lowHalves f
  let srcL := L.map (fun h => h.1)
  let dstL := L.map (fun h => (f h).1)
  pure ⟨fun k => srcL.getD k.1 (g.defaultHE k).1, fun k => dstL.getD k.1 (g.defaultHE k).1⟩

end DegSeq

/-- The basis sampler of Theorem 1.1: draw `(π, T)` from the tilted `4`-regular model on
`n = d − 1` vertices (Lemma C.6) and output `π` with the fundamental-cycle matrix `C_T` of
`G(π)`, a `ℤ`-basis of `Λ_{G(π)}`. -/
def sampleBasis (d : ℕ) (fuel : ℕ) :
    RProg (((reg4 (d - 1)).HalfEdge → (reg4 (d - 1)).HalfEdge) ×
      (Fin (reg4 (d - 1)).m → Fin d → ℤ)) := do
  let r ← (reg4 (d - 1)).sampleProcess fuel
  let G ← liftC ((reg4 (d - 1)).materializeC r.1 (reg4 (d - 1)).m)
  let B ← liftC (G.fundMatrixC r.2)
  rcharge ((reg4 (d - 1)).m * d + 1)
  pure (r.1, fun e j =>
    if h : j.1 < (reg4 (d - 1)).m + 1 - (d - 1) then B e ⟨j.1, h⟩ else 0)

end FlowLatRound


