-- Prove2me | Definitions.Def_NogoodColoring1137_Main_TwoListRecursion
-- name    : NogoodColoring1137_Main_TwoListRecursion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:37.708284+00:00
-- url     : https://prove2.me/theorems/39c7a112-88a8-4eeb-90c2-77901229216a
-- title:
--   Singleton propagation and exact two-list recursion
-- statement:
--   Propagate singleton colors on the original graph. Simultaneous deletion reaches a fixed point within $3n$ rounds, since only $3n$ color-membership bits can disappear. Return zero on empty lists and one when all vertices are fixed. With a common remaining two-list, finite parity reachability detects nonbipartiteness or returns $2^h$, including isolated components.
--   $$T(t)\le T(t-1)+T(\lfloor5t/6\rfloor),\qquad T(0)=1.$$
--   Otherwise choose a largest list type, a vertex outside it, and local forbidden pairs from adjacency or a common-neighbor list certificate. Choose the color covering at least half the pairs. One branch fixes it and removes the forbidden partner colors; the other fixes the alternative. CountRec returns both the sum of counts and the number of leaves. Its public call has fuel $n$. LeafBound is $(t+1)^{\lceil\log_{6/5}(t+1)\rceil+1}$.
--
--   This is a concrete recursion, not an assumed counting answer. **Formalization Note** Parity closure uses $2n$ rounds on $2n$ states. Every recursive branch fixes a two-list vertex; proving that the fuel-zero fallback is unreachable before a base case is part of Lemma 6.2.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), §6, pp.19–20, equation (10)

import Mathlib
import Definitions.Def_NogoodColoring1137_Main_Computation

namespace NogoodColoring1137.Main

/-- One simultaneous round of the source singleton rule; it only removes colors. -/
def PropagateStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) : Lists n := fun v =>
  (L v).filter (fun a => ∀ w, G.Adj w v → L w ≠ {a})

/-- At most 3n membership bits can disappear, so 3n rounds suffice. -/
def Propagate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) : Lists n := (PropagateStep G)^[3*n] L

def TwoVertices {n : ℕ} (L : Lists n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (L v).card = 2)

/-- Reachability with parity, by 2n rounds on a graph with 2n vertex/parity states. -/
def ParityReach {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n × Bool) :=
  (fun R : Finset (Fin n × Bool) => R ∪
    Finset.univ.filter (fun z => z.1 ∈ S ∧
      ∃ y ∈ R, G.Adj y.1 z.1 ∧ z.2 = !y.2))^[2*n] {(v,false)}

/-- Return the number of bipartite orientations, including isolated components. -/
def CommonListCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : ℕ :=
  if ∃ v ∈ S, (v,true) ∈ ParityReach G S v then 0
  else 2 ^ (S.filter (fun v => ∀ w ∈ S,
    ((w,false) ∈ ParityReach G S v ∨ (w,true) ∈ ParityReach G S v) → v ≤ w)).card

/-- The local certificates in the proof of Lemma 6.1, rather than testing extensions. -/
def LocalForbidden {n : ℕ} (G : SimpleGraph (Fin n)) (L : Lists n)
    (v w : Fin n) (a b : Color) : Prop :=
  (G.Adj v w ∧ a = b) ∨
  ∃ u, G.Adj v u ∧ G.Adj u w ∧ ∀ g ∈ L u, g = a ∨ g = b

instance localForbiddenDecidable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) (v w : Fin n) (a b : Color) : Decidable (LocalForbidden G L v w a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

def FindPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) (v w : Fin n) : Option (Color × Color) :=
  ((List.finRange 3).flatMap (fun a => (List.finRange 3).map (a, ·))).find?
    (fun ab => ab.1 ∈ L v ∧ ab.2 ∈ L w ∧ LocalForbidden G L v w ab.1 ab.2)

/-- Pair (number of colorings, number of leaves). The finite fuel is n in the public call;
each recursive edge fixes at least one currently two-list vertex. -/
def CountRec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ℕ → Lists n → ℕ × ℕ
  | fuel, lists =>
    let L := Propagate G lists
    let S := TwoVertices L
    if ∃ v, L v = ∅ then (0,1)
    else if S = ∅ then (1,1)
    else if ∀ v ∈ S, ∀ w ∈ S, L v = L w then (CommonListCount G S,1)
    else match fuel with
    | 0 => (0,1)
    | k+1 =>
      let size := fun a : Color => (S.filter (fun w => L w = Finset.univ.erase a)).card
      let typ := (List.finRange 3).foldl (fun best a => if size best < size a then a else best) 0
      let largest := S.filter (fun w => L w = Finset.univ.erase typ)
      match (List.finRange n).find? (fun v => v ∈ S ∧ v ∉ largest) with
      | none => (0,1)
      | some v =>
        let score := fun a : Color => (largest.filter (fun w =>
          (FindPair G L v w).any (fun ab => ab.1 == a))).card
        let colors := (List.finRange 3).filter (fun a => a ∈ L v)
        match colors with
        | [] => (0,1)
        | first :: rest =>
          let gamma := rest.foldl (fun best a => if score best < score a then a else best) first
          let fast : Lists n := fun w => if w = v then {gamma} else
            if w ∈ largest then
              match FindPair G L v w with
              | some ab => if ab.1 = gamma then (L w).erase ab.2 else L w
              | none => L w
            else L w
          let slow := Function.update L v ((L v).erase gamma)
          let ansFast := CountRec G k fast
          let ansSlow := CountRec G k slow
          (ansFast.1 + ansSlow.1, ansFast.2 + ansSlow.2)

def TwoListCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) : ℕ := (CountRec G n L).1

/-- Explicit leaf bound obtained by unrolling (10); no real logarithm is evaluated by the algorithm. -/
noncomputable def LeafBound (t : ℕ) : ℕ :=
  (t+1)^(⌈Real.log ((t : ℝ)+1) / Real.log (6/5 : ℝ)⌉₊ + 1)

end NogoodColoring1137.Main


