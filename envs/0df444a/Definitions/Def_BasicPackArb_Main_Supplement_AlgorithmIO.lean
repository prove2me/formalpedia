-- Prove2me | Definitions.Def_BasicPackArb_Main_Supplement_AlgorithmIO
-- name    : BasicPackArb_Main_Supplement_AlgorithmIO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:57:40.461834+00:00
-- url     : https://prove2.me/theorems/a1e7f096-eea4-4879-b723-8567f2dfc2eb
-- title:
--   Labelled rooted-digraph inputs, packing and obstruction output, signed costs
-- statement:
--   An instance explicitly lists $n$ vertices, $m$ actual arcs, $t$ root elements, each arc's endpoints and each root's placement. Labels preserve loops, parallel arcs, repeated roots, isolated vertices and zero sizes. Its input size $L$ includes $n+m+t$ and the binary lengths of the graph and placement lists. The matroid is not listed: a correct oracle must return $r_M(Q)$ for every root subset $Q$ queried.
--
--   A tag-zero output lists all vertex and arc membership bits of every root's arborescence, in fixed label order. A tag-one output is a vertex $v$ with $S_v$ dependent. A tag-two output lists a nonempty vertex set $X$ satisfying
--
--   $$\rho_D(X)+r_M(S_X)<r_M(S).$$
--
--   Validity is checked against the published packing, independence and cut definitions. Matching output masks determine the full family of subgraphs, rather than merely its existence. For signed arc costs $c$, packing cost is the sum over the union of selected arcs. An optimal output encodes a feasible packing of cost at most that of every feasible packing. Real costs use exact arithmetic; rational bit input size adds the numerator and denominator lengths of every cost. These are output specifications, never promises that an efficient solver is supplied.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, pp. 6–7, Theorems 4.2–4.3 and rank oracle convention

import Definitions.Def_BasicPackArb_Main_Supplement_Polyhedron
import Definitions.Def_BasicPackArb_Main_Supplement_RankMachine
import Definitions.Def_BasicPackArb_Main_ProofObjects

set_option autoImplicit false
open scoped BigOperators

namespace BasicPackArb.Main.Supplement

/-- Explicitly labelled finite instance. All finite digraphs with roots have such a presentation;
there is no matroid table, solution, minimization oracle or feasibility promise in this input. -/
structure Instance (n m t : ℕ) where
  tail : Fin m → Fin n
  head : Fin m → Fin n
  placement : Fin t → Fin n

namespace Instance

variable {n m t : ℕ}

def digraph (I : Instance n m t) : Digraph (Fin n) (Fin m) :=
  ⟨I.tail, I.head, Finset.univ⟩

/-- Three dimensions, followed by tails, heads and root placements in label order. -/
def input (I : Instance n m t) : List ℕ :=
  [n, m, t] ++ List.ofFn (fun a => (I.tail a).val) ++
    List.ofFn (fun a => (I.head a).val) ++ List.ofFn (fun s => (I.placement s).val)

/-- Includes explicit carrier sizes (also isolated vertices) and the binary graph encoding.
The rank table of size 2^t is never included. -/
def size (I : Instance n m t) : ℕ :=
  1 + n + m + t + (I.input.map bitSize).sum

def rankOracleCorrect (M : Matroid (Fin t)) (oracle : Finset (Fin t) → ℕ) : Prop :=
  ∀ Q, oracle Q = rank M (Q : Set (Fin t))

/-- A concrete full packing is emitted as tag 0 then the vertex and arc masks for every root.
The root of each arborescence is the already supplied placement. All bits are emitted. -/
noncomputable def packingCode (I : Instance n m t)
    (T : Fin t → Arborescence I.digraph) : List ℕ := by
  classical
  exact 0 :: (List.finRange t).flatMap (fun s =>
    List.ofFn (fun v : Fin n => if v ∈ (T s).verts then 1 else 0) ++
    List.ofFn (fun a : Fin m => if a ∈ (T s).arcs then 1 else 0))

/-- All three outputs of Theorem 4.2, with actual offending objects. -/
noncomputable def ValidOutput (I : Instance n m t) (M : Matroid (Fin t))
    (out : List ℕ) : Prop :=
  (∃ T, IsBasicPacking I.digraph I.placement M T ∧ out = I.packingCode T) ∨
  (∃ v : Fin n, ¬ M.Indep (I.placement ⁻¹' {v}) ∧ out = [1, v.val]) ∨
  (∃ X : Finset (Fin n), X.Nonempty ∧
    (I.digraph.inDeg X : ℕ∞) + M.eRk (I.placement ⁻¹' (X : Set (Fin n))) < M.eRk Set.univ ∧
    out = 2 :: List.ofFn (fun v : Fin n => if v ∈ X then 1 else 0))

/-- Signed costs on the actual arc set; each arc is counted once in the union. -/
noncomputable def packingCost {K : Type} [AddCommMonoid K] (I : Instance n m t)
    (c : Fin m → K) (T : Fin t → Arborescence I.digraph) : K := by
  classical
  exact ∑ a : Fin m, if ∃ s, a ∈ (T s).arcs then c a else 0

/-- Optimality is against every actual feasible packing, not against an assigned optimum. -/
noncomputable def OptimalOutput {K : Type} [AddCommMonoid K] [LE K]
    (I : Instance n m t) (M : Matroid (Fin t)) (c : Fin m → K) (out : List ℕ) : Prop :=
  ∃ T, IsBasicPacking I.digraph I.placement M T ∧ out = I.packingCode T ∧
    ∀ U, IsBasicPacking I.digraph I.placement M U → I.packingCost c T ≤ I.packingCost c U

/-- Standard finite-encoding input size for signed rational costs. -/
def rationalInputSize (I : Instance n m t) (c : Fin m → ℚ) : ℕ :=
  I.size + (List.ofFn (fun a => rationalSize (c a))).sum

end Instance
end BasicPackArb.Main.Supplement


