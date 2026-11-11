-- Prove2me | Definitions.Def_ARGFContract_Hardness_GraphCodes
-- name    : ARGFContract_Hardness_GraphCodes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:04.281052+00:00
-- url     : https://prove2.me/theorems/7c8032d9-dc03-4744-afd0-9e2f0276aadc
-- title:
--   Finite simple graph input and dense binary encoding
-- statement:
--   A graph input contains a vertex count $n$ and an $n\times n$ Boolean table. Its undirected simple graph ignores diagonal entries and joins two distinct vertices when either directed table entry is true. Thus every finite simple graph is represented.
--
--   $$\operatorname{code}(G)=\operatorname{code}(n)\,\Vert\,\operatorname{matrix}(G).$$
--
--   The decoder requires a canonical self-delimiting vertex count and exactly $n^2$ table bits; invalid words denote the zero-vertex graph. The representation includes arbitrary finite graphs and adds no graph-theoretic promise. It supplies the concrete inputs for MIS and the contract instance family.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), proof of Theorem 1, p. 7 (G=(V,E), n=|V|); computational encoding reading; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Definitions.Def_ARGFContract_Hardness_BinaryCodes
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace ARGFContract.Hardness

/-- Dense graph input: binary vertex count plus a Boolean adjacency matrix.
No planarity, degree, weight, or nonemptiness promise. -/
structure GraphInput where
  n : ℕ
  edge : Fin n → Fin n → Bool

/-- Ignore the diagonal and symmetrize the adjacency table. -/
def GraphInput.graph (I : GraphInput) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel fun i j => I.edge i j = true

/-- Binary vertex count followed by n² adjacency bits in row-major order. -/
def encodeGraph (I : GraphInput) : List Bool :=
  encodeNat I.n ++ (List.ofFn fun i => List.ofFn fun j => I.edge i j).flatten

/-- Invalid strings are the empty graph. Reject noncanonical headers and wrong
matrix lengths before interpreting a table. This also bounds n by input length. -/
def decodeGraph (x : List Bool) : GraphInput :=
  match parseDigits x with
  | none => ⟨0, fun i => Fin.elim0 i⟩
  | some (digits, table) =>
    let n := digits.foldr (fun b a => 2 * a + if b then 1 else 0) 0
    if encodeNat n ++ table = x ∧ table.length = n * n then
      ⟨n, fun i j => table.getD (i.val * n + j.val) false⟩
    else ⟨0, fun i => Fin.elim0 i⟩

end ARGFContract.Hardness


