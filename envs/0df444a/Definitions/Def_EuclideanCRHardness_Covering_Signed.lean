-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Signed
-- name    : EuclideanCRHardness_Covering_Signed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:11.57944+00:00
-- url     : https://prove2.me/theorems/3f11b47c-cb54-4e71-bf37-3e2bc558f7d5
-- title:
--   Signed multigraph edge objects and optimum
-- statement:
--   A signed instance has $n$ vertices and a list of unit edge objects. Each object names its endpoints and prefers equality or inequality. Validity requires endpoints in range and distinct endpoints. Parallel objects with either preference remain separate. The score counts satisfied objects and $C$ is the finite maximum over sign assignments.
--
--   The incidence degree counts objects before cancellation. Trimming retains the endpoint set and relabels it, thereby discarding isolated vertices without enumerating a possibly enormous declared vertex range. The eligibility check recognizes valid nonisolated positive-edge instances before dense matrix construction.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), §3 preamble and Proposition 3.1 proof, printed p. 5 / PDF p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf Also Proposition 3.1 proof, printed p. 7 / PDF p. 8.

import Definitions.Def_EuclideanCRHardness_Covering_Wire

namespace EuclideanCRHardness.Covering

open scoped BigOperators
/-- Edge objects are a list: multiplicities and opposite preferences survive. -/
structure SignedEdge where
  u : ℕ
  v : ℕ
  equal : Bool
  deriving DecidableEq
structure SignedInstance where
  n : ℕ
  edges : List SignedEdge
  deriving DecidableEq

def SignedInstance.Valid (G : SignedInstance) : Prop :=
  ∀ e ∈ G.edges, e.u < G.n ∧ e.v < G.n ∧ e.u ≠ e.v

def atSign {n : ℕ} (s : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then s ⟨i,h⟩ else false

def score (G : SignedInstance) (s : Fin G.n → Bool) : ℕ :=
  (G.edges.filter (fun e => (atSign s e.u == atSign s e.v) == e.equal)).length

def optimum (G : SignedInstance) : ℕ := Finset.univ.sup (score G)

def degree (G : SignedInstance) (i : Fin G.n) : ℕ :=
  (G.edges.filter (fun e => e.u == i.val || e.v == i.val)).length

def Nonisolated (G : SignedInstance) : Prop := ∀ i : Fin G.n, 0 < degree G i

def edgeFields (e : SignedEdge) : List ℤ := [e.u, e.v, if e.equal then 1 else -1]
def encodeSigned (G : SignedInstance) : List Bool :=
  wireEncode ((G.n : ℤ) :: G.edges.flatMap edgeFields)
def readEdges : List ℤ → Option (List SignedEdge)
  | [] => some []
  | u::v::s::rest => do
      if u < 0 ∨ v < 0 ∨ (s ≠ 1 ∧ s ≠ -1) then none else do
        let es ← readEdges rest
        return ⟨u.toNat,v.toNat,s == 1⟩ :: es
  | _ => none

def decodeSigned (bits : List Bool) : Option SignedInstance := do
  let n::rest ← wireDecode bits | none
  if n < 0 then none else do
    let es ← readEdges rest
    return ⟨n.toNat, es⟩

def activeVertices (G : SignedInstance) : List ℕ :=
  (G.edges.flatMap (fun e => [e.u,e.v])).eraseDups
def trim (G : SignedInstance) : SignedInstance :=
  ⟨(activeVertices G).length, G.edges.map (fun e =>
    ⟨(activeVertices G).idxOf e.u, (activeVertices G).idxOf e.v, e.equal⟩)⟩
def eligible (G : SignedInstance) : Bool :=
  !G.edges.isEmpty && (G.n ≤ 2*G.edges.length) &&
    ((activeVertices G).length == G.n) &&
    G.edges.all (fun e => e.u < G.n && e.v < G.n && e.u != e.v)
def trimBits (bits : List Bool) : List Bool :=
  match decodeSigned bits with
  | none => []
  | some G => encodeSigned (trim G)

end EuclideanCRHardness.Covering


