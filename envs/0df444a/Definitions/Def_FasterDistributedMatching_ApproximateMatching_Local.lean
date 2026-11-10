-- Prove2me | Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
-- name    : FasterDistributedMatching_ApproximateMatching_Local
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:09:34.390327+00:00
-- url     : https://prove2.me/theorems/02e5df90-2ba2-4ac9-a4d2-5463b27ae463
-- title:
--   Deterministic synchronous LOCAL execution and local edge outputs
-- statement:
--   A deterministic LOCAL protocol specializes the published synchronous unbounded-message program by requiring initialization to be independent of every private tape. Its state and message types and all protocol rules are chosen before any network instance. A round broadcasts a message, receives the multiset of neighboring messages, and updates the local state. Addressed payloads can be carried in a broadcast dictionary.
--
--   $$\operatorname{OPT}(G)\le (1+\varepsilon)|M|$$
--
--   is expressed using an actual subgraph matching whose endpoint reports agree. Nodes report their partner's identifier, or no edge. Incident real-valued outputs similarly agree at both endpoints. Initial inputs contain only neighbor identifiers and the locally supplied data. Global parameters contain only the stated graph bounds and accuracy parameter. Unique identifiers range over a fixed polynomial in the supplied vertex bound; every injection in this range is permitted. Vertex indices are absent from processor inputs.
--
--   This interface expresses operational distributed claims without assuming any algorithmic correctness or runtime in a model field.
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), §2 LOCAL model, printed p.6, PDF p.8; §3.5, printed pp.14–15, PDF pp.16–17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
import Definitions.Def_SmoothedMIS_LocalAlg

namespace FasterDistributedMatching.ApproximateMatching

/-! The §2 LOCAL model is the published synchronous model with no private-tape dependence.
No correctness or runtime assertion is a field of this wrapper. -/
structure Deterministic (K I O : Type) where
  program : SmoothedMIS.LocalAlg K I O
  tape_independent : ∀ k id x t t', program.init k id x t = program.init k id x t'

noncomputable def execute {K I O : Type} (A : Deterministic K I O) {N : ℕ}
    (G : SimpleGraph (Fin N)) (k : K) (ids : Fin N → ℕ) (inp : Fin N → I) : Fin N → O :=
  A.program.output G k ids inp (fun _ _ => false)

/- One fixed polynomial ID convention, including n=0,1. Every injection in range is allowed. -/
def Identifiers {N : ℕ} (n b : ℕ) (ids : Fin N → ℕ) : Prop :=
  Function.Injective ids ∧ ∀ v, ids v < (max 2 n) ^ b

open Classical in
noncomputable def boundedGraph {N : ℕ} (G : SimpleGraph (Fin N)) (n D : ℕ) : Prop :=
  N ≤ n ∧ ∀ v, G.degree v ≤ D

open Classical in
noncomputable def neighborIDs {N : ℕ} (G : SimpleGraph (Fin N))
    (ids : Fin N → ℕ) (v : Fin N) : Finset ℕ :=
  (G.neighborFinset v).image ids

structure Bounds where
  n : ℕ
  degree : ℕ
  deriving Inhabited

structure Accuracy extends Bounds where
  epsilon : ℝ

/- The source's matching output: either no edge or the identifier of one's partner. -/
def ReportsMatching {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (out : Fin N → Option ℕ) (M : SimpleGraph (Fin N)) : Prop :=
  Matching G M ∧ ∀ v,
    (out v = none ↔ ∀ w, ¬ M.Adj v w) ∧
    (∀ j, out v = some j ↔ ∃ w, M.Adj v w ∧ ids w = j)

/- Real-valued incident outputs agree at both endpoints; all other pairs are zero extended. -/
def ReportsWeights {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (out : Fin N → ℕ → ℝ) (x : Sym2 (Fin N) → ℝ) : Prop :=
  (∀ e, e ∉ G.edgeSet → x e = 0) ∧
  ∀ u v, G.Adj u v → out u (ids v) = x s(u,v) ∧ out v (ids u) = x s(u,v)

/- Local incident values only; absent IDs carry zero, never a full labelled graph. -/
open Classical in
noncomputable def weightInput {N : ℕ} (G : SimpleGraph (Fin N))
    (ids : Fin N → ℕ) (x : Sym2 (Fin N) → ℝ) (v : Fin N) :
    Finset ℕ × (ℕ → ℝ) :=
  (neighborIDs G ids v, fun j => ∑ w ∈ G.neighborFinset v,
    if ids w = j then x s(v,w) else 0)

end FasterDistributedMatching.ApproximateMatching


