-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_VertexFlow
-- name    : MaxIsoVertexCuts_Shredders_VertexFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:56:08.562215+00:00
-- url     : https://prove2.me/theorems/316885d5-2c2d-4922-896f-d9c718161867
-- title:
--   VertexFlow
-- statement:
--   An independent general vertex-capacitated undirected maximum-flow interface: nonnegative flow in both directions on each enumerated edge, conservation at nonterminals, and incoming/outgoing throughput bounded by finite integer vertex capacities. Source and sink capacities can be set above all other capacity sums. Every correct oracle may return any integral maximum flow, including circulations. Invalid requests return the empty list. T is monotone in both sizes, jointly superadditive and at least m+n. Oracle cost is the executed RAM cost plus the sum of T(m_q,n_q), and writing the output is charged. This direct vertex interface avoids silently changing T(m,n) to T(2m+n,2n) through edge splitting; the published edge-capacitated interface is not reused.
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_RAMBounds

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

structure VertexFlowQuery where
  n : ℕ
  edges : List (Fin n × Fin n)
  capacity : Fin n → ℕ
  source : Fin n
  sink : Fin n

def VertexFlowQuery.Valid (Q : VertexFlowQuery) : Prop := Q.source ≠ Q.sink

def VertexFlowQuery.encode (Q : VertexFlowQuery) : List ℤ :=
  ([Q.n, Q.edges.length, Q.source.val, Q.sink.val] : List ℤ) ++
  (List.ofFn fun v : Fin Q.n => (Q.capacity v : ℤ)) ++
  Q.edges.flatMap (fun e => [(e.1.val : ℤ), (e.2.val : ℤ)])

noncomputable def flowIn (Q : VertexFlowQuery) (f : Fin Q.edges.length → Bool → ℝ) (v : Fin Q.n) : ℝ :=
  ∑ e : Fin Q.edges.length, ((if (Q.edges.get e).2 = v then f e false else 0) +
    (if (Q.edges.get e).1 = v then f e true else 0))
noncomputable def flowOut (Q : VertexFlowQuery) (f : Fin Q.edges.length → Bool → ℝ) (v : Fin Q.n) : ℝ :=
  ∑ e : Fin Q.edges.length, ((if (Q.edges.get e).1 = v then f e false else 0) +
    (if (Q.edges.get e).2 = v then f e true else 0))

def FeasibleVertexFlow (Q : VertexFlowQuery) (f : Fin Q.edges.length → Bool → ℝ) : Prop :=
  (∀ e b, 0 ≤ f e b) ∧
  (∀ v, flowIn Q f v ≤ Q.capacity v ∧ flowOut Q f v ≤ Q.capacity v) ∧
  ∀ v, v ≠ Q.source → v ≠ Q.sink → flowIn Q f v = flowOut Q f v

noncomputable def vertexFlowValue (Q : VertexFlowQuery) (f : Fin Q.edges.length → Bool → ℝ) : ℝ :=
  flowOut Q f Q.source - flowIn Q f Q.source

def MaximumVertexFlow (Q : VertexFlowQuery) (f : Fin Q.edges.length → Bool → ℝ) : Prop :=
  FeasibleVertexFlow Q f ∧ ∀ g, FeasibleVertexFlow Q g → vertexFlowValue Q g ≤ vertexFlowValue Q f

def IsVertexFlowOracle (O : CongruencyTU.Oracle) : Prop :=
  (∀ Q : VertexFlowQuery, Q.Valid → ∃ f : Fin Q.edges.length → Bool → ℕ,
    O Q.encode = (List.ofFn (fun e => [(f e false : ℤ), (f e true : ℤ)])).flatten ∧
      MaximumVertexFlow Q (fun e b => (f e b : ℝ))) ∧
  ∀ input, (¬ ∃ Q : VertexFlowQuery, Q.Valid ∧ Q.encode = input) → O input = []

def AdmissibleTime (T : ℕ → ℕ → ℕ) : Prop :=
  (∀ m n, m+n ≤ T m n) ∧
  (∀ m m' n, m ≤ m' → T m n ≤ T m' n) ∧
  (∀ m n n', n ≤ n' → T m n ≤ T m n') ∧
  ∀ m n m' n', T m n + T m' n' ≤ T (m+m') (n+n')

noncomputable def oracleCost (P : CongruencyTU.Program) (O : CongruencyTU.Oracle)
    (input : List ℤ) (T : ℕ → ℕ → ℕ) (steps : ℕ) : ℕ :=
  (CongruencyTU.run P O CongruencyTU.noCoins input steps).cost +
  ∑ t ∈ Finset.range steps,
    match CongruencyTU.queryAt P O CongruencyTU.noCoins input t with
    | none => 0
    | some q => T (q.getD 1 0).toNat (q.getD 0 0).toNat

def OracleRun (P : CongruencyTU.Program) (O : CongruencyTU.Oracle) (input : List ℤ)
    (T : ℕ → ℕ → ℕ) (B n m c : ℕ) (Good : List ℤ → Prop) : Prop :=
  ∃ t, CongruencyTU.isHalted P (CongruencyTU.run P O CongruencyTU.noCoins input t) = true ∧
    oracleCost P O input T t + (CongruencyTU.outputAfter P O CongruencyTU.noCoins input t).length ≤ B ∧
    WordBound P O CongruencyTU.noCoins input n m c ∧
    (∀ j < t, ∀ q, CongruencyTU.queryAt P O CongruencyTU.noCoins input j = some q →
      ∃ Q : VertexFlowQuery, Q.Valid ∧ Q.encode = q) ∧
    Good (CongruencyTU.outputAfter P O CongruencyTU.noCoins input t)

end MaxIsoVertexCuts.Shredders


