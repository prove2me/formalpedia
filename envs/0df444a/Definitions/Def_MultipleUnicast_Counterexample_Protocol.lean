-- Prove2me | Definitions.Def_MultipleUnicast_Counterexample_Protocol
-- name    : MultipleUnicast_Counterexample_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:54.9121+00:00
-- url     : https://prove2.me/theorems/0c776d74-b370-49ea-9852-e97083a9d917
-- title:
--   Local interpolation execution, concrete network, and rate interfaces
-- statement:
--   Process the vertices in the Appendix A order. At each vertex use only its own $B$ source messages, previously received physical values, and public zero values on $C$. Interpolate the local quartic and assign its evaluations to the outgoing positions. Only outgoing physical positions are transmitted. The chronological list orders those transmissions first by vertex and then by edge index; the later endpoint of a session uses its locally available values to decode the corresponding $B$ position.
--
--   The network has symmetric capacity one exactly on the physical graph and unit demand for each session. The witness law is the uniform law on the complete input tuple, with scale
--   $$c^*=\log_2 9.$$
--   The routing throughput is the published real-arc-flow maximum, and the feasible-rate set contains precisely its nonnegative feasible common rates.
--
--   The proposition `CausalLinearCode` states the conclusions to verify about the already constructed code: five-position linear interpolation, causality, physical-arc use, recovery for all tuples, one transmission per physical edge, and linear transmission and local decoding functions. These properties are not construction assumptions.
--
--   **Formalization Note** Sessions are reindexed by an explicit equivalence between $B$ and `Fin (card B)` for the published flow interface. Outgoing artificial $J$ evaluations are internal state, not transmitted resources. Classical solving in interpolation uses no global compatible-extension oracle. The execution is a recursion from an initial zero state, and a destination's decoder receives only its own source messages and incoming physical history.
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §4, PDF pp. 10–12 / printed pp. 9–11; §2, PDF pp. 4–5 / printed pp. 3–4; Appendix A, PDF pp. 14–15 / printed pp. 13–14

import Definitions.Def_MultipleUnicast_Counterexample_LocalSpace
import Definitions.Def_MultipleUnicast_Counterexample_CausalModel
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample
noncomputable section
open scoped Classical

abbrev Input := Session → F9

def available (v : Vertex) (x : Input) (state : Edge → F9) (q : Edge) : F9 :=
  if q ∈ C then 0
  else if h : q ∈ B then
    if head q = v then x ⟨q,h⟩ else state q
  else state q

/-- A processing step accesses only local inputs and already received edge values.
Only outgoing artificially oriented positions are updated. -/
def process (v : Vertex) (x : Input) (state : Edge → F9) : Edge → F9 :=
  let a := interpolate v (available v x state)
  fun q => if tail q = v then localEvaluation v a q else state q

def run : ℕ → Input → Edge → F9
  | 0, _ => 0
  | n + 1, x => process (processingOrder.getD n 0) x (run n x)

def execution (x : Input) : Edge → F9 := run 182 x

/-- Chronological serial refinement: vertex order first, outgoing physical edge index second. -/
def schedule : List Edge := processingOrder.flatMap fun v =>
  (List.finRange 910).filter fun q => q ∈ physical ∧ tail q = v

def eventEdge (t : Fin schedule.length) : Edge := schedule.getD t.val 0

def sessionEquiv : Fin (Fintype.card Session) ≃ Session := (Fintype.equivFin Session).symm

/-- Symmetric 0/1 capacity matrix. Zero capacity is used for absent edges. -/
def network : GeometryOfGraphs.FlowCut.Network Vertex where
  C u v := if graph.Adj u v then 1 else 0
  C_nonneg _ _ := by split_ifs <;> norm_num
  C_symm u v := by
    have h : graph.Adj u v ↔ graph.Adj v u := ⟨graph.adj_symm, graph.adj_symm⟩
    simp only [h]
  C_self u := by simp
  k := Fintype.card Session
  s i := earlier (sessionEquiv i).val
  t i := later (sessionEquiv i).val
  D _ := 1
  D_nonneg _ := by norm_num

abbrev IndexInput := Fin network.k → F9

def toInput (x : IndexInput) : Input := fun q => x (sessionEquiv.symm q)

/-- A sink builds its five local values from its own sources and received events.
Searches for received symbols have a zero default outside their stipulated domain. -/
def decoderValues (v : Vertex) (own : Own network (fun _ => F9) v)
    (history : (t : {t : Fin schedule.length // later (eventEdge t) = v}) → F9)
    (q : Edge) : F9 :=
  if q ∈ C then 0
  else if h : q ∈ B then
    let i := sessionEquiv.symm ⟨q,h⟩
    if h' : network.s i = v then own ⟨i,h'⟩ else 0
  else if h : ∃ t : Fin schedule.length, eventEdge t = q ∧ later (eventEdge t) = v
    then history ⟨Classical.choose h, (Classical.choose_spec h).2⟩ else 0

/-- The concrete code data is computed without any correctness certificate. -/
def protocol : ChronologicalCode network (fun _ => F9) where
  length := schedule.length
  src t := earlier (eventEdge t)
  dst t := later (eventEdge t)
  alphabet _ := F9
  transmit m t := execution (toInput m) (eventEdge t)
  decode i own history :=
    localEvaluation (network.t i)
      (interpolate (network.t i) (decoderValues (network.t i) own history))
      (sessionEquiv i).val

/-- Uniform independent input law for the finite witness only. -/
def witnessLaw : PMF IndexInput := PMF.uniformOfFintype IndexInput

def witnessScale : ℝ := Real.logb 2 9

def routingThroughput : ℝ := network.maxflow

def feasibleRates : Set ℝ := {r | 0 ≤ r ∧ ∃ f, network.IsFeasibleFlow f r}

/-- The claimed local linear interpolation API, kept as a proposition to prove. -/
def LocalInterpolation : Prop :=
  ∀ v, (knownPositions v).card = 5 ∧
    ∃ L : ({q : Edge // q ∈ knownPositions v} → F9) →ₗ[F9] Coefficients,
      (∀ y q, localEvaluation v (L y) q.val = y q) ∧
      (∀ y, interpolate v y = L (fun q => y q.val))

/-- Verification conditions on the already constructed code, NOT constructor fields. -/
def CausalLinearCode : Prop :=
  LocalInterpolation ∧ Causal protocol ∧ UsesPhysicalArcs protocol ∧ Correct protocol ∧
  schedule.length = physical.card ∧
  (∀ t, eventEdge t ∈ physical) ∧
  (∀ q ∈ physical, ∃! t : Fin schedule.length, eventEdge t = q) ∧
  (∀ t, ∃ L : IndexInput →ₗ[F9] F9, ∀ x, protocol.transmit x t = L x) ∧
  (∀ i, ∃ L : (Own network (fun _ => F9) (network.t i) ×
      ((t : {t : Fin protocol.length // protocol.dst t = network.t i}) → F9)) →ₗ[F9] F9,
    ∀ o h, protocol.decode i o h = L (o,h))

end
end MultipleUnicast.Counterexample


