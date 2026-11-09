-- Prove2me | Definitions.Def_MultipleUnicast_Counterexample_CausalModel
-- name    : MultipleUnicast_Counterexample_CausalModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:49.26801+00:00
-- url     : https://prove2.me/theorems/10a6de56-106d-415d-b227-3c60e7fbf261
-- title:
--   General chronological codes and Shannon throughput
-- statement:
--   For an undirected capacitated network with indexed sources $s_i$, sinks $t_i$ and demands $d_i$, a raw code consists of finitely many directed events, arbitrary event alphabets, their transmitted functions of the message tuple, and local destination decoding functions. Causality requires equality of an event's outputs whenever its tail's own source messages and all earlier received event values agree. Correctness requires recovery for every message tuple. Only physical arcs may be used. Grouping the events on each directed arc into a chronological product supplies exactly its full transmitted alphabet.
--
--   For any discrete probability law $p$, Shannon entropy in bits is
--   $$H(p)=\sum_a-p(a)\log_2p(a),\qquad 0\log_2 0=0.$$
--   The sum is extended nonnegative, so infinite entropy is retained. A joint source law is independent when its mass is the product of its marginal masses. A code supports rate $r\ge0$ at a scale $c^*>0$ when it is causal and correct, its sources are independent, and
--   $$H(m_i)\ge r d_i c^*,\qquad H(X_{uv})+H(X_{vu})\le c(\{u,v\})c^*.$$
--   The coding throughput is the supremum over all such codes, alphabets, laws, rates and scales. It is not restricted to linear codes or finite alphabets.
--
--   This is the general interface needed to compare the particular finite witness with the full coding throughput. Raw data carries no causality or recovery certificates; these are separate predicates.
--
--   **Formalization Note** Arbitrary discrete laws use `PMF` on unrestricted carrier types, as appropriate for Shannon messages. No finiteness or uniformity assumption is imposed. Infinite entropy and an unbounded throughput use `ENNReal`. The base is fixed to two, with the freely varying positive scale absorbing a change of logarithm base.
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §2, PDF pp. 4–5 / printed pp. 3–4

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample
noncomputable section
open scoped Classical

/-- Shannon entropy in bits, for arbitrary discrete laws and arbitrary alphabets.
The extended nonnegative sum preserves infinite entropy; zero masses contribute zero. -/
def entropy {A : Type} (p : PMF A) : ENNReal :=
  ∑' a, ENNReal.ofReal (-(p a).toReal * Real.logb 2 (p a).toReal)

variable {V : Type} (N : GeometryOfGraphs.FlowCut.Network V)
abbrev Messages (M : Fin N.k → Type) := (i : Fin N.k) → M i
abbrev Own (M : Fin N.k → Type) (v : V) := (i : {i : Fin N.k // N.s i = v}) → M i.val

/-- Raw chronological computation data, with no success or rate assertions in its fields.
Directed arc alphabets are the chronological products of the event alphabets. -/
structure ChronologicalCode (M : Fin N.k → Type) where
  length : ℕ
  src : Fin length → V
  dst : Fin length → V
  alphabet : Fin length → Type
  transmit : Messages N M → (t : Fin length) → alphabet t
  decode : (i : Fin N.k) → Own N M (N.t i) →
    ((t : {t : Fin length // dst t = N.t i}) → alphabet t.val) → M i

variable {N} {M : Fin N.k → Type}

def ownValues (v : V) (m : Messages N M) : Own N M v := fun i => m i.val

def received (P : ChronologicalCode N M) (v : V) (m : Messages N M) :
    (t : {t : Fin P.length // P.dst t = v}) → P.alphabet t.val :=
  fun t => P.transmit m t.val

/-- Extensional dependence precisely on the tail's messages and earlier receptions. -/
def Causal (P : ChronologicalCode N M) : Prop :=
  ∀ t m m',
    (∀ i, N.s i = P.src t → m i = m' i) →
    (∀ a, a.val < t.val → P.dst a = P.src t → P.transmit m a = P.transmit m' a) →
    P.transmit m t = P.transmit m' t

def UsesPhysicalArcs (P : ChronologicalCode N M) : Prop :=
  ∀ t, P.src t ≠ P.dst t ∧ 0 < N.C (P.src t) (P.dst t)

def Correct (P : ChronologicalCode N M) : Prop :=
  ∀ m i, P.decode i (ownValues (N.t i) m) (received P (N.t i) m) = m i

def arcSymbols (P : ChronologicalCode N M) (u v : V) (m : Messages N M) :
    (t : {t : Fin P.length // P.src t = u ∧ P.dst t = v}) → P.alphabet t.val :=
  fun t => P.transmit m t.val

/-- Finite indexed independence of arbitrary discrete source laws: joint mass is the
product of its marginals. No uniformity, finite alphabet or linearity requirement. -/
def IndependentSources (p : PMF (Messages N M)) : Prop :=
  ∀ m, p m = ∏ i, (p.map (fun x => x i)) (m i)

/-- Exactly §2's entropy normalization and shared BOTH-direction capacity. -/
def SupportsRate (P : ChronologicalCode N M) (p : PMF (Messages N M))
    (r scale : ℝ) : Prop :=
  0 ≤ r ∧ 0 < scale ∧ IndependentSources p ∧
  Causal P ∧ UsesPhysicalArcs P ∧ Correct P ∧
  (∀ i, ENNReal.ofReal (r * N.D i * scale) ≤ entropy (p.map (fun m => m i))) ∧
  (∀ u v, entropy (p.map (arcSymbols P u v)) + entropy (p.map (arcSymbols P v u)) ≤
    ENNReal.ofReal (N.C u v * scale))

/-- The supremum over ALL §2 codes and source laws, with +∞ retained if unbounded. -/
def codingThroughput (N : GeometryOfGraphs.FlowCut.Network V) : ENNReal :=
  sSup {R | ∃ (M : Fin N.k → Type) (P : ChronologicalCode N M)
    (p : PMF (Messages N M)) (r scale : ℝ), SupportsRate P p r scale ∧ R = ENNReal.ofReal r}

end
end MultipleUnicast.Counterexample


