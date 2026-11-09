-- Prove2me | Definitions.Def_OnlineSteinitz_Reduction_Signer
-- name    : OnlineSteinitz_Reduction_Signer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:24.547717+00:00
-- url     : https://prove2.me/theorems/70ce3eb3-47cf-4316-b549-8d8446acd573
-- title:
--   Causal online signers and terminal proposed sums
-- statement:
--   An online signer, given a fixed private random tape, observes its local input history and emits one of the signs $\{-1,+1\}$ immediately for the current vector. Its history records the vectors and its own proposed signs. For a completed history $(x_i,\varepsilon_i)$ define
--   $$S=\sum_i\varepsilon_i x_i,\qquad q=\sum_i\varepsilon_i.$$
--   For randomized signers, every decision is measurable as a function of its tape for each fixed history and current vector. This interface expresses terminal signing guarantees without assuming any performance bound.
--
--   **Formalization Note** Boolean true denotes $+1$. A tape and the entire proposed history represent persistent private state by replay. The node capacity is known to its chosen rule; the supplied routing statistics in Algorithm 1 can be reconstructed from that capacity and the proposed history by quota repair. The interface gives no future-vector or total-sum input. No measurable structure on the vector type is imposed by this definition.
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf, SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366, §2.1, p.5 (persistent signers and routing statistics); §2.2, p.6 (online signer and terminal sums)

import Mathlib

namespace OnlineSteinitz.Reduction

/-! §2.1–2.2, pp.5–6: a fixed tape and the proposed-sign history represent
a persistent online state. Quota routing statistics can be reconstructed from
this history and the node capacity; no future input is available. -/
abbrev ProposalHistory (E : Type*) := List (E × Bool)

abbrev Signer (E Ω : Type*) := Ω → ProposalHistory E → E → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

def signHistory {E Ω : Type*} (rule : Signer E Ω) (ω : Ω) (xs : List E) :
    ProposalHistory E :=
  xs.foldl (fun h x => h ++ [(x, rule ω h x)]) []

def MeasurableSigner {E Ω : Type*} [MeasurableSpace Ω] (rule : Signer E Ω) : Prop :=
  ∀ h x, Measurable (fun ω => rule ω h x)

noncomputable def signedVector {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : ProposalHistory E) : E :=
  (h.map (fun e => sign e.2 • e.1)).sum

def signedCount {E : Type*} (h : ProposalHistory E) : ℝ :=
  (h.map (fun e => sign e.2)).sum

end OnlineSteinitz.Reduction


