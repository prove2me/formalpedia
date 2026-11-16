-- Prove2me | Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Observation
-- name    : LocalProbeMIS871_Greedy_Supplement_Observation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:02:53.715865+00:00
-- url     : https://prove2.me/theorems/7f621f69-584a-4546-abb1-a05a8b9cf49a
-- title:
--   §4.2–§4.3 — Shared error constant, observations and total variation
-- statement:
--   Fix the source-derived witness $c_*=1/2304$ for the constant in the selection error $\eta_{c_*}(\Delta,m)$. For a stateless LCA with tape law $\mu$, its membership probability under $D_i$ is the uniform finite average of
--
--   $$\mu\{r:A(G_i,L_i,v_i;r)=1\}$$
--
--   over the independent construction seeds, including the query uniformly drawn from hidden $A$. Tape laws are probability measures in every use.
--
--   A deterministic adaptive procedure may use arbitrary free parameters $n,\Delta,k,\ell,m$ and any output type. It chooses its next action from the root and observed history alone; local divergence is allowed. A $q$-bounded procedure requests no further probe after $q$ replies. Define $T_i$ to contain the query label, every probe and reply, and the terminal output if present, by observing its run through the local action immediately after probe $q$. Earlier terminal states are absorbing. For these finite graph experiments, define
--
--   $$d_{\rm TV}(T_0,T_1)=\sup_E|\Pr(T_0\in E)-\Pr(T_1\in E)|,\qquad
--   \rho_{\Delta,q}(m)=\min\{1,K_\Delta(q+1)^2/m\}.$$
--
--   The same procedure and the same free parameters are used on both distributions. Neither correctness nor a favorable coupling is part of this definition. The variation distance has the source's event-supremum normalization in $[0,1]$.
--
--   These definitions separate the observation available to an algorithm from latent construction data and the auxiliary infinite explorations used only in the proof.
--
--   **Formalization Note** A bounded procedure is normalized to stop or diverge after every history of length at least $q$; arbitrary values on unreachable histories can always be changed to meet this convention. This changes no $q$-probe interaction. The supremum is over all events in a finite-support law, so the set is nonempty and bounded by one. No default value for an unbounded real supremum is used. The constant witness follows from $(N/12)^2/(8h)\ge N/2304$ when $h\le2N$ in Eq. (40).
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), pp. 26–27, PDF pp. 28–29, §4.2–§4.3, Eqs. (40)–(44)

import Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Configuration

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
universe uObservation

namespace LocalProbeMIS871.Greedy.Supplement

/-- Eq.(40), using h ≤ 2N: (N/12)^2/(8h) ≥ N/2304. -/
def cStar : ℝ := 1 / 2304

/-- Uniform finite graph sample, independently averaged against an arbitrary tape law. -/
def membershipProbability {Ω : Type uObservation} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Algorithm Ω) (one : Bool) (Δ m : ℕ) : ℝ :=
  (∑ s : Seed Δ m,
    (μ {r | answersYes A Δ (sampleLists one s) (sampleRoot s) r}).toReal) /
      (Fintype.card (Seed Δ m) : ℝ)

/-- A bounded procedure has arbitrary output type and sees only the root and transcript.
Its closure may use all the free parameters n, Δ, k, ℓ, m. -/
abbrev Procedure (n : ℕ) (O : Type*) := Fin n → History n → Option (O ⊕ Probe n)

def BoundedProcedure {n : ℕ} {O : Type*} (B : Procedure n O) (q : ℕ) : Prop :=
  ∀ v h, q ≤ h.length → B v h = none ∨ ∃ o, B v h = some (Sum.inl o)

/-- After q probes the next local action is observed, including the final output.
Earlier termination is absorbing. -/
def transcript {Δ m : ℕ} {O : Type*} (B : Procedure (graphSize Δ m) O)
    (q : ℕ) (one : Bool) (s : Seed Δ m) : Fin (graphSize Δ m) × State (graphSize Δ m) O :=
  (sampleRoot s, run (oracle (sampleLists one s))
    (B (sampleRoot s)) (q + 1))

/-- Event-supremum normalization of total variation. These are genuine finite
probabilities in [0,1]; the supremum set is nonempty and bounded by one. -/
def transcriptTV {Δ m : ℕ} {O : Type*} (B : Procedure (graphSize Δ m) O) (q : ℕ) : ℝ :=
  ⨆ E : Set (Fin (graphSize Δ m) × State (graphSize Δ m) O),
    |finiteProb (fun s : Seed Δ m => transcript B q false s ∈ E) -
      finiteProb (fun s : Seed Δ m => transcript B q true s ∈ E)|

def rho (K : ℕ → ℝ) (Δ q m : ℕ) : ℝ :=
  min 1 (K Δ * ((q : ℝ) + 1) ^ (2 : ℕ) / (m : ℝ))

end LocalProbeMIS871.Greedy.Supplement


