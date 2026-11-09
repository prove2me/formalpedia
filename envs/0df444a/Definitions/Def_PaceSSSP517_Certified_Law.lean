-- Prove2me | Definitions.Def_PaceSSSP517_Certified_Law
-- name    : PaceSSSP517_Certified_Law
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:00.075453+00:00
-- url     : https://prove2.me/theorems/0cfeff93-b107-4853-a889-74566a448a65
-- title:
--   Conditional independent Bernoulli sampling and the actual finite-horizon law
-- statement:
--   Given the past, sample each edge independently with probability
--
--   $$p_e=\min\{1,s_rq_e/Q\}.$$
--
--   The finite subset law is the product of Bernoulli choices over the distinct edges. The adaptive recursion binds this law to the transition of Algorithm 1 at each successive history. Its projection to the prefix through the first stop is the actual run law. A finite horizon does not force a stop: unfinished runs remain unfinished in this law.
--
--   This construction supplies normalized unconditional probabilities, while retaining the precise conditional sampling kernel for Lemma 3.4. The sample size is random and is not capped or rounded. The total parameter definition additionally clips negative probabilities to zero on invalid states; on every legal prehistory the rate and weights are positive, so this clipping changes nothing. Event probability is a sum of PMF masses in the extended nonnegative reals; it does not use a default Bochner expectation.
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 6, Algorithm 1 line 3; p. 17, Appendix A.3; p. 18, Appendix A.5

import Definitions.Def_PaceSSSP517_Certified_Algorithm

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical

namespace PaceSSSP517.Certified

/-- A total probability parameter. On legal histories it is exactly
min(1, rate*q/Q); the max with 0 only defines unused invalid inputs. -/
noncomputable def inclusion {n : ℕ} (G : WeightedGraph n) (a : State n) (e : Edge n) : ℝ≥0 :=
  ⟨max 0 (min 1 (a.rate * edgeWeight G a e / a.Q)), le_max_left _ _⟩

/-- Independent Bernoulli selections of a list of distinct edges. There is no
sample-size cap, rejection conditioning or rounding of the real sampling rate. -/
noncomputable def sampleEdges {n : ℕ} (p : Edge n → ℝ≥0) (hp : ∀ e, p e ≤ 1) :
    List (Edge n) → PMF (Finset (Edge n))
  | [] => PMF.pure ∅
  | e :: es => (PMF.bernoulli (p e) (hp e)).bind (fun b =>
      (sampleEdges p hp es).map (fun F => if b then insert e F else F))

noncomputable def sampleLaw {n : ℕ} (G : WeightedGraph n) (a : State n) : PMF (Finset (Edge n)) :=
  sampleEdges (inclusion G a) (fun e => by
    change max 0 (min 1 (a.rate * edgeWeight G a e / a.Q)) ≤ (1 : ℝ)
    exact max_le (by norm_num) (min_le_left _ _)) G.edges.toList

/-- The finite adaptive stochastic recursion. Each kernel is recomputed from its
own past, so edges are independent conditional on that past, not across rounds. -/
noncomputable def virtualLaw {n : ℕ} (G : WeightedGraph n) (H : Finset (Edge n))
    (s₀ : Fin n) (k : ℕ) (ε : ℝ) : ℕ → PMF (State n)
  | 0 => PMF.pure (initial G k ε)
  | r + 1 => (virtualLaw G H s₀ k ε r).bind (fun a =>
      (sampleLaw G a).map (advance G H s₀ k ε a))

/-- The actual run law is the absorbing stopped prefix of the virtual recursion.
It includes the terminal Pass A/B and excludes every later virtual update. -/
noncomputable def runLaw {n : ℕ} (G : WeightedGraph n) (H : Finset (Edge n))
    (s₀ : Fin n) (k : ℕ) (ε : ℝ) (horizon : ℕ) : PMF (List (Round n)) :=
  (virtualLaw G H s₀ k ε horizon).map (fun a => execution a.rounds)

/-- PMFs supply normalized probabilities on arbitrary events by summing their
atomic masses. No Bochner integral, default expectation or measurability premise. -/
noncomputable def probability {α : Type*} (p : PMF α) (E : Set α) : ℝ≥0∞ :=
  p.toOuterMeasure E

end PaceSSSP517.Certified


