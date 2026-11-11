-- Prove2me | Definitions.Def_DirectedTreeCovers_Strong_Hierarchy
-- name    : DirectedTreeCovers_Strong_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:34.780182+00:00
-- url     : https://prove2.me/theorems/6cb6dd8c-e7fe-4064-8645-dc20ad63b491
-- title:
--   Unforced independent Bernoulli hierarchy
-- statement:
--   For a finite vertex set of size $n$ and an integer $k\ge1$, put $q=n^{-1/k}$. Independently sample a Bernoulli coin of success probability $q$ at each vertex and each of the $k-1$ intermediate transitions. Let $A_0=V$, let $A_i$ contain the vertices whose first $i$ coins succeeded, and set $A_k=\varnothing$. Level-$i$ centers are $A_i\setminus A_{i+1}$.
--
--   $$\mathbb P(\text{all specified coin outcomes})=\prod_{(j,v)}q^{\mathbf1_{\text{success}}}(1-q)^{\mathbf1_{\text{failure}}}.$$
--
--   The finite product measure has total mass one. No distinguished vertex is retained forcibly, and no conditioning excludes empty top levels. This is the common sampling law for the entire construction.
--
--   **Formalization Note** The rate is clipped to $[0,1]$ solely to totalize invalid inputs: for $n\ge1,k\ge1$ clipping changes nothing. With $V=\varnothing$ there are no coins. With $k=1$ there are no intermediate transitions. The probability-measure instance is supplied by the library's finite-product construction.
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, §4.1, printed p.12 (PDF p.13); §5.1 and Algorithm 3 lines 1–4, printed pp.16–17 (PDF pp.17–18)

import Mathlib

noncomputable section

namespace DirectedTreeCovers.Strong

open scoped Classical
open MeasureTheory ProbabilityTheory

/-- Independent coins for the k-1 sampled transitions, one per vertex per level.
No extra coin is needed for A_0 = V or A_k = empty. -/
abbrev Coins (V : Type) (k : ℕ) := (Fin (k - 1) × V) → Bool

/-- Source rate n^(-1/k). Clipping only totalizes out-of-domain inputs: for n ≥ 1,
k ≥ 1 the unclipped expression already lies in [0,1]. Empty V has no coins. -/
def samplingRate (V : Type) [Fintype V] (k : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 ((Fintype.card V : ℝ) ^ (-(1 / (k : ℝ))))),
    le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Finite product Bernoulli law. In particular the top sampled set may be empty.
Section 5.1 / Algorithm 3, printed pp.16-17 / PDF pp.17-18. -/
def hierarchyLaw (V : Type) [Fintype V] (k : ℕ) : Measure (Coins V k) :=
  Measure.pi fun _ : Fin (k - 1) × V => bernoulliMeasure true false (samplingRate V k)

/-- A structural library instance: the finite product of probability measures has mass one. -/
instance hierarchyLaw_probability (V : Type) [Fintype V] (k : ℕ) :
    IsProbabilityMeasure (hierarchyLaw V k) := by
  unfold hierarchyLaw
  infer_instance

/-- A_i consists of vertices whose first i coins were all successes, with A_k empty.
Unobserved coins remain independent; no distinguished vertex is forced into a level. -/
def sampledLevel {V : Type} [Fintype V] (k : ℕ) (ω : Coins V k) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v => i < k ∧ ∀ j : Fin (k - 1), j.val < i → ω (j, v) = true

def centers {V : Type} [Fintype V] (k : ℕ) (ω : Coins V k) (i : ℕ) : Finset V :=
  sampledLevel k ω i \ sampledLevel k ω (i + 1)

end DirectedTreeCovers.Strong


