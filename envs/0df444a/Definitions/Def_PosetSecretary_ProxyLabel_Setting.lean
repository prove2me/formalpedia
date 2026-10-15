-- Prove2me | Definitions.Def_PosetSecretary_ProxyLabel_Setting
-- name    : PosetSecretary_ProxyLabel_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:45.488851+00:00
-- url     : https://prove2.me/theorems/c6a6385d-0efb-47dd-94e1-1a81a87c9018
-- title:
--   §3.1, §3.3, Definition 3.4, Algorithm 1 — consistent scorings, OPT, and the ProxyLabel run with its selection probabilities and expected score
-- statement:
--   This file fixes the model of the **poset secretary problem** and the algorithm **ProxyLabel** of Salem and Gupta.
--
--   **Elements and scores.** A finite set $C$ of $N$ elements carries a partial order $\preceq$ (the observed ordinal information). A **scoring consistent with the partial order** is a function $w : C \to \mathbb R$ such that
--
--   1. every score is non-negative, $w(a) \ge 0$;
--   2. the scores are pairwise distinct;
--   3. $a \prec b$ implies $w(a) < w(b)$.
--
--   **Offline optimum.** For a selection capacity $k$, the offline optimum is the largest total score of at most $k$ elements,
--   $$\mathrm{OPT} = \max\Big\{\sum_{a \in s} w(a) \;:\; s \subseteq C,\ |s| \le k\Big\}.$$
--   The family of admissible sets contains $\emptyset$, so the maximum is over a nonempty finite family; for $k \ge N$ it is the total score of $C$.
--
--   **ProxyLabel (Algorithm 1).** The elements arrive in a uniformly random order; write $\pi(a) \in \{0, \dots, N-1\}$ for the arrival time of $a$. Each element receives a label $\ell(a) \in \{1, \dots, k\}$, uniformly and independently. A number $m \sim \mathrm{Bin}(N, \omega'/(\omega'+1))$ is drawn, where $\omega' \in \mathbb N$ is the width estimate, and the first $m$ arrivals form the sample $S$. An element $x$ **passes** if no element $b$ that arrived before $x$ and has the same label satisfies $x \prec b$; the earlier elements include sampled ones. An element $a$ is **selected** if it is not sampled, it passes, and no earlier non-sampled element with the same label passes. Thus the set $\mathrm{Alg}$ of selected elements contains, for each label, the first non-sampled element of that label that passes, if there is one.
--
--   **Probabilities.** With $p = \omega'/(\omega'+1)$ and binomial weights $\binom{N}{m} p^m (1-p)^{N-m}$,
--   $$\mathbb P(a \in \mathrm{Alg}) = \sum_{\pi} \sum_{\ell} \sum_{m=0}^{N} \frac{1}{N!}\cdot\frac{1}{k^N}\cdot\binom{N}{m} p^m (1-p)^{N-m}\,\mathbf 1[a \in \mathrm{Alg}(\pi, \ell, m)],$$
--   and $\mathbb E[w(\mathrm{Alg})]$ is the same average of $\sum_{a \in \mathrm{Alg}(\pi,\ell,m)} w(a)$. Finally, the probability that $a$ is the highest-scored element of its label class is the fraction of labellings $\ell$ under which no element of larger score shares the label of $a$.
--
--   These objects are the vocabulary of Proposition 5.2, Corollary 5.1 and the milestones of the proof.
--
--   **Formalization Note** Elements form a finite type `α` with a `PartialOrder`; $N$ is its cardinality and $\omega$ is the published `AppliedComb.Posets.width α`, the largest size of an antichain. Arrival orders are bijections `α ≃ Fin N`, labellings are functions `α → Fin k`. Assigning labels "as the elements arrive" gives the same distribution as a uniform function, independent of the arrival order. Probabilities and expectations are written as explicit finite averages. Decidability is classical (`open Classical`) in the filters defining the selected set and the label-maximum event.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), §3.1 p. 7, §3.3 p. 11, Definition 3.4 p. 12, Algorithm 1 p. 16

import Mathlib
import Definitions.Def_AppliedComb_Posets_width

namespace PosetSecretary.ProxyLabel

/-- A scoring `w : α → ℝ` consistent with the partial order on `α` (Salem & Gupta, §3.1, p. 7;
§3.3, p. 11): scores are non-negative, distinct, and `a ≺ b` implies `w a < w b`. -/
def IsConsistentScoring {α : Type*} [PartialOrder α] (w : α → ℝ) : Prop :=
  (∀ a, 0 ≤ w a) ∧ Function.Injective w ∧ ∀ a b, a < b → w a < w b

/-- `OPT`, the offline optimum of Definition 3.4 (p. 12): the largest total score
`∑_{a ∈ s} w a` over sets `s` of at most `k` elements. The family of such sets contains `∅`,
so the maximum is over a nonempty finite family. -/
noncomputable def opt {α : Type*} [Fintype α] (w : α → ℝ) (k : ℕ) : ℝ :=
  ((Finset.univ : Finset α).powerset.filter (fun s : Finset α => s.card ≤ k)).sup'
    ⟨∅, by simp⟩ (fun s => ∑ a ∈ s, w a)

/-- Algorithm 1, line 4, first test: under the arrival order `pos` (element `x` is the
`pos x`-th arrival) and the labelling `ℓ`, the element `x` is maximal with respect to the
previously seen elements with its label, i.e. no earlier arrival `b` with `ℓ b = ℓ x`
satisfies `x < b`. Earlier arrivals include sampled ones. -/
def passes {α : Type*} [PartialOrder α] [Fintype α] {k : ℕ}
    (pos : α ≃ Fin (Fintype.card α)) (ℓ : α → Fin k) (x : α) : Prop :=
  ∀ b, ℓ b = ℓ x → pos b < pos x → ¬ x < b

open Classical in
/-- The output `Alg` of ProxyLabel (Algorithm 1, p. 16) for the arrival order `pos`, the
labelling `ℓ` and the sample size `m`. The sample `S` is the first `m` arrivals
(`pos a < m`). An element `a` is selected iff it is not sampled, passes the maximality test of
line 4, and no earlier non-sampled element with the same label passed that test (such an
element would have been selected, so "no `ℓ`-labeled element has been selected" would fail).
At most one element per label is selected: the first non-sampled one that passes. -/
noncomputable def selected {α : Type*} [PartialOrder α] [Fintype α] {k : ℕ}
    (pos : α ≃ Fin (Fintype.card α)) (ℓ : α → Fin k) (m : ℕ) : Finset α :=
  Finset.univ.filter (fun a =>
    m ≤ (pos a : ℕ) ∧ passes pos ℓ a ∧
      ∀ b, ℓ b = ℓ a → m ≤ (pos b : ℕ) → pos b < pos a → ¬ passes pos ℓ b)

/-- The binomial probability `P(Bin(N, p) = m) = (N choose m) p^m (1 - p)^(N - m)`. -/
noncomputable def binomWeight (N m : ℕ) (p : ℝ) : ℝ :=
  (N.choose m : ℝ) * p ^ m * (1 - p) ^ (N - m)

/-- The sampling probability `ω′/(ω′+1)` of Algorithm 1, line 2. -/
noncomputable def sampleProb (ω' : ℕ) : ℝ :=
  (ω' : ℝ) / (ω' + 1)

/-- `P(a ∈ Alg)` for ProxyLabel with selection capacity `k` and width estimate `ω'`: the
average over uniformly random arrival orders (weight `1/N!`), uniformly random labellings
`α → Fin k` (weight `1/k^N`), and `m ∼ Bin(N, ω′/(ω′+1))` (binomial weight), of the indicator
that `a` is selected. -/
noncomputable def selectionProb {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (k ω' : ℕ) (a : α) : ℝ :=
  ∑ pos : α ≃ Fin (Fintype.card α), ∑ ℓ : α → Fin k, ∑ m ∈ Finset.range (Fintype.card α + 1),
    (1 / ((Fintype.card α).factorial : ℝ)) * (1 / (k : ℝ) ^ Fintype.card α) *
      binomWeight (Fintype.card α) m (sampleProb ω') *
        (if a ∈ selected pos ℓ m then 1 else 0)

/-- `E[w(Alg)]` for ProxyLabel with selection capacity `k` and width estimate `ω'`: the same
average as in `selectionProb` of the total score `∑_{a ∈ Alg} w a` of the selected set. -/
noncomputable def proxyLabelValue {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (k ω' : ℕ) : ℝ :=
  ∑ pos : α ≃ Fin (Fintype.card α), ∑ ℓ : α → Fin k, ∑ m ∈ Finset.range (Fintype.card α + 1),
    (1 / ((Fintype.card α).factorial : ℝ)) * (1 / (k : ℝ) ^ Fintype.card α) *
      binomWeight (Fintype.card α) m (sampleProb ω') *
        ∑ a ∈ selected pos ℓ m, w a

open Classical in
/-- The probability, over a uniformly random labelling `ℓ : α → Fin k`, that `a` has the
largest score among the elements sharing its label: no element of larger score receives the
label of `a`. -/
noncomputable def labelMaxProb {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (k : ℕ) (a : α) : ℝ :=
  ((Finset.univ.filter (fun ℓ : α → Fin k => ∀ b, w a < w b → ℓ b ≠ ℓ a)).card : ℝ) /
    (k : ℝ) ^ Fintype.card α

end PosetSecretary.ProxyLabel


