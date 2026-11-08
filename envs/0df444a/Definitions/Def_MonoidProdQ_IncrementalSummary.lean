-- Prove2me | Definitions.Def_MonoidProdQ_IncrementalSummary
-- name    : MonoidProdQ_IncrementalSummary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:42:56.11902+00:00
-- url     : https://prove2.me/theorems/65db75a7-7ac0-4a45-a5e3-f3906684094b
-- title:
--   Incremental summary (Definition 2)
-- statement:
--   Let $I$ be a finite index set, $\Sigma$ and $O$ finite alphabets and $f$ a function on a promise domain $D\subseteq\Sigma^I$ with values in $O$. An **incremental summary** for $f$ with state set $Q$ consists of
--
--   1. an initial state $q_\emptyset\in Q$;
--   2. for each $i\in I$ an update map $\delta_i:Q\times\Sigma\to Q$;
--   3. a readout map $g:Q\to O$;
--   4. for each input $x\in D$ and revealed index set $T\subseteq I$ a summary state $s_x(T)\in Q$,
--
--   such that, for every $x\in D$,
--
--   $$s_x(\emptyset)=q_\emptyset,\qquad s_x(T\cup\{i\})=\delta_i\big(s_x(T),x_i\big)\ (i\notin T),\qquad f(x)=g\big(s_x(I)\big).$$
--
--   The state depends on the revealed set, not on the order in which it was revealed. Summaries of small essential width yield adversary upper bounds (Theorem 14).
--
--   **Formalization Note** The summary states are given for every word, but only those at inputs of $D$ are constrained. The standing assumptions of Definition 2 (finite $I$, $\Sigma$, $O$, $Q$; $|I|=n\ge1$; $D$ nonempty) are hypotheses of the statements that use summaries.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 2, p.27

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 2, p.27: an incremental summary for a function `f` on the promise domain
`D ⊆ Σ^I`. It has a state set `Q` with a fixed initial state `q∅`, for each `i ∈ I` an update map
`δᵢ : Q × Σ → Q`, a readout map `g : Q → O`, and for each input `x ∈ D` and revealed index set
`T ⊆ I` a summary state `sₓ(T) ∈ Q`, such that
`sₓ(∅) = q∅`, `sₓ(T ∪ {i}) = δᵢ(sₓ(T), xᵢ)` for `i ∉ T`, and `f(x) = g(sₓ(I))`.

**Formalization Note.** `s` is a function on all words; only its values at `x ∈ D` are
constrained (the paper defines `sₓ` for `x ∈ D` only). The standing assumptions of Definition 2
(`I`, `Σ`, `O`, `Q` finite, `|I| = n ≥ 1`, `D` nonempty) are hypotheses of the statements that
use the structure, not fields. -/
structure IncrementalSummary {I Sig Out : Type*} [DecidableEq I] [Fintype I]
    (f : (I → Sig) → Out) (D : Finset (I → Sig)) (Q : Type*) where
  /-- The initial state `q∅`. -/
  q0 : Q
  /-- The update maps `δᵢ : Q × Σ → Q`. -/
  δ : I → Q → Sig → Q
  /-- The readout map `g : Q → O`. -/
  g : Q → Out
  /-- The summary states `sₓ(T)`. -/
  s : (I → Sig) → Finset I → Q
  /-- `sₓ(∅) = q∅`. -/
  s_empty : ∀ x ∈ D, s x ∅ = q0
  /-- `sₓ(T ∪ {i}) = δᵢ(sₓ(T), xᵢ)` for `i ∉ T`. -/
  s_insert : ∀ x ∈ D, ∀ (T : Finset I) (i : I), i ∉ T → s x (insert i T) = δ i (s x T) (x i)
  /-- `f(x) = g(sₓ(I))`. -/
  readout : ∀ x ∈ D, f x = g (s x Finset.univ)

end MonoidProdQ


