-- Prove2me | Definitions.Def_HighConfRobust_Supplement_IsAdaptiveAdversary
-- name    : HighConfRobust_Supplement_IsAdaptiveAdversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:42:22.700593+00:00
-- url     : https://prove2.me/theorems/c12c63d0-ca11-49d1-a40a-4e23556e8ab2
-- title:
--   Adaptive $\varepsilon$-adversary
-- statement:
--   Let $\mathcal X$ be a sample space and $m\in\mathbb N$. An **adaptive $\varepsilon$-adversary** on $m$ samples is a randomized map $T:\mathcal X^m\times\Omega_T\to\mathcal X^m$ that inspects the whole clean dataset $S=(x_1,\dots,x_m)$ and returns a dataset $T(S,\omega)$ of the same size such that, for every $S$ and every seed $\omega$, at least $(1-\varepsilon)m$ of the elements of $T(S,\omega)$ overlap with those of $S$ as multisets. The corrupted dataset may be reordered, so the overlap is counted up to a permutation:
--
--   $$
--   \forall S,\ \forall\omega,\quad \exists\sigma\in\mathfrak S_m:\quad \#\{i\in[m] : T(S,\omega)_i=x_{\sigma(i)}\}\ \ge\ (1-\varepsilon)\,m .
--   $$
--
--   Such an adversary may replace up to an $\varepsilon$ fraction of the samples by arbitrary points chosen after seeing the data, and may shuffle the result. It is the corruption model of strong (adaptive) contamination.
--
--   **Formalization Note** A multiset overlap of size $k$ is the same as a permutation matching $k$ positions. The seed law and the measurability of $T$ are fixed where adversaries are quantified (adaptive robustness), not in this predicate.
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Definition 1.5 and footnote 2, p.5

import Mathlib

namespace HighConfRobust.Supplement

/-- An **adaptive `ε`-adversary** on `m` samples (Definition 1.5, p.5): a randomized map
`T : (Fin m → X) → Ωt → (Fin m → X)` that sees the whole clean dataset `S` and returns a dataset
`T S ω` of the same size such that, for every dataset and every seed, at least `(1 − ε)·m` of its
elements overlap with those of `S` as multisets. The output may be reordered (footnote 2), so the
overlap is counted after a permutation: some `σ` matches at least `(1 − ε)·m` positions,
`T S ω i = S (σ i)`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Definition 1.5 and footnote 2, p.5.

**Formalization Note** The multiset overlap of `T` and `S` is at least `k` iff some permutation `σ`
of the indices matches at least `k` positions (a partial matching of `k` equal entries extends to a
permutation of `Fin m`). The count is `Set.ncard` of the matched positions. The seed law and the
measurability of `T` are not part of this predicate; they are fixed where adversaries are
quantified (`IsAdaptiveRobust`). -/
def IsAdaptiveAdversary {X Ωt : Type*} {m : ℕ} (ε : ℝ)
    (T : (Fin m → X) → Ωt → (Fin m → X)) : Prop :=
  ∀ (S : Fin m → X) (ω : Ωt), ∃ σ : Equiv.Perm (Fin m),
    (1 - ε) * (m : ℝ) ≤ ({i : Fin m | T S ω i = S (σ i)}.ncard : ℝ)

end HighConfRobust.Supplement


