-- Prove2me | Definitions.Def_MultiThinkCoT_IsStrictAdversary
-- name    : MultiThinkCoT_IsStrictAdversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:09.241044+00:00
-- url     : https://prove2.me/theorems/153dc0d8-bcbf-466c-8416-0ed62686891f
-- title:
--   Adversaries of the active and adaptive protocol (Definition 2.3) and of the relaxed protocol
-- statement:
--   In the **active and adaptive collection protocol**, the learner holds the training set $S_{\mathrm{e2e}}$ with inputs $x^{(1)},\dots,x^{(m)}$ and target $h^\star\in\mathcal F^{\mathrm{e2e}\text{-}T}$. In each round $k$ it selects a subset $S_k\subseteq[m]$; the adversary then chooses a source $f_k\in\mathcal F$ with
--
--   $$
--   f_k^{\mathrm{e2e}\text{-}T}\equiv h^\star\quad\text{on }\mathcal X,
--   $$
--
--   and reveals the CoTs $f_k^{\mathrm{CoT}\text{-}T}(x^{(i)})$, $i\in S_k$. The choice may depend on the history $S_1,\dots,S_{k-1},f_1,\dots,f_{k-1}$ and on the current subset $S_k$. In the **relaxed protocol** the adversary chooses $f_k$ before observing $S_k$.
--
--   A **strict adversary** for $h^\star$ is a strategy mapping the inputs, the history and the current subset to a source in $\mathcal F$ that realizes $h^\star$ on all of $\mathcal X$; a **relaxed adversary** maps the inputs and the history alone.
--
--   These are the adversaries against which Theorem 7 holds.
--
--   **Formalization Note** Strategies are deterministic functions; a randomized adversary is a mixture of deterministic ones, and the theorems quantify over all strategies. The history is the list of earlier pairs $(S_j,f_j)$, oldest first. The strategy sees the drawn inputs (the labels are $h^\star$ of them).
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Definition 2.3, pp.8–9 (PDF pp.8–9); relaxed protocol, Theorem 7, p.25

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e

namespace MultiThinkCoT

/-!
# Adversaries of the active and adaptive protocol (Definition 2.3) and of the relaxed protocol

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers*,
arXiv:2604.24737 (held version, sha256 e663a640…), Definition 2.3, pp.8–9 (PDF pp.8–9);
relaxed protocol, Theorem 7, p.25.

In round `k` the learner selects `S_k ⊆ [m]`; "the adversary then chooses a source `f_k ∈ F`
such that `f_k^{e2e-T} ≡ h⋆` … The choice can depend on the entire history
`S_1, …, S_{k−1}, f_1, …, f_{k−1}`, as well as the current subset `S_k`." In the relaxed
protocol "the adversary chooses `f_k` before observing the subset `S_k`".

**Formalization Note.**
* A strict adversary is a deterministic strategy that sees the drawn inputs `x(1), …, x(m)`,
  the history (the list of earlier pairs `(S_j, f_j)`, oldest first) and the current subset, and
  returns a generator. A relaxed adversary sees the inputs and the history only. A randomized
  adversary is a mixture of deterministic ones, and the theorems quantify over all of them.
* `f_k^{e2e-T} ≡ h⋆` is agreement at every point of the domain `X`, required for every input of
  the strategy.
-/

/-- The history of the protocol: the earlier rounds' subsets and sources, oldest first. -/
abbrev History (m : ℕ) : Type := List (Finset (Fin m) × Gen)

/-- Definition 2.3: `A` is an adversary of the active and adaptive protocol for target `hstar`:
each choice, made after seeing the inputs, the history and the current subset, lies in `F` and
realizes `hstar` end to end on all of `X`. -/
def IsStrictAdversary (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (hstar : X → Bool) {m : ℕ}
    (A : (Fin m → X) → History m → Finset (Fin m) → Gen) : Prop :=
  ∀ xs hist S, A xs hist S ∈ F ∧ ∀ x : X, e2e (A xs hist S) T x = hstar x

/-- The relaxed protocol (Theorem 7, p.25): the source is chosen from the inputs and the history,
before the current subset is seen. -/
def IsRelaxedAdversary (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (hstar : X → Bool) {m : ℕ}
    (R : (Fin m → X) → History m → Gen) : Prop :=
  ∀ xs hist, R xs hist ∈ F ∧ ∀ x : X, e2e (R xs hist) T x = hstar x

end MultiThinkCoT


