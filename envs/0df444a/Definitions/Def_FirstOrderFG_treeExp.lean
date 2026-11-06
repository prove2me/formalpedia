-- Prove2me | Definitions.Def_FirstOrderFG_treeExp
-- name    : FirstOrderFG_treeExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:26.652213+00:00
-- url     : https://prove2.me/theorems/d2a23f9f-9ad5-4621-87bb-58c0685f5b73
-- title:
--   Expectation over the finite tree of play sequences
-- statement:
--   All randomness of the algorithms is the sequence of played arms, the arm of each round being drawn from a distribution $\mathrm{play}(h)$ that depends on the history $h$ of earlier arms. For a functional $\Phi$ of histories, the expectation of $\Phi$ after $n$ further rounds, conditional on the history $h$, is defined recursively:
--   $$
--   \mathbb E_h^{(0)}[\Phi]=\Phi(h),\qquad \mathbb E_h^{(n+1)}[\Phi]=\sum_{I}\mathrm{play}(h)(I)\ \mathbb E_{h\cdot I}^{(n)}[\Phi].
--   $$
--
--   **Formalization Note** This is the finite trajectory law of an oblivious adversary, used in place of a filtered probability space; conditioning on a history is evaluation at that history.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Lemma B.1, p.22

import Mathlib

namespace FirstOrderFG

/-- **Expectation over the finite tree of play sequences.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3 (expected regret
`E[·]`, conditional expectations `E_t`, and `E_τ` "conditional on the history before `τ`",
Lemma B.1, p.22).

All randomness of the algorithms is the sequence of played arms `I_t`, drawn from a distribution
`play h` that is a function of the history `h` (the list of earlier arms). `treeExp play n h Φ` is
the expectation of `Φ` evaluated on the history extended by `n` further rounds, conditional on the
history `h`: `treeExp play 0 h Φ = Φ h` and
`treeExp play (n+1) h Φ = ∑_I play h I · treeExp play n (h ++ [I]) Φ`.

**Formalization Note.** This is the finite trajectory law of an oblivious adversary (losses fixed
in advance) in place of a filtered probability space; conditioning on a history is evaluating the
recursion at that history. -/
noncomputable def treeExp {K : ℕ} (play : List (Fin K) → Fin K → ℝ) :
    ℕ → List (Fin K) → (List (Fin K) → ℝ) → ℝ
  | 0, h, Φ => Φ h
  | n + 1, h, Φ => ∑ I, play h I * treeExp play n (h ++ [I]) Φ

end FirstOrderFG


