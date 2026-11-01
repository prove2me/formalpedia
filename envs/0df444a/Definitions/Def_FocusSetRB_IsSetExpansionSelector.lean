-- Prove2me | Definitions.Def_FocusSetRB_IsSetExpansionSelector
-- name    : FocusSetRB_IsSetExpansionSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:28.657287+00:00
-- url     : https://prove2.me/theorems/0658212d-640f-4519-a601-0748fe7d6503
-- title:
--   The set-expansion focus-set update (Algorithm 2, lines 2–5)
-- statement:
--   The **set-expansion policy** is the focus-set policy whose update is (Algorithm 2, lines 2–5): given $X_t=x$ and $D_{t-1}$,
--
--   1. if $\delta(x,D_{t-1})>0$, let $D_t$ be any set with the largest $m(D_t)$ such that $D_t\supseteq D_{t-1}$ and $\delta(x,D_t)\ge0$;
--   2. otherwise, let $D_t$ be any set with the largest $m(D_t)$ such that $D_t\subseteq D_{t-1}$ and $\delta(x,D_t)\ge0$.
--
--   The initial focus set is $D_{-1}=\emptyset$. The slack condition $\delta(x,D_t)\ge0$ guarantees that most arms of $D_t$ can follow $\bar\pi^*$ within the budget, and the update keeps $D_t$ nested with $D_{t-1}$.
--
--   **Formalization Note** The update may randomize among the maximizers; "largest $m(D_t)$" means largest cardinality among the admissible sets of the branch. Both branches have an admissible set: $D_{t-1}$ in the first, and $\emptyset$, whose slack is $\beta>0$, in the second.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Algorithm 2, lines 2–5, p.8

import Mathlib
import Definitions.Def_FocusSetRB_focusLaw

namespace FocusSetRB

variable {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}

/-- The **set-expansion** focus-set update (arXiv:2402.05689v4, Algorithm 2, lines 2–5, p.8):
`sel` is a focus-set update kernel and every focus set `D_t` it can choose from
`(X_t, D_{t−1}) = (x, Dprev)` obeys:
* if `δ(x, Dprev) > 0`: `D_t ⊇ Dprev`, `δ(x, D_t) ≥ 0`, and `D_t` has the largest `m(D_t)`
  among all such sets (line 3);
* otherwise: `D_t ⊆ Dprev`, `δ(x, D_t) ≥ 0`, and `D_t` has the largest `m(D_t)` among all such
  sets (line 5).

**Formalization Note.** "Any set with the largest `m(D_t)`" is: no admissible set of the branch
has larger cardinality; the kernel may randomize among the maximizers. Both branches are
satisfiable: `Dprev` is admissible in the first, and `∅` (slack `β > 0`) in the second. -/
def IsSetExpansionSelector (α : ℝ) (y : S → Bool → ℝ)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ) : Prop :=
  IsSelectorKernel sel ∧
  ∀ x Dprev D, 0 < sel x Dprev D →
    (0 < slack α y x Dprev →
      Dprev ⊆ D ∧ 0 ≤ slack α y x D ∧
        ∀ D' : Finset (Fin N), Dprev ⊆ D' → 0 ≤ slack α y x D' → D'.card ≤ D.card) ∧
    (¬ 0 < slack α y x Dprev →
      D ⊆ Dprev ∧ 0 ≤ slack α y x D ∧
        ∀ D' : Finset (Fin N), D' ⊆ Dprev → 0 ≤ slack α y x D' → D'.card ≤ D.card)

end FocusSetRB


