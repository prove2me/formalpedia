-- Prove2me | Definitions.Def_NondualOpt_transcript
-- name    : NondualOpt_transcript
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:51.496775+00:00
-- url     : https://prove2.me/theorems/5857d9d0-bd9e-444a-b946-d034fe394f6b
-- title:
--   The transcript of an algorithm run against an oracle
-- statement:
--   Given an algorithm $A$, an objective $f$ and an adaptive oracle $O$, the **transcript** lists the answers of the run: at round $t$ the algorithm queries $x_t=A_t(\text{answers before }t)$ and receives $(f(x_t),\,O_t(\text{answers before }t,\,x_t))$. The algorithm's output is $\hat x_T=A_{\mathrm{out}}(\text{transcript})$.
--
--   **Formalization Note** Defined by recursion on the number $n\le T$ of rounds played; each query sees only the answers before it. The full transcript is the case $n=T$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, §2, (4), p.7

import Mathlib
import Definitions.Def_NondualOpt_FOAlgorithm

open scoped ENNReal

namespace NondualOpt

/-- The first `n` oracle answers when algorithm `A` runs on `f` against oracle `O`: the query at
round `t < n` is `x_t = A.query t (answers before t)` and the answer is `(f(x_t), O t (answers
before t) x_t)`. The full transcript is `transcript A f O T le_rfl`, and the algorithm's output
is `A.output (transcript A f O T le_rfl)`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, §2, (4), p.7.

**Formalization Note.** Defined by recursion on `n`; each query sees only the answers before it.
Rounds are indexed from `0`. -/
def transcript {d T : ℕ} {p : ℝ≥0∞} (A : FOAlgorithm d T p) (f : (Fin d → ℝ) → ℝ)
    (O : (t : Fin T) → (Fin t → ℝ × (Fin d → ℝ)) → (Fin d → ℝ) → (Fin d → ℝ)) :
    (n : ℕ) → n ≤ T → (Fin n → ℝ × (Fin d → ℝ))
  | 0, _ => Fin.elim0
  | n + 1, hn =>
    let past := transcript A f O n (Nat.le_of_succ_le hn)
    let x := A.query ⟨n, hn⟩ past
    Fin.snoc (α := fun _ => ℝ × (Fin d → ℝ)) past (f x, O ⟨n, hn⟩ past x)

end NondualOpt


