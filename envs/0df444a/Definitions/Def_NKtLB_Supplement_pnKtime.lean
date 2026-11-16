-- Prove2me | Definitions.Def_NKtLB_Supplement_pnKtime
-- name    : NKtLB_Supplement_pnKtime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:21:05.308644+00:00
-- url     : https://prove2.me/theorems/3af720db-8c92-4809-801f-302ba5006011
-- title:
--   $pnK^{t,O}_\lambda(x\mid y)$ — probabilistic nondeterministic time-bounded complexity (Definition 21)
-- statement:
--   For $\lambda\in[0,1]$ and $t\in\mathbb N$,
--   $$
--   pnK^{t}_\lambda(x\mid y)=\min\Bigl\{\,s\in\mathbb N : \Pr_{r\sim\{0,1\}^t}\bigl[nK^t(x\mid y;r)\le s\bigr]\ge\lambda\Bigr\},
--   $$
--   where $nK^t$ is the nondeterministic time-bounded complexity of Definition 17 (base mission). It appears in Theorem 55.
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). Inner measure `NKtLB.nKtime` without query bound; values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 21, p.24

import Mathlib
import Definitions.Def_NKtLB_nKtime
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`pnK^t_λ(x | y)`, probabilistic nondeterministic `t`-time-bounded Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Definition 21, p.24), in its "equivalently" form: "`pnK^t_λ(x | y) ≜ min { s ∈ ℕ : Pr_{r∼{0,1}^t}
[nK^t(x | y; r) ≤ s] ≥ λ }`."

**Formalization Note.** The inner measure is the base `nKtime U O ⊤ t x y r` (Definition 17, no
query bound). Value in `ℕ∞`. -/
noncomputable def pnKtime (U : Machine) (O : Set (List Bool)) (lam : ℝ) (t : ℕ) (x y : List Bool) :
    ℕ∞ :=
  ⨅ (s : ℕ) (_ : lam ≤ prob t (fun r => nKtime U O ⊤ t x y r ≤ (s : ℕ∞))), (s : ℕ∞)

end NKtLB.Supplement


