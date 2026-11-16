-- Prove2me | Definitions.Def_NKtLB_Supplement_pKtime
-- name    : NKtLB_Supplement_pKtime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:19:01.736302+00:00
-- url     : https://prove2.me/theorems/9b68a7fa-9f28-49dc-b5ab-c106cf7694d1
-- title:
--   $pK^{t,O}_\lambda(x\mid y)$ — probabilistic time-bounded Kolmogorov complexity (Definition 15)
-- statement:
--   For $\lambda\in[0,1]$ and $t\in\mathbb N$,
--   $$
--   pK^{t}_\lambda(x\mid y)=\min\Bigl\{\,s\in\mathbb N : \Pr_{r\sim\{0,1\}^t}\bigl[K^t(x\mid y;r)\le s\bigr]\ge\lambda\Bigr\}.
--   $$
--   Here the random string is fixed first and the program may depend on it: $x$ has $pK^t$ complexity at most $s$ if, for a $\lambda$-fraction of the random strings $r$, some program of length at most $s$ prints $x$ from $(y;r)$ within $t$ steps.
--
--   It appears in the semi-symmetry-of-information Theorems 55 and 57.
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). The paper's second ('equivalently') form is used; values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 15, p.23

import Mathlib
import Definitions.Def_NKtLB_Supplement_Ktime
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`pK^t_λ(x | y)`, probabilistic `t`-time-bounded Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Definition 15,
p.23), in its "equivalently" form: "`pK^t_λ(x | y) ≜ min { s ∈ ℕ : Pr_{r∼{0,1}^t}[K^t(x | y; r) ≤ s]
≥ λ }`."

**Formalization Note.** The inner measure is `Ktime` (Definition 11) with the same oracle. Value in
`ℕ∞` (`⊤` when no `s` qualifies). The first form of Definition 15 writes `∃Π ∈ {0,1}^s`; the paper
states the two forms are equivalent, and the second (`≤ s`) is used here, as in Definition 21. -/
noncomputable def pKtime (U : Machine) (O : Set (List Bool)) (lam : ℝ) (t : ℕ) (x y : List Bool) :
    ℕ∞ :=
  ⨅ (s : ℕ) (_ : lam ≤ prob t (fun r => Ktime U O t x y r ≤ (s : ℕ∞))), (s : ℕ∞)

end NKtLB.Supplement


