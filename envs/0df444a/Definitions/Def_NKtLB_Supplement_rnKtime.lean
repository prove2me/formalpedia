-- Prove2me | Definitions.Def_NKtLB_Supplement_rnKtime
-- name    : NKtLB_Supplement_rnKtime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:20:05.137199+00:00
-- url     : https://prove2.me/theorems/2607eedc-2147-499a-8d66-7294ae674e45
-- title:
--   $rnK^{t,O}_\lambda(x\mid y)$ — randomized nondeterministic time-bounded complexity (Definition 19)
-- statement:
--   For $\lambda\in[0,1]$ and $t\in\mathbb N$,
--   $$
--   rnK^{t}_\lambda(x\mid y)=\min_{\Pi}\Bigl\{\,|\Pi| : \Pr_{r\sim\{0,1\}^t}\Bigl[\begin{array}{l}\forall w\in\{0,1\}^t,\ \Pi(y;w;r)\text{ outputs }x\text{ or }\bot\text{ in }t\text{ steps};\\ \exists w\in\{0,1\}^t,\ \Pi(y;w;r)\text{ outputs }x\text{ in }t\text{ steps}\end{array}\Bigr]\ge\lambda\Bigr\}.
--   $$
--   For most random strings, the program must be a single-valued nondeterministic description of $x$: every guess yields $x$ or the rejection symbol $\bot$, and some guess yields $x$.
--
--   It appears in Theorem 57.
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). The event is the base `NKtLB.NondetOutputs` without query bound; values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 19, p.23

import Mathlib
import Definitions.Def_NKtLB_NondetOutputs
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`rnK^t_λ(x | y)`, randomized nondeterministic `t`-time-bounded Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Definition 19, p.23): "`rnK^t_λ(x | y) ≜ min_{Π ∈ {0,1}^*} { |Π| : Pr_{r∼{0,1}^t}[∀w ∈ {0,1}^t,
Π(y; w; r) outputs x or ⊥ in t steps; ∃w ∈ {0,1}^t, Π(y; w; r) outputs x in t steps] ≥ λ }`."

**Formalization Note.** The event inside the probability is the base `NondetOutputs U O ⊤ p y r t x`
(no query bound). Random string of length `t`. Value in `ℕ∞`. -/
noncomputable def rnKtime (U : Machine) (O : Set (List Bool)) (lam : ℝ) (t : ℕ) (x y : List Bool) :
    ℕ∞ :=
  ⨅ (p : List Bool) (_ : lam ≤ prob t (fun r => NondetOutputs U O ⊤ p y r t x)), (p.length : ℕ∞)

end NKtLB.Supplement


