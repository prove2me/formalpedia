-- Prove2me | Definitions.Def_NKtLB_Supplement_rKtime
-- name    : NKtLB_Supplement_rKtime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:18:07.397482+00:00
-- url     : https://prove2.me/theorems/fb67b51a-44a6-48ff-9491-8f469b54ab08
-- title:
--   $rK^{t,O}_\lambda(x\mid y)$ — randomized time-bounded Kolmogorov complexity (Definition 13)
-- statement:
--   For $\lambda\in[0,1]$ and $t\in\mathbb N$,
--   $$
--   rK^{t,O}_\lambda(x\mid y)=\min_{\Pi}\Bigl\{\,|\Pi| : \Pr_{r\sim\{0,1\}^t}\bigl[\Pi^O(y;\varepsilon;r)\text{ outputs }x\text{ within }t\text{ steps}\bigr]\ge\lambda\Bigr\}.
--   $$
--   The subscript is $2/3$ when omitted. A program qualifies if, for a $\lambda$-fraction of the random strings of length $t$, it prints $x$ within $t$ steps.
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). The random string sits on the randomness tape; values in `ℕ∞`. This is the paper's Definition 13, distinct from the base mission's `NKtLB.rK` (Definition 99).
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 13, p.22

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`rK^{t,O}_λ(x | y)`, randomized `t`-time-bounded Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Definition 13,
p.22): "`rK^{t,O}_λ(x | y) = min_{Π ∈ {0,1}^*} { |Π| : Pr_{r∼{0,1}^t}[Π(y; ε; r) outputs x within t
steps] ≥ λ }`." The oracle version is the one the paper says "can easily be generalized" (p.22):
the oracle `O` is given to the universal machine.

**Formalization Note.** `lam` is the paper's `λ` (`2/3` when omitted, p.22). The random string has
length exactly `t` and sits on the randomness tape; the guess tape is empty. Value in `ℕ∞`. This is
the paper's Definition 13, not the base `rK` (Definition 99, which has a separate random-string
length and a query bound). -/
noncomputable def rKtime (U : Machine) (O : Set (List Bool)) (lam : ℝ) (t : ℕ) (x y : List Bool) :
    ℕ∞ :=
  ⨅ (p : List Bool) (_ : lam ≤ prob t (fun r => U.HaltsWith O ⟨p, y, [], r⟩ t (bitsSym x))),
    (p.length : ℕ∞)

end NKtLB.Supplement


