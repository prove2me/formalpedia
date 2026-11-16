-- Prove2me | Definitions.Def_NKtLB_Supplement_Ktime
-- name    : NKtLB_Supplement_Ktime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:17:17.358175+00:00
-- url     : https://prove2.me/theorems/d8ecab7f-bb0b-4d16-9ffc-7af65c49b78a
-- title:
--   $K^{t,O}(x\mid y;r)$ — time-bounded Kolmogorov complexity (Definition 11)
-- statement:
--   For strings $x,y,r$, a time bound $t\in\mathbb N$ and an oracle $O$, the **$t$-time-bounded Kolmogorov complexity** of $x$ given $(y;r)$ is
--   $$
--   K^{t,O}(x\mid y;r)=\min_{\Pi\in\{0,1\}^*}\bigl\{\,|\Pi| : \Pi^O(y;\varepsilon;r)\text{ outputs }x\text{ within }t\text{ steps}\bigr\},
--   $$
--   i.e. the length of a shortest program that, run by the universal machine $U$ with auxiliary string $y$, empty guess tape and random string $r$, halts within $t$ steps with output $x$. $K^{t,O}(x\mid y)=K^{t,O}(x\mid y;\varepsilon)$.
--
--   This is the inner measure of the probabilistic complexity $pK^t$ (Definition 15).
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). Values lie in $\mathbb N\cup\{\infty\}$ (`ℕ∞`), with $\min\emptyset=\infty$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 11, p.22

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB.Supplement

/-- **`K^{t,O}(x | y; r)`, `t`-time-bounded Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Definition 11, p.22):
"`K^{t,O}(x | y; r) ≜ min_{Π ∈ {0,1}^*} { |Π| : Π^O(y; ε; r) outputs x within t steps }`.
We define `K^{t,O}(x | y)` as `K^{t,O}(x | y; ε)`, and `K^{t,O}(x)` as `K^{t,O}(x | ε)`."

The universal machine `U`, with the program `p` on its input tape, `y` on the auxiliary tape, an
empty guess tape, `r` on the randomness tape and oracle `O`, halts within `t` steps with output `x`.

**Formalization Note.** Value in `ℕ∞` (`⊤` when no program qualifies), as the base `nKtime`.
The unrelativized measure is `O = ∅`. -/
noncomputable def Ktime (U : Machine) (O : Set (List Bool)) (t : ℕ) (x y r : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : U.HaltsWith O ⟨p, y, [], r⟩ t (bitsSym x)), (p.length : ℕ∞)

end NKtLB.Supplement


