-- Prove2me | Definitions.Def_NKtLB_Supplement_rKt
-- name    : NKtLB_Supplement_rKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:18:29.915219+00:00
-- url     : https://prove2.me/theorems/c053abd9-7f8c-4b55-be58-da034ace5061
-- title:
--   $r\mathrm{Kt}^O_\lambda(x\mid y)$ — randomized Levin–Kolmogorov complexity (Definition 14)
-- statement:
--   For $\lambda\in[0,1]$,
--   $$
--   r\mathrm{Kt}^O_\lambda(x\mid y)=\min_{\Pi,\;t}\Bigl\{\,|\Pi|+\lceil\log t\rceil : \Pr_{r\sim\{0,1\}^t}\bigl[\Pi^O(y;\varepsilon;r)\text{ outputs }x\text{ within }t\text{ steps}\bigr]\ge\lambda\Bigr\},
--   $$
--   with $\lambda=2/3$ when omitted. It is one of the five measures of Theorem 66.
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). Values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 14, p.22

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`rKt^O_λ(x | y)`, randomized Levin–Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Definition 14, p.22):
"`rKt^O_λ(x | y) = min_{Π ∈ {0,1}^*, t ∈ ℕ} { |Π| + ⌈log t⌉ : Pr_{r∼{0,1}^t}[Π(y; ε; r) outputs x
within t steps] ≥ λ }`."

**Formalization Note.** `⌈log t⌉ = Nat.clog 2 t`; random string of length `t`; value in `ℕ∞`;
oracle passed to `U` (p.22, "can easily be generalized"). `rKt(x)` is `rKt U ∅ (2/3) x []`. -/
noncomputable def rKt (U : Machine) (O : Set (List Bool)) (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (t : ℕ)
    (_ : lam ≤ prob t (fun r => U.HaltsWith O ⟨p, y, [], r⟩ t (bitsSym x))),
    ((p.length + Nat.clog 2 t : ℕ) : ℕ∞)

end NKtLB.Supplement


