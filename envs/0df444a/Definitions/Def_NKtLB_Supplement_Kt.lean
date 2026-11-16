-- Prove2me | Definitions.Def_NKtLB_Supplement_Kt
-- name    : NKtLB_Supplement_Kt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:17:40.320755+00:00
-- url     : https://prove2.me/theorems/d6cb314b-08fc-4063-a421-7a3cb3fc5a95
-- title:
--   $\mathrm{Kt}^O(x\mid y;r)$ — Levin–Kolmogorov complexity (Definition 12)
-- statement:
--   The **Levin–Kolmogorov complexity** of $x$ given $(y;r)$ with oracle $O$ is
--   $$
--   \mathrm{Kt}^O(x\mid y;r)=\min_{\Pi,\;t}\bigl\{\,|\Pi|+\lceil\log t\rceil : \Pi^O(y;\varepsilon;r)\text{ outputs }x\text{ within }t\text{ steps}\bigr\},
--   $$
--   with $\mathrm{Kt}^O(x\mid y)=\mathrm{Kt}^O(x\mid y;\varepsilon)$ and $\mathrm{Kt}^O(x)=\mathrm{Kt}^O(x\mid\varepsilon)$. It charges a program both for its length and for the logarithm of its running time.
--
--   It defines the problem MKtP and is the inner measure of $p\mathrm{Kt}$ (Definition 16).
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). $\lceil\log t\rceil$ is `Nat.clog 2 t`; values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 12, p.22

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB.Supplement

/-- **`Kt^O(x | y; r)`, Levin–Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Definition 12, p.22):
"`Kt^O(x | y; r) ≜ min_{Π ∈ {0,1}^*, t ∈ ℕ} { |Π| + ⌈log t⌉ : Π^O(y; ε; r) outputs x within t steps }`.
We define `Kt^O(x | y)` as `Kt^O(x | y; ε)`, and `Kt^O(x)` as `Kt^O(x | ε)`."

**Formalization Note.** `⌈log t⌉` is `Nat.clog 2 t`, as in the base `nKt`. Value in `ℕ∞`. The
unrelativized `Kt(x)` is `Kt U ∅ x [] []`. -/
noncomputable def Kt (U : Machine) (O : Set (List Bool)) (x y r : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (t : ℕ) (_ : U.HaltsWith O ⟨p, y, [], r⟩ t (bitsSym x)),
    ((p.length + Nat.clog 2 t : ℕ) : ℕ∞)

end NKtLB.Supplement


