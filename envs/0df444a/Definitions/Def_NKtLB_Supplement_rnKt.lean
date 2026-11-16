-- Prove2me | Definitions.Def_NKtLB_Supplement_rnKt
-- name    : NKtLB_Supplement_rnKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:20:31.682428+00:00
-- url     : https://prove2.me/theorems/ce56ecf5-21d6-4446-9b69-0d5d0dab02ae
-- title:
--   $rn\mathrm{Kt}^O_\lambda(x\mid y)$ — randomized nondeterministic Levin–Kolmogorov complexity (Definition 20)
-- statement:
--   For $\lambda\in[0,1]$,
--   $$
--   rn\mathrm{Kt}_\lambda(x\mid y)=\min_{\Pi,\;t}\Bigl\{\,|\Pi|+\lceil\log t\rceil : \Pr_{r\sim\{0,1\}^t}\Bigl[\begin{array}{l}\forall w\in\{0,1\}^t,\ \Pi(y;w;r)\text{ outputs }x\text{ or }\bot\text{ in }t\text{ steps};\\ \exists w\in\{0,1\}^t,\ \Pi(y;w;r)\text{ outputs }x\text{ in }t\text{ steps}\end{array}\Bigr]\ge\lambda\Bigr\},
--   $$
--   with $\lambda=2/3$ when omitted. This is the central randomized nondeterministic measure of Theorems 4, 5, 7, 9, 58, 65, 66 and 82.
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). Values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 20, p.23

import Mathlib
import Definitions.Def_NKtLB_NondetOutputs
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`rnKt_λ(x | y)`, randomized nondeterministic Levin–Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Definition 20, p.23): "`rnKt_λ(x | y) ≜ min_{Π ∈ {0,1}^*, t ∈ ℕ} { |Π| + ⌈log t⌉ : Pr_{r∼{0,1}^t}[∀w ∈
{0,1}^t, Π(y; w; r) outputs x or ⊥ in t steps; ∃w ∈ {0,1}^t, Π(y; w; r) outputs x in t steps] ≥ λ }`."

**Formalization Note.** `⌈log t⌉ = Nat.clog 2 t`; event `NondetOutputs U O ⊤ p y r t x`; random
string of length `t`; value in `ℕ∞`; oracle passed to `U`. `rnKt(x)` is `rnKt U ∅ (2/3) x []`. -/
noncomputable def rnKt (U : Machine) (O : Set (List Bool)) (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (t : ℕ) (_ : lam ≤ prob t (fun r => NondetOutputs U O ⊤ p y r t x)),
    ((p.length + Nat.clog 2 t : ℕ) : ℕ∞)

end NKtLB.Supplement


