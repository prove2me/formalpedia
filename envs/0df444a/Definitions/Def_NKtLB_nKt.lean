-- Prove2me | Definitions.Def_NKtLB_nKt
-- name    : NKtLB_nKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:04:23.785194+00:00
-- url     : https://prove2.me/theorems/483b0f72-0f5d-4800-9c0a-fefdadb81a03
-- title:
--   $\mathrm{nKt}(x\mid y;r)$: nondeterministic Levin–Kolmogorov complexity
-- statement:
--   For strings $x,y,r$, an oracle $O$ and a query-length bound $\ell$,
--   $$
--   \mathrm{nKt}^{O^{\le\ell}}(x\mid y;r)=\min_{\Pi,\ t\in\mathbb N}\bigl\{|\Pi|+\lceil\log t\rceil : \Pi\text{ nondeterministically outputs }x\text{ on }(y;r)\text{ in time }t\bigr\}.
--   $$
--   Further, $\mathrm{nKt}(x\mid y)=\mathrm{nKt}(x\mid y;\varepsilon)$ and $\mathrm{nKt}(x)=\mathrm{nKt}(x\mid\varepsilon)$, with no oracle.
--
--   The $\lceil\log t\rceil$ term charges a description for its running time; without it $\mathrm{nKt}$ would be the time-unbounded nondeterministic complexity.
--
--   **Formalization Note** $\lceil\log t\rceil$ is `Nat.clog 2 t`, which is $0$ for $t\le1$. The value lies in $\mathbb N\cup\{\infty\}$. $\mathrm{nKt}(x)$ is `nKt U ∅ ⊤ x [] []`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 18, p.23

import Mathlib
import Definitions.Def_NKtLB_NondetOutputs

namespace NKtLB

/-- **`nKt^O(x | y; r)`, nondeterministic Levin–Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Definition 18,
p.23): `nKt(x | y; r) = min_{Π ∈ {0,1}^*, t ∈ ℕ} { |Π| + ⌈log t⌉ : ∀w ∈ {0,1}^t, Π(y; w; r)
outputs x or ⊥ in t steps; ∃w ∈ {0,1}^t, Π(y; w; r) outputs x in t steps }`.
"We define `nKt(x | y)` as `nKt(x | y; ε)`, and `nKt(x)` as `nKt(x | ε)`."

**Formalization Note.** `⌈log t⌉` is `Nat.clog 2 t` (`0` for `t ≤ 1`). Value in `ℕ∞`. `nKt(x)` is
`nKt U ∅ ⊤ x [] []`. -/
noncomputable def nKt (U : Machine) (O : Set (List Bool)) (ℓ : ℕ∞) (x y r : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (t : ℕ) (_ : NondetOutputs U O ℓ p y r t x),
    ((p.length + Nat.clog 2 t : ℕ) : ℕ∞)

end NKtLB


