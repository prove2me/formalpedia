-- Prove2me | Definitions.Def_NKtLB_nKtime
-- name    : NKtLB_nKtime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:03:38.888857+00:00
-- url     : https://prove2.me/theorems/6a896463-bcbd-467e-96d7-7bc209846d9b
-- title:
--   $\mathrm{nK}^{t}(x\mid y;r)$: nondeterministic time-bounded Kolmogorov complexity
-- statement:
--   For strings $x,y,r$, a time bound $t$, an oracle $O$ and a query-length bound $\ell$,
--   $$
--   \mathrm{nK}^{t,O^{\le\ell}}(x\mid y;r)=\min\bigl\{|\Pi| : \Pi\text{ nondeterministically outputs }x\text{ on }(y;r)\text{ in time }t\bigr\}.
--   $$
--   Further, $\mathrm{nK}^t(x\mid y)=\mathrm{nK}^t(x\mid y;\varepsilon)$ and $\mathrm{nK}^t(x)=\mathrm{nK}^t(x\mid\varepsilon)$.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$. The unrelativized measure has oracle $\emptyset$ and $\ell=\infty$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 17, p.23 (oracle version: p.22)

import Mathlib
import Definitions.Def_NKtLB_NondetOutputs

namespace NKtLB

/-- **`nK^{t,O}(x | y; r)`, nondeterministic `t`-time-bounded Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Definition 17, p.23):
`nK^t(x | y; r) = min_{Π ∈ {0,1}^*} { |Π| : ∀w ∈ {0,1}^t, Π(y; w; r) outputs x or ⊥ in t steps;
∃w ∈ {0,1}^t, Π(y; w; r) outputs x in t steps }`, with the oracle versions "easily generalized"
(p.22). `nK^t(x | y) = nK^t(x | y; ε)`.

**Formalization Note.** Value in `ℕ∞`, `⊤` when no program qualifies. `ℓ` restricts query lengths
(`⊤`: none). -/
noncomputable def nKtime (U : Machine) (O : Set (List Bool)) (ℓ : ℕ∞) (t : ℕ)
    (x y r : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : NondetOutputs U O ℓ p y r t x), (p.length : ℕ∞)

end NKtLB


