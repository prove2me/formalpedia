-- Prove2me | Definitions.Def_AvgWorstGap_Kt
-- name    : AvgWorstGap_Kt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:44.695552+00:00
-- url     : https://prove2.me/theorems/fff6f5e6-c92e-49ff-897b-1747c700c652
-- title:
--   Time-bounded Kolmogorov complexity $K^{t,O}(x\mid y;r)$ and plain $K(x)$
-- statement:
--   For strings $x,y,r$, a time bound $t$ and an oracle $O$,
--   $$K^{t,O}(x\mid y;r)=\min\{|\Pi| : \Pi^O(y;\epsilon;r)\text{ outputs }x\text{ within }t\text{ steps}\},$$
--   the minimum over programs $\Pi$ of the composition model. The value is $+\infty$ when no program qualifies. $K^{t,O}(x\mid y)$ is $K^{t,O}(x\mid y;\epsilon)$. The **unbounded** complexity $K^O(x\mid y)$ is the minimum of $K^{t,O}(x\mid y)$ over all $t$, and **plain Kolmogorov complexity** is $K(x)=K^{\emptyset}(x\mid\epsilon)$.
--
--   The module also provides the embedding of $\mathbb N\cup\{\infty\}$ into the extended reals, used to compare complexities with real thresholds.
--
--   **Formalization Note** Values lie in $\mathbb N\cup\{\infty\}$ (`ℕ∞`).
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 2.1, p.13

import Mathlib
import Definitions.Def_AvgWorstGap_Program
import Definitions.Def_NKtLB_toEReal

namespace AvgWorstGap

open NKtLB

/-- **Time-bounded Kolmogorov complexity `K^{t,O}(x | y; r)`** (Def. 2.1, arXiv:2610.19162,
version of October 30, 2026, p.13): "`K^{t,O}(x | y; r) ≜ min_{Π∈{0,1}∗} { |Π| | Π^O(y; ϵ; r)
outputs x within t steps }`. We write `K^{t,O}(x | y)` for `K^{t,O}(x | y; ϵ)` and `K^{t,O}(x)` for
`K^{t,O}(x | ϵ)`."

**Formalization Note.** Programs are those of the composition model (`Program`, p.13); `|Π|` is the
length of `progEnc Π`. The value is in `ℕ∞` and is `⊤` when no program qualifies. -/
noncomputable def Kt (O : Set (List Bool)) (t : ℕ) (x y r : List Bool) : ℕ∞ :=
  ⨅ (P : Program) (_ : ProgOutputs O P y r t (bitsSym x)), ((progEnc P).length : ℕ∞)

/-- **Unbounded Kolmogorov complexity `K^O(x | y)`** (Def. 2.1, p.13: "We write `K(x)` for the
corresponding unbounded plain Kolmogorov complexity"): the minimum of `K^{t,O}(x | y)` over all
time bounds `t`. -/
noncomputable def KU (O : Set (List Bool)) (x y : List Bool) : ℕ∞ :=
  ⨅ t : ℕ, Kt O t x y []

/-- **Plain Kolmogorov complexity `K(x)`** (p.13): `K^∅(x | ϵ)`. -/
noncomputable def K (x : List Bool) : ℕ∞ := KU ∅ x []

end AvgWorstGap


