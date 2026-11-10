-- Prove2me | Definitions.Def_LemonsPoA_TwoSided_Monopoly
-- name    : LemonsPoA_TwoSided_Monopoly
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:10:33.630609+00:00
-- url     : https://prove2.me/theorems/1c6e8a18-6ec1-43f2-b448-3292ad282d17
-- title:
--   Monopoly profit on a finite menu $u_Q$, continuous monopoly profit $u$, survival function, fine menu sequences
-- statement:
--   Let $V$ be a real random variable (a buyer's value) with law $\nu$, and write its **survival function** $\bar S(t)=\Pr[V>t]=\nu((t,\infty))$.
--
--   **Monopoly profit on a finite menu** (display (30)). For a finite price menu $Q\subset\mathbb R$ and a seller with reservation value $k\in\mathbb R$,
--   $$u_Q(k)=\max\Big(\{0\}\cup\{(q-k)\Pr[V>q] : q\in Q,\ q>k\}\Big).$$
--   It is the best profit a seller with value $k$ obtains by posting a price from $Q$ (or not trading) to a buyer who accepts exactly when $V>q$.
--
--   **Continuous monopoly profit** (display (32)).
--   $$u(k)=\sup_{q>k}\,(q-k)\Pr[V>q].$$
--
--   **Fine menu sequences** (display (24)). A sequence of finite menus $(Q_n)$ is fine if for every $H>0$, $\sup_{|q|\le H}\mathrm{dist}(q,Q_n)\to 0$, where $\mathrm{dist}(q,Q)=\min_{q'\in Q}|q-q'|$ (and $+\infty$ for an empty menu).
--
--   **Formalization Note** `survival ν t = (ν (Ioi t)).toReal`. `uQ ν Q k` is the maximum of the finite set $\{0\}\cup\{(q-k)\bar S(q):q\in Q,q>k\}$. `u ν k` is the real `sSup` of the nonempty set $\{(q-k)\bar S(q):q>k\}$; for integrable $V$ it is bounded above by $E[(V-k)_+]$, so this is the true supremum (the statements using it assume integrability). `IsFine Qs` is the equivalent form: for all $H>0$ and $\varepsilon>0$, eventually every $q$ with $|q|\le H$ has some $q'\in Q_n$ with $|q-q'|\le\varepsilon$ (the distance to a finite menu is attained and continuous in $q$, so this is (24) exactly; an empty menu fails it).
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), pp. 17-19, (24), (30), (32)

import Mathlib

open MeasureTheory Filter

namespace LemonsPoA.TwoSided

/-- Survival function `t ↦ Pr[V > t]` of a real random variable `V` with law `ν`. -/
noncomputable def survival (ν : Measure ℝ) (t : ℝ) : ℝ :=
  (ν (Set.Ioi t)).toReal

/-- Monopoly profit on a finite price menu, display (30):
`u_Q(k) = max ({0} ∪ {(q - k) Pr[V > q] : q ∈ Q, q > k})`, where `ν` is the law of the buyer's
value `V` and `k` is the seller's reservation value. -/
noncomputable def uQ (ν : Measure ℝ) (Q : Finset ℝ) (k : ℝ) : ℝ :=
  (insert 0 ((Q.filter (fun q => k < q)).image (fun q => (q - k) * survival ν q))).max'
    (Finset.insert_nonempty _ _)

/-- Continuous monopoly profit, display (32): `u(k) = sup_{q > k} (q - k) Pr[V > q]`.
The set is nonempty; for an integrable `V` it is bounded above by `E[(V - k)_+]`, so the real
`sSup` is the true supremum. -/
noncomputable def u (ν : Measure ℝ) (k : ℝ) : ℝ :=
  sSup ((fun q => (q - k) * survival ν q) '' Set.Ioi k)

/-- A sequence of finite price menus `(Q n)` is *fine*, display (24): for every `H > 0`,
`sup_{|q| ≤ H} dist(q, Q n) → 0`, where `dist(q, Q) = min_{q' ∈ Q} |q - q'|` (`+∞` for an
empty menu). Since `dist(·, Q n)` is continuous and the minimum over a finite menu is attained,
this is: for every `H > 0` and `ε > 0`, eventually every `q` with `|q| ≤ H` has a menu price
within `ε`. -/
def IsFine (Qs : ℕ → Finset ℝ) : Prop :=
  ∀ H : ℝ, 0 < H → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, ∀ q : ℝ, |q| ≤ H → ∃ q' ∈ Qs n, |q - q'| ≤ ε

end LemonsPoA.TwoSided


