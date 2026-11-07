-- Prove2me | Definitions.Def_DoublingMST_IsRepEdge
-- name    : DoublingMST_IsRepEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:20.083348+00:00
-- url     : https://prove2.me/theorems/b51ec8c1-d41b-4514-b552-99568dffbc1b
-- title:
--   Representative edge of a pair, Lines 6–14 of Algorithm 2
-- statement:
--   Let $\epsilon=2^{-K}$, so $\log(1/\epsilon)=K$ and $\gamma=\epsilon^{-1}\log(1/\epsilon)=2^K K$; let $\ell^*$ be a critical level and $\ell=\max\{\operatorname{lev}(u),\operatorname{lev}(v)\}$. The edge $(p,q)$ chosen for $(u,v)$ is:
--
--   1. if $\ell<\ell^*-10K$ (low level): $(p,q)=(u,v)$;
--   2. if $\ell^*-10K\le\ell\le\ell^*+10K$ (middle level): a refined closest pair with threshold $\gamma$;
--   3. otherwise (high level): a refined closest pair with threshold $\tau_\ell=1.1^{\ell-\ell^*}$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Algorithm 2, Lines 6–14, and §4.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_DoublingMST_IsRefinedClosestPair

namespace DoublingMST

/-- **The representative edge of a pair, Lines 6–14 of Algorithm 2.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Algorithm 2, Lines 6–14, p.18 (PDF p.20), and §4.1, p.18: "Throughout the section, we may
assume that ϵ is a power of 2. Let γ := ϵ^{−1} log(1/ϵ). For each high level ℓ ≥ ℓ* + 10 log(1/ϵ),
define τ_ℓ := 1.1^{ℓ−ℓ*}."

With `ϵ = 2^{−K}` (so `log(1/ϵ) = K` and `γ = 2^K · K`), critical level `ℓs` and `m = max{lev u,
lev v}`, `IsRepEdge H K ℓs u v p q` says that `(p, q)` is an edge Lines 6–14 may produce for `(u, v)`:
* if `m < ℓs − 10K` (Line 6–7): `(p, q) = (u, v)`;
* if `ℓs − 10K ≤ m ≤ ℓs + 10K` (Lines 8–10): `IsRefinedClosestPair` with threshold `γ`;
* otherwise (Lines 11–14): `IsRefinedClosestPair` with threshold `τ_m = 1.1^{m − ℓs}`.

**Formalization Note.** Levels are compared in `ℤ`. Logs are base 2. -/
def IsRepEdge {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (K ℓs : ℕ)
    (u v : Fin n × ℕ) (p q : Fin n) : Prop :=
  if ((max u.2 v.2 : ℕ) : ℤ) < (ℓs : ℤ) - 10 * K then p = u.1 ∧ q = v.1
  else if ((max u.2 v.2 : ℕ) : ℤ) ≤ (ℓs : ℤ) + 10 * K then
    IsRefinedClosestPair H K ((2 : ℝ) ^ K * K) u v p q
  else IsRefinedClosestPair H K ((1.1 : ℝ) ^ (((max u.2 v.2 : ℕ) : ℤ) - ℓs)) u v p q

end DoublingMST


