-- Prove2me | Definitions.Def_OWFLocalDesc_InInterval
-- name    : OWFLocalDesc_InInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:28.82866+00:00
-- url     : https://prove2.me/theorems/0d514441-4e43-485c-b45b-67cfd0ad18a0
-- title:
--   Tolerant quantile window in $\mathbb Z\cup\{\infty\}$
-- statement:
--   Quantiles take values in $\mathbb Z_{\ge0}\cup\{\infty\}$. For an integer $d\ge0$ we set $\infty-d=\infty+d=\infty$, and every integer is smaller than $\infty$. For quantile values $\ell,h$, the value $o\in\mathbb Z\cup\{\infty\}$ **lies in the window** $[\ell-d,\,h+d]$ if
--   $$\ell-d\ \le\ o\ \le\ h+d$$
--   in the ordered set $\mathbb Z\cup\{\infty\}$. In particular the window $[\infty-d,\infty+d]$ contains exactly $\infty$.
--
--   **Formalization Note** Values are in `WithTop ℤ`; the shift by $d$ fixes $\infty$ and the lower end may be negative (no clamping at $0$).
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §2.1, p.13

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc

/-- A quantile value in `ℤ≥0 ∪ {∞}` read in `ℤ ∪ {∞}`. -/
def toWT (v : ℕ∞) : WithTop ℤ := WithTop.map (fun k : ℕ => (k : ℤ)) v

/-- **Tolerant quantile window.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), §2.1, p.13: "For every real d ≥ 0
we set ∞ − d = ∞ + d = ∞, and every integer is smaller than ∞. Intervals are closed intervals of
the ordered set Z ∪ {∞}. Hence an interval whose endpoints are ∞ − d and ∞ + d contains exactly ∞."

`InInterval lo hi d o` says that `o ∈ [lo − d, hi + d]` in `ℤ ∪ {∞}`, with `∞ ± d = ∞`.

**Formalization Note.** The shift by `d` is `WithTop.map`, so `⊤` is fixed and the lower end may
be negative (no clamping at `0`). -/
def InInterval (lo hi : ℕ∞) (d : ℕ) (o : WithTop ℤ) : Prop :=
  WithTop.map (fun v : ℤ => v - d) (toWT lo) ≤ o ∧ o ≤ WithTop.map (fun v : ℤ => v + d) (toWT hi)

end OWFLocalDesc


