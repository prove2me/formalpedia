-- Prove2me | Definitions.Def_HWMaskLeak_fullRange
-- name    : HWMaskLeak_fullRange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:59.787911+00:00
-- url     : https://prove2.me/theorems/812e79e5-83b5-4ab8-b4ec-460646ed939e
-- title:
--   Full-range multiplicity function $B_w$, eq. (19), and its transform $\hat B_w$, eq. (20)
-- statement:
--   Let $Q:=2^n$. For a weight $w$ and $x\in G=\mathbb Z/N\mathbb Z$, the **full-range multiplicity function** counts the $n$-bit integers of weight $w$ that reduce to $x$:
--   $$
--   B_w(x):=\#\{0\le y<Q:\ y\equiv x \pmod N,\ \mathrm{wt}(y)=w\}.
--   $$
--   Its normalized Fourier transform is
--   $$
--   \hat B_w(t)=\frac1N\sum_{x\in G}B_w(x)\,e_N(-xt)=\frac1N\sum_{\substack{0\le y<Q\\ \mathrm{wt}(y)=w}}e_N(-yt).
--   $$
--
--   $B_w$ replaces the actual slice $S_w$ in the paper's **full-range model**: the summation runs over the complete $n$-bit range, while addition and characters stay modulo $N$, so $\hat B_w$ has a product (generating-function) structure.
--
--   **Formalization Note** $\mathrm{wt}(y)$ of the integer $y$ is the sum of its binary digits. The definition is total in $w$; for $w>n$ it is identically $0$.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §4.1, p.20, eqs. (19)–(20)

import Mathlib
import Definitions.Def_HWMaskLeak_fhat

namespace HWMaskLeak

/-- **The full-range multiplicity function `B_w`, eq. (19)** (Biswas, Hwang, Maji, Shkredov, Ye, *When
Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding*, preprint (version
of October 31, 2026, sha256 ab686360…), §4.1, p.20): with `Q := 2ⁿ`, for `w ∈ W_bin = {0, …, n}` and
`x ∈ G = ℤ/Nℤ`, `B_w(x) := #{0 ⩽ y < Q : y ≡ x mod N, wt(y) = w}`.

**Formalization Note** `wt(y)` of the integer `y < 2ⁿ` is the sum of its binary digits. The
definition is total in `w`; for `w > n` it is identically `0`. -/
def fullRange (n N : ℕ) (w : ℕ) (x : ZMod N) : ℕ :=
  ((Finset.range (2 ^ n)).filter (fun y : ℕ => ((y : ZMod N) = x) ∧ (Nat.digits 2 y).sum = w)).card

/-- **The Fourier transform `B̂_w(t)`, eq. (20)** (same preprint, §4.1, p.20):
`B̂_w(t) = (1/N) Σ_{x ∈ G} B_w(x) e_N(−xt)`, the normalized transform of §2.1 applied to `B_w`. -/
noncomputable def fullRangeHat (n N : ℕ) [NeZero N] (w : ℕ) (t : ZMod N) : ℂ :=
  fhat N (fun x => (fullRange n N w x : ℂ)) t

end HWMaskLeak


