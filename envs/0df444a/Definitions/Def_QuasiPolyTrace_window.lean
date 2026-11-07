-- Prove2me | Definitions.Def_QuasiPolyTrace_window
-- name    : QuasiPolyTrace_window
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:53.939977+00:00
-- url     : https://prove2.me/theorems/653bdc5c-4024-4677-9ef4-be9a4b2833ce
-- title:
--   The zero-padded window $x_{[i:n]}$
-- statement:
--   For a binary string $x=(x_1,\dots,x_n)$ and an integer $i$, the **window** $x_{[i:n]}$ is the substring $(x_i,\dots,x_n)$ when $i\ge 1$, and, when $i\le 0$, the string
--
--   $$
--   (\underbrace{0,\dots,0}_{1-i},x_1,\dots,x_n)
--   $$
--
--   obtained by prepending known zeros at the positions $i,\dots,0$. This is the paper's convention for deletion channels that extend "off the end" of the strings (proof of Theorem 44): the induction considers windows $x_{[d-2R:n]}$ and $x_{[d-R-R':n]}$ that may start before the first bit.
--
--   **Formalization Note** Only left padding is encoded: zeros appended on the right change no statistic, since reads beyond the end of a trace are already $0$.
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), §2, p.6 (substrings x[i:j]); padding convention, proof of Theorem 44, p.42

import Mathlib

namespace QuasiPolyTrace

/-- **The padded window `x[i:n]`.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), §2, p.6 ("`x[i:j]` … refers to the string
`(x_i, …, x_j)`") with the padding convention of the proof of Theorem 44, p.42: "If at any point in this
proof we consider a deletion channel that extends 'off the end' of our strings, the intention is to
implicitly pad the string by prepending and appending known 0s".

For a 1-indexed string `u = (x_1, …, x_n)` and an integer `i`, `window u i` is `(x_i, …, x_n)` when
`i ≥ 1`, and the string `(0, …, 0, x_1, …, x_n)` with `1 − i` prepended zeros (positions `i, …, 0`) when
`i ≤ 0`.

**Formalization Note.** Only left padding is encoded: appending zeros on the right changes no statistic,
since reads beyond the end of a trace are already 0 (Definition 3). The windows of the paper all run to the
end of the string (`x[d−2R:n]`, `x[d−R−R′:n]`), so the right end is always `n`. -/
def window (u : List Bool) (i : ℤ) : List Bool :=
  List.replicate (1 - i).toNat false ++ u.drop (i - 1).toNat

end QuasiPolyTrace


