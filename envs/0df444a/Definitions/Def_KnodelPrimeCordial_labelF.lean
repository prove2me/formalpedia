-- Prove2me | Definitions.Def_KnodelPrimeCordial_labelF
-- name    : KnodelPrimeCordial_labelF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T05:59:14.321578+00:00
-- url     : https://prove2.me/theorems/d12b7da6-e0bc-498a-81dc-1894f1de499d
-- title:
--   The labeling $f$ of the proof of Lemma 2.3
-- statement:
--   For an index $i\ge 0$, the paper defines the label of $v_i$ by its residue modulo $12$:
--
--   $$
--   f(v_i)=\begin{cases}
--   i+2, & i\equiv 0,6,10 \pmod{12},\\
--   i+3, & i\equiv 1,2 \pmod{12},\\
--   i-2, & i\equiv 3 \pmod{12},\\
--   i-1, & i\equiv 4,8,11 \pmod{12},\\
--   i+1, & i\equiv 5 \pmod{12},\\
--   i+4, & i\equiv 7 \pmod{12},\\
--   i, & i\equiv 9 \pmod{12}.
--   \end{cases}
--   $$
--
--   On each block $\{12m,\dots,12m+11\}$ it permutes the values $12m+1,\dots,12m+12$ (Table 2.1: $2,4,5,1,3,6,8,11,7,9,12,10$ on the first block). For $n\equiv 0\pmod{12}$ it is the prime cordial labeling $f_0$ of $W_{3,n}$; the labelings $f_1,\dots,f_5$ of the remaining residue classes modify it on the last few vertices.
--
--   **Formalization Note** `labelF i` is $f(v_i)$ as a function of the index $i\in\mathbb N$. The subtractions $i-2$ and $i-1$ occur only when $i\equiv 3$, respectively $i\equiv 4,8,11 \pmod{12}$, so they never truncate.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), proof of Lemma 2.3, p.4 (PDF p.4), display defining f; Table 2.1, p.4

import Mathlib

namespace KnodelPrimeCordial

/-- **The labeling `f` of the proof of Lemma 2.3** (Haque, Khanam, Shahriar, *Prime cordial
labeling of Knödel graph*, manuscript (2026), proof of Lemma 2.3, p.4): "For 0 ≤ i ≤ n − 1, we
define the function f as follows:
f(vi) = i + 2, i ≡ 0, 6, 10 (mod 12); i + 3, i ≡ 1, 2 (mod 12); i − 2, i ≡ 3 (mod 12);
i − 1, i ≡ 4, 8, 11 (mod 12); i + 1, i ≡ 5 (mod 12); i + 4, i ≡ 7 (mod 12); i, i ≡ 9 (mod 12)."

`labelF i` is `f(v_i)`, as a function of the index `i`.

**Formalization Note** The value is computed from `i mod 12`. The case `i − 2` occurs only
for `i ≡ 3 (mod 12)`, so `i ≥ 3` and natural-number subtraction never truncates; likewise
`i − 1` occurs only for `i ≡ 4, 8, 11`. The final wildcard branch is the case `i ≡ 9`. -/
def labelF (i : ℕ) : ℕ :=
  match i % 12 with
  | 0 | 6 | 10 => i + 2
  | 1 | 2 => i + 3
  | 3 => i - 2
  | 4 | 8 | 11 => i - 1
  | 5 => i + 1
  | 7 => i + 4
  | _ => i

end KnodelPrimeCordial


