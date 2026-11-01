-- Prove2me | Definitions.Def_NoSignalPA_Str
-- name    : NoSignalPA_Str
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:46.280494+00:00
-- url     : https://prove2.me/theorems/e5d11d4c-46d1-4448-b84c-f49ef1bdbcf0
-- title:
--   Bit strings $\{0,1\}^n$
-- statement:
--   The set $\{0,1\}^n$ of bit strings of length $n$. Alice's inputs $\mathbf x$ and outputs $\mathbf a$, Bob's inputs $\mathbf y$ and outputs $\mathbf b$ (all of length $N_r$) and the secret key $\mathbf k$ (of length $N_s$) are such strings.
--
--   **Formalization Note** A string is a function $\{0,\dots,n-1\}\to\{\mathtt{false},\mathtt{true}\}$ with $\mathtt{false}=0$, $\mathtt{true}=1$.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, p.2 (bit-string variables; h : {0,1}^Nr → {0,1}^Ns)

import Mathlib

namespace NoSignalPA

/-- **Bit strings of length `n`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, p. 2 ("Bold symbols correspond to bit-string variables"; `h : {0,1}^{Nr} → {0,1}^{Ns}`),
printed p. 2 = PDF p. 2.

`Str n` is `{0,1}^n`, encoded as `Fin n → Bool` with `false = 0`, `true = 1`. -/
abbrev Str (n : ℕ) : Type := Fin n → Bool

end NoSignalPA


