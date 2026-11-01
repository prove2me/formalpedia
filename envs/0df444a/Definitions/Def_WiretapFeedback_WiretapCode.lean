-- Prove2me | Definitions.Def_WiretapFeedback_WiretapCode
-- name    : WiretapFeedback_WiretapCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:51.868825+00:00
-- url     : https://prove2.me/theorems/b31d8929-5f7a-4ee0-9d92-33d3a5bc6d4c
-- title:
--   Wiretap code with public feedback
-- statement:
--   A **wiretap code with feedback** for a discrete memoryless wiretap channel $W:\mathcal X\to\mathcal Y\times\mathcal Z$, with $N$ messages and block length $n$, consists of (possibly randomized) encoder mappings $e_t:\{1,\dots,N\}\times\mathcal F^t\to\mathcal X$, $1\le t\le n$, feedback mappings $f_t:\mathcal Y^t\to\mathcal F$, $0\le t\le n-1$, and a decoder $d:\mathcal Y^n\to\{1,\dots,N\}$.
--
--   For a message $M$, the protocol begins with a feedback $F_0$ from the receiver. At each time the transmitter sends $X_t=e_t(M,F^{t-1})$, the channel outputs $(Y_t,Z_t)$ with probability $W(Y_t,Z_t|X_t)$, the receiver observes $Y_t$ and sends the feedback $F_t=f_t(Y^t)$, and the eavesdropper observes $Z_t$ (and, the feedback being public, all of $\mathbf F$). After the final transmission $X_n$ the receiver decodes $\hat M=d(Y^n)$.
--
--   **Formalization Note** Messages are $\{0,\dots,N-1\}$. The randomization is represented by independent local randomness $U_x$ (transmitter) and $U_y$ (receiver) of arbitrary types, shared across rounds, as in the proof of Lemma 7; the feedback alphabet $\mathcal F$ is arbitrary. Rounds are indexed $s=0,\dots,n-1$: round $s$ sends $F_s=f_s(Y_0,\dots,Y_{s-1},U_y)$, then $X_s=e_s(M,U_x,F_0,\dots,F_s)$. The decoder is deterministic, as printed.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, pp.1–2 (wiretap code with feedback)

import Mathlib

namespace WiretapFeedback

/-- A **wiretap code with feedback** of `N` messages and block length `n`, for a wiretap channel
with input alphabet `X` and legitimate-receiver output alphabet `Y`, Hayashi–Tyagi–Watanabe,
*Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing*,
arXiv:1410.0443v1, §II, pp. 1–2:

"A wiretap code for a discrete memoryless wiretap channel `W : X → Y × Z` with feedback consists
of (possibly randomized) encoder mappings `e_t : {1, ..., N} × 𝓕^t → X`, `1 ≤ t ≤ n`, feedback
mappings `f_t : Y^t → 𝓕`, `0 ≤ t ≤ n − 1`, and a decoder `d : Yⁿ → {1, ..., N}`."

With rounds indexed `s = 0, …, n − 1` (the paper's `t = s + 1` for the encoder), round `s` is:
the receiver sends `F_s = feedback s (Y_0, …, Y_{s−1}) U_y`, the transmitter sends
`X_s = encoder s M Uₓ (F_0, …, F_s)`, the channel outputs `(Y_s, Z_s) ∼ W(·|X_s)`; finally
`M̂ = decoder (Y_0, …, Y_{n−1})`.

**Formalization Note** Messages `{1, …, N}` are `Fin N`. "Possibly randomized" mappings are
deterministic functions of independent local randomness `Uₓ` (transmitter) and `U_y` (receiver)
of arbitrary types, shared across rounds: the representation of the proof of Lemma 7 (p. 3); it
contains every randomized encoder and feedback rule. The feedback alphabet `𝓕` is an arbitrary
type. The feedback sees only the legitimate output `Y`; the decoder is deterministic, as printed. -/
structure WiretapCode (X Y : Type) (N n : ℕ) where
  /-- The feedback alphabet `𝓕`. -/
  Fb : Type
  /-- The type of the transmitter's local randomness `Uₓ`. -/
  Ux : Type
  /-- The type of the receiver's local randomness `U_y`. -/
  Uy : Type
  /-- The law of `Uₓ`. -/
  lawX : PMF Ux
  /-- The law of `U_y`. -/
  lawY : PMF Uy
  /-- The feedback map of round `s`: `F_s = f_s(Y_0, …, Y_{s−1}, U_y)`. -/
  feedback : (s : Fin n) → (Fin s → Y) → Uy → Fb
  /-- The encoder map of round `s`: `X_s = e_s(M, Uₓ, F_0, …, F_s)`. -/
  encoder : (s : Fin n) → Fin N → Ux → (Fin (s + 1) → Fb) → X
  /-- The decoder `M̂ = d(Yⁿ)`. -/
  decoder : (Fin n → Y) → Fin N

end WiretapFeedback


