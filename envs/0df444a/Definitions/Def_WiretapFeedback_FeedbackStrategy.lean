-- Prove2me | Definitions.Def_WiretapFeedback_FeedbackStrategy
-- name    : WiretapFeedback_FeedbackStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:50.510865+00:00
-- url     : https://prove2.me/theorems/8c5a7243-6865-43a6-bd49-aad7d52ae521
-- title:
--   $n$-round transmission–feedback strategy over a channel
-- statement:
--   An **$n$-round transmission–feedback strategy** over a channel with input alphabet $\mathcal X$ and output alphabet $\mathcal O$ consists of
--
--   1. a feedback alphabet $\mathcal F$ (any set);
--   2. independent local randomness $U_x\sim P_{U_x}$ at the transmitter and $U_y\sim P_{U_y}$ at the receiver, of arbitrary types;
--   3. feedback maps: in round $s=0,\dots,n-1$ the receiver sends $F_s=f_s(O_0,\dots,O_{s-1},U_y)\in\mathcal F$;
--   4. encoder maps: then the transmitter sends $X_s=e_s(U_x,F_0,\dots,F_s)\in\mathcal X$, and the channel produces the output $O_s$.
--
--   This is the common skeleton of a wiretap code with feedback (§II, where the encoder also sees the message and the feedback sees only the legitimate output) and of an $n$-length active hypothesis test (§III, where the encoder mappings are $e_t:\mathcal F^t\to\mathcal X$ and the feedback mappings $f_t:\mathcal O^t\to\mathcal F$).
--
--   **Formalization Note** "Possibly randomized" mappings are deterministic functions of local randomness shared across rounds, which is the representation the paper itself uses in the proof of Lemma 7 and contains every randomized protocol. Rounds are indexed from $0$: the paper's $X_t$ ($1\le t\le n$) is $X_{t-1}$ here, and the paper's $F_t$ ($0\le t\le n-1$) is $F_t$.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, pp.1–2 (wiretap code with feedback); §III, p.2 (n-length active hypothesis test); proof of Lemma 7, p.3 (local randomness Ux, Uy)

import Mathlib

namespace WiretapFeedback

/-- An `n`-round **transmission–feedback strategy** over a channel with input alphabet `X` and
output alphabet `O`: the common structure of a wiretap code with feedback (Hayashi–Tyagi–Watanabe,
arXiv:1410.0443v1, §II, pp. 1–2) and of an `n`-length active hypothesis test (§III, p. 2).

The transmitter and the receiver hold independent local randomness `Ux ∼ lawX` and
`Uy ∼ lawY` (the representation used in the proof of Lemma 7, p. 3). With rounds indexed
`s = 0, …, n − 1` (the paper's `t = s + 1`), round `s` consists of
1. the feedback `F_s = feedback s (O_0, …, O_{s−1}) Uy ∈ Fb` from the receiver,
2. the channel input `X_s = encoder s Ux (F_0, …, F_s) ∈ X` from the transmitter,
3. the channel output `O_s ∼ W(·|X_s)`.

**Formalization Note** "Possibly randomized" encoder and feedback mappings are deterministic
functions of the local randomness, of arbitrary type, shared across rounds: this is the paper's
own representation (proof of Lemma 7) and contains every randomized protocol. The feedback
alphabet `Fb` is an arbitrary type. The paper's `F₀` (sent at `t = 0`) is `F_0` here, and the
paper's `X_t = e_t(M, F^{t−1})` is `X_{t−1}` here. -/
structure FeedbackStrategy (X O : Type) (n : ℕ) where
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
  /-- The feedback map of round `s`: `F_s = f_s(O_0, …, O_{s−1}, U_y)`. -/
  feedback : (s : Fin n) → (Fin s → O) → Uy → Fb
  /-- The encoder map of round `s`: `X_s = e_s(Uₓ, F_0, …, F_s)`. -/
  encoder : (s : Fin n) → Ux → (Fin (s + 1) → Fb) → X

end WiretapFeedback


