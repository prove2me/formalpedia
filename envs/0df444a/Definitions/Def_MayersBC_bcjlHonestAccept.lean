-- Prove2me | Definitions.Def_MayersBC_bcjlHonestAccept
-- name    : MayersBC_bcjlHonestAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:59:10.107982+00:00
-- url     : https://prove2.me/theorems/006716f5-fd75-4a9f-a43f-cce40a4b364b
-- title:
--   Honest BCJL acceptance probability
-- statement:
--   The probability that Bob accepts an honest opening of $b$ in the BCJL protocol: Alice draws $(\theta, c)$ with probability $p(\theta, c\mid b)$, sends $|c\rangle_\theta$, Bob measures in a uniformly random basis string and obtains $(\hat\theta, \hat c)$, and accepts when $T_b(\theta, c, \hat\theta, \hat c)$ returns ok:
--
--   $$
--   \Pr\big(T_b(W^{(b)}) = ok\big) = \sum_{\theta,c}\ \sum_{(\hat\theta,\hat c):\ T_b(\theta,c,\hat\theta,\hat c)} p(\theta,c\mid b)\, 2^{-n} \big|\langle \hat c|_{\hat\theta}\, | c\rangle_\theta\big|^2 .
--   $$
--
--   The correctness of the protocol is the requirement that this probability be close to $1$.
--
--   **Formalization Note** The test $T$ is an arbitrary predicate; its exact description "is irrelevant for our analysis" (p.3).
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, pp.3–5

import Mathlib
import Definitions.Def_MayersBC_honestAccept
import Definitions.Def_MayersBC_bcjlProb
import Definitions.Def_MayersBC_bb84State
import Definitions.Def_MayersBC_bobPOVM

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section b, pp.3–5: `Pr(T_b(W^{(b)}) = ok)`, the probability
that Bob accepts an honest opening of `b` in the BCJL protocol: Alice draws `(θ, c)` with
probability `p(θ, c|b)` and sends `|c⟩_θ`, Bob measures with `bobPOVM n` and obtains `(θ̂, ĉ)`,
and accepts when `T_b(θ, c, θ̂, ĉ)` is ok.

**Formalization Note.** The test is any predicate
`T : ZMod 2 → Opening n → Opening n → Prop`; `(C, r)` is suppressed in its input (p.4). -/
noncomputable def bcjlHonestAccept {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : Fin n → ZMod 2) (T : ZMod 2 → Opening n → Opening n → Prop) (b : ZMod 2) : ℝ :=
  honestAccept (bcjlProb C r) (fun w : Opening n => bb84State w.1 w.2) (bobPOVM n) T b

end MayersBC


