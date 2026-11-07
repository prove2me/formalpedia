-- Prove2me | Definitions.Def_QPACLarge_SubexpOWFExists
-- name    : QPACLarge_SubexpOWFExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:16.822917+00:00
-- url     : https://prove2.me/theorems/596308a7-18f5-4db0-af85-c4705e330a9f
-- title:
--   Subexponentially secure one-way functions exist
-- statement:
--   A uniform family $f_n : \{0,1\}^n \to \{0,1\}^{m(n)}$ computable in deterministic polynomial time is a **subexponentially secure one-way function** if there is a constant $\varepsilon > 0$ such that, for every uniform randomized algorithm $I$ running in time at most $2^{n^\varepsilon}$, every positive polynomial $p$ and every sufficiently large $n$,
--
--   $$
--   \Pr_{x \sim U_n,\ y = f_n(x),\ I}\big[I(1^n, y) \in f_n^{-1}(y)\big] < \frac{1}{p(n)}.
--   $$
--
--   This proposition states that such a family exists. It is the hypothesis of the conditional clause of Theorem 1.5 and of Lemma 4.2.
--
--   **Formalization Note** The family is one polynomial-time computable map $F$ whose output length depends only on the input length. Inverters are clocked Turing machines (see `owfInvSuccess`) with time $\lfloor 2^{n^\varepsilon}\rfloor$ measured in the security parameter $n$. Clocking every machine admits truncations of slower machines; a truncation runs in time polynomial in $2^{n^\varepsilon}$, so the notion agrees with the paper's after halving $\varepsilon$, which is existential. A positive polynomial is read as $p(n)+1$ with $p \in \mathbb N[X]$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.6, p.19 (also p.6)

import Mathlib
import Definitions.Def_QPACLarge_owfInvSuccess

namespace QPACLarge

open QAlgorithms.Complexity Filter

/-- **Subexponentially secure one-way functions exist.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.6, p.19 (also p.6): "A uniform family of functions `fₙ : {0,1}ⁿ → {0,1}^{m(n)}`
computable in deterministic polynomial time is a subexponentially secure one-way function if there
is a constant `ε > 0` such that, for every uniform randomized algorithm `I` running in time at
most `2^{n^ε}`, every positive polynomial `p`, and every sufficiently large `n`,
`Pr_{x∼Uₙ, y=fₙ(x), I}[I(1ⁿ, y) ∈ fₙ⁻¹(y)] < 1/p(n)`."

There are a polynomial-time computable `F : {0,1}* → {0,1}*` whose output length depends only on
the input length (`fₙ` is `F` on `n`-bit inputs) and an `ε > 0` such that every machine clocked at
`⌊2^{n^ε}`⌋ steps, with that many coin bits, inverts with probability below `1/(p(n) + 1)` for every
polynomial `p` with natural coefficients and every large `n`.

**Formalization Note.** Time is measured in the security parameter `n` (the input is
`1ⁿ0 · y · r`). "Positive polynomial `p`" is read as `p + 1` with `p ∈ ℕ[X]` (every positive
polynomial is below some such `p + 1`, and every `p + 1` is positive). Clocking every machine at
`T` instead of quantifying over machines that always halt within `T` admits truncated machines;
a truncation runs in time polynomial in `T`, so the two notions agree once `ε` is halved, and
`ε` is existential. -/
def SubexpOWFExists : Prop :=
  ∃ (F : Str → Str) (mlen : ℕ → ℕ), PolyTimeComputable F ∧
    (∀ x : Str, (F x).length = mlen x.length) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ (I : Turing.TM2ComputableAux Bool Bool) (p : Polynomial ℕ),
      ∀ᶠ n : ℕ in atTop,
        owfInvSuccess F I ⌊(2 : ℝ) ^ ((n : ℝ) ^ ε)⌋₊ n < 1 / ((p.eval n : ℕ) + 1 : ℝ)

end QPACLarge


