-- Prove2me | Definitions.Def_RvsCert_IsCertificate
-- name    : RvsCert_IsCertificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:03.469858+00:00
-- url     : https://prove2.me/theorems/80d5753d-73e3-444e-a863-97048db7e395
-- title:
--   Certificate for an input of a Boolean function
-- statement:
--   Let $\iota$ be a set of bit positions and $f:\{0,1\}^\iota\to\{0,1\}$ a Boolean function. A set $S\subseteq\iota$ is a **certificate** for the input $x$ if every input that agrees with $x$ on $S$ has the same value:
--   $$
--   \forall y\in\{0,1\}^\iota:\quad \big(y_i=x_i\ \text{for all } i\in S\big)\ \Longrightarrow\ f(y)=f(x).
--   $$
--   The size of a certificate is the number $|S|$ of bits it reveals. This is the standard notion of [BdW02], which the paper uses without restating.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 1, p.1 (standard notion, deferred to [BdW02])

import Mathlib

namespace RvsCert

/-- **Certificate** (standard notion used without definition by Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1, p.1, which defers
to [BdW02]). A set `S` of positions is a certificate for the input `x` of the Boolean function
`f` if every input `y` that agrees with `x` on `S` has `f y = f x`.

**Formalization Note.** Inputs are bit strings `ι → Bool`; `S` is a `Finset ι`; its size is
the number of revealed bits. -/
def IsCertificate {ι : Type} (f : (ι → Bool) → Bool) (x : ι → Bool) (S : Finset ι) : Prop :=
  ∀ y : ι → Bool, (∀ i ∈ S, y i = x i) → f y = f x

end RvsCert


