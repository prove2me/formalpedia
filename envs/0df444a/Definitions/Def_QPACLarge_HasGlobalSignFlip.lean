-- Prove2me | Definitions.Def_QPACLarge_HasGlobalSignFlip
-- name    : QPACLarge_HasGlobalSignFlip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:09.793416+00:00
-- url     : https://prove2.me/theorems/0b71acee-de77-4816-98a9-87b821410955
-- title:
--   Global sign flip
-- statement:
--   A family $\{H_a\}_{a \in A}$ of sign-valued functions **admits a global sign flip** if there is a bijection $\iota : A \to A$ with $H_{\iota(a)}(x) = -H_a(x)$ for every seed $a$ and input $x$. For a Boolean family $h_a$ with $H_a = (-1)^{h_a}$ this reads $h_{\iota(a)} = 1 - h_a$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.5, p.18

import Mathlib

namespace QPACLarge

/-- **Global sign flip.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.5, p.18: "We say that the family `H` admits a global sign flip if there is a
bijection `ι : A → A` such that `H_{ι(a)}(x) = −H_a(x)` for every seed `a` and every input `x`."

For a Boolean family `h` (`H_a = (−1)^{h_a}`), `H_{ι(a)} = −H_a` is `h_{ι(a)} = ¬h_a`. -/
def HasGlobalSignFlip {A X : Type*} (h : A → X → Bool) : Prop :=
  ∃ ι : A ≃ A, ∀ a x, h (ι a) x = !h a x

end QPACLarge


