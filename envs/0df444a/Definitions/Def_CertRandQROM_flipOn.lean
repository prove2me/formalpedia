-- Prove2me | Definitions.Def_CertRandQROM_flipOn
-- name    : CertRandQROM_flipOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:10.410371+00:00
-- url     : https://prove2.me/theorems/bb5ed6e2-254b-4a4a-9e26-461cbfbaf8fb
-- title:
--   Reprogrammed oracle $H\oplus X$
-- statement:
--   For an oracle $H:U\to\{0,1\}$ and a set $X\subseteq U$ of inputs, $H\oplus X$ is the oracle obtained by flipping $H$ on $X$:
--
--   $$
--   (H\oplus X)(u)=\begin{cases}1-H(u), & u\in X,\\ H(u), & u\notin X.\end{cases}
--   $$
--
--   The family $\mathcal F_H(M)=\{H\oplus X : X\subseteq M\}$ of reprogrammings of $H$ on $M$ is written in the statements as "for every $X\subseteq M$".
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §4.1, p.18 (PDF p.20), definition of H ⊕ X; F_H(M), p.19 (PDF p.21)

import Mathlib

namespace CertRandQROM

/-- **Reprogramming an oracle on a set** (§4.1, p.18 of Coladangelo et al., arXiv:2608.31112,
sha256 b75095a2…): `H ⊕ X` is obtained from `H` by flipping the coordinates in `X`:
`(H ⊕ X)(u) = H(u)` for `u ∉ X` and `(H ⊕ X)(u) = 1 − H(u)` for `u ∈ X`.
The family `F_H(M) = {H ⊕ X : X ⊆ M}` (p.19) is written in statements as "for all `X ⊆ M`". -/
def flipOn {U : Type} [DecidableEq U] (h : U → Bool) (X : Finset U) : U → Bool :=
  fun u => if u ∈ X then !h u else h u

end CertRandQROM


