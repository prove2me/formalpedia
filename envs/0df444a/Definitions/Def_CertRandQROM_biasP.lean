-- Prove2me | Definitions.Def_CertRandQROM_biasP
-- name    : CertRandQROM_biasP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:19.612262+00:00
-- url     : https://prove2.me/theorems/984969ea-6749-4a81-b0c7-2b0f32db7700
-- title:
--   The bias $p$ of Construction 6.2
-- statement:
--   For a code length $n\ge1$, the bias of the oracle in Construction 6.2 is the unique power of $1/2$ with
--
--   $$
--   \frac{1}{80\sqrt n}<p\le\frac{1}{40\sqrt n},\qquad p=2^{-d},\ d=\lceil\log_2(40\sqrt n)\rceil .
--   $$
--
--   The bias is of order $1/\sqrt n$: small enough for the honest prover's dual decoding and large enough that $pn=\Omega(\sqrt n)$ in the min-entropy bound.
--
--   **Formalization Note** The sanity file proves for every $n\ge1$ that `biasP n` lies in the half-open interval and is the only power of $1/2$ there. At $n=0$ the interval is undefined and the value is $1$; no statement uses it.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §6.2 Biased Random Oracle, p.28 (PDF p.30)

import Mathlib

namespace CertRandQROM

/-- **The bias of Construction 6.2** (§6.2, p.28 of Coladangelo et al., arXiv:2608.31112,
sha256 b75095a2…): "the unique bias `1/(80√n) < p ≤ 1/(40√n)` which is a power of `1/2`",
`p = (1/2)^d` with `d = ⌈log₂(40√n)⌉`.

**Formalization Note** For `n ≥ 1` this is the unique power of `1/2` in the half-open interval
(proved in `Solutions/verification/CertRandQROM_sanity.lean`). At `n = 0` the paper's interval
is undefined and the value is `1`; no statement uses it there. -/
noncomputable def biasP (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ ⌈Real.logb 2 (40 * Real.sqrt n)⌉₊

end CertRandQROM


