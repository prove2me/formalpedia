-- Prove2me | Definitions.Def_CertRandQROM_Supplement_leverLam
-- name    : CertRandQROM_Supplement_leverLam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:45:22.979819+00:00
-- url     : https://prove2.me/theorems/0c4130a8-d512-46d6-b1a4-43be2678e1e9
-- title:
--   The enlarged parameter $\lambda(\lambda',h'_\infty)=\max\{\lambda',\lceil(3h'_\infty)^{1/c}\rceil\}$ of Construction 6.4
-- statement:
--   For a constant $c\in(0,\tfrac12)$, a security parameter $\lambda'$ and a min-entropy threshold $h'_\infty$, Construction 6.4 runs Construction 6.2 at the security parameter
--
--   $$
--   \lambda(\lambda',h'_\infty)=\max\Big\{\lambda',\ \big\lceil(3h'_\infty)^{1/c}\big\rceil\Big\}.
--   $$
--
--   Then $\lceil\lambda^c/3\rceil\ge h'_\infty$, so the min-entropy guarantee of Construction 6.2 at $\lambda$ gives $h'_\infty$ bits (complexity leveraging).
--
--   **Formalization Note** The power is a real power and the ceiling the natural-number ceiling. The second quantity of Construction 6.4, $h_\infty(\lambda',h'_\infty)=\lceil\lambda(\lambda',h'_\infty)^c/3\rceil$, is only passed to Prove and Verify of Construction 6.2, which ignore it.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Construction 6.4, p.30 (PDF p.32)

import Mathlib

set_option autoImplicit false

namespace CertRandQROM.Supplement

/-- **The enlarged security parameter of Construction 6.4** (p.30 of Coladangelo et al.,
arXiv:2608.31112, sha256 b75095a2…):
`λ(λ′, h′∞) = max{λ′, ⌈(3 h′∞)^{1/c}⌉}`, for the constant `c ∈ (0, 1/2)`.

**Formalization Note** The power is the real power `(3h′)^{1/c}` and the ceiling is the natural
ceiling; at `h′ = 0` the value is `λ′`. The companion threshold
`h∞(λ′, h′∞) = ⌈λ(λ′, h′∞)^c/3⌉` of Construction 6.4 is passed to `Prove` and `Verify` of
Construction 6.2, which ignore it, so it needs no definition. -/
noncomputable def leverLam (c : ℝ) (l' h' : ℕ) : ℕ :=
  max l' ⌈((3 * h' : ℕ) : ℝ) ^ (1 / c)⌉₊

end CertRandQROM.Supplement


