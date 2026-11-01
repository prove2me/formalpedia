-- Prove2me | Definitions.Def_SeqHolevo_vecNormSq
-- name    : SeqHolevo_vecNormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:01.816024+00:00
-- url     : https://prove2.me/theorems/6bfe439b-3468-41c3-9e45-360b5f979a09
-- title:
--   Squared norm $\|v\|^2$ of a coefficient vector
-- statement:
--   The squared norm of a coefficient vector $v$ on $\ell^2(J)$:
--
--   $$\|v\|^2=\sum_{a\in J}|v_a|^2.$$
--
--   For an orthogonal projector $\Pi$ and a unit vector $|\varphi\rangle$, $\operatorname{Tr}\{\Pi\varphi\Pi\}=\|\Pi|\varphi\rangle\|^2$; this is how the mission writes $\mathbb E\operatorname{Tr}\{\Pi\varphi_{X^n(M)}\Pi\}$.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, pp.6–7

import Mathlib

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, pp.6–7 (PDF pages): the squared norm `‖v‖² = Σ_a |v_a|²` of a coefficient
vector on ℓ²(J). For an orthogonal projector `Π` and a unit vector `|φ⟩` with `φ = |φ⟩⟨φ|`,
`Tr{Π φ Π} = ‖Π|φ⟩‖²`, the form in which the mission writes `E Tr{Π φ_{Xⁿ(M)} Π}`.

**Formalization Note.** Unconditional `tsum` of nonnegative reals; it is applied only to
square-summable vectors. -/
noncomputable def vecNormSq {J : Type} (v : J → ℂ) : ℝ :=
  ∑' a, Complex.normSq (v a)

end SeqHolevo


