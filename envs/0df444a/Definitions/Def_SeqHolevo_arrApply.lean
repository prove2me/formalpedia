-- Prove2me | Definitions.Def_SeqHolevo_arrApply
-- name    : SeqHolevo_arrApply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:59.595094+00:00
-- url     : https://prove2.me/theorems/f694f05e-4a27-412e-994b-7ee23f19ce66
-- title:
--   Action $Pv$ of an operator on a coefficient vector
-- statement:
--   For an operator with coefficient array $P$ on $\ell^2(J)$ and a coefficient vector $v$,
--
--   $$(Pv)_a=\sum_{b\in J}P_{ab}\,v_b.$$
--
--   It gives the projected codeword $\Pi|\varphi_{x^n}\rangle$ of the smoothed channel $x^n\mapsto\Pi\varphi_{x^n}\Pi$.
--
--   **Formalization Note** For a bounded operator and a square-summable vector the series converges absolutely.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, pp.6–7

import Mathlib

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, pp.6–7 (PDF pages): the action `(Pv)_a = Σ_b P_{ab} v_b` of an operator,
given by its coefficient array `P` on ℓ²(J), on a coefficient vector `v`. It gives the
projected codeword `Π|φ_{xⁿ}⟩` of the smoothed channel `xⁿ ↦ Π φ_{xⁿ} Π`.

**Formalization Note.** Unconditional `tsum`; for a bounded operator (every row square-summable)
and a square-summable `v` the series converges absolutely, so no junk value occurs where the
mission uses it. -/
noncomputable def arrApply {J : Type} (P : Matrix J J ℂ) (v : J → ℂ) : J → ℂ :=
  fun a => ∑' b, P a b * v b

end SeqHolevo


