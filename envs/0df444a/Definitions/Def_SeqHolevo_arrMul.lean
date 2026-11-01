-- Prove2me | Definitions.Def_SeqHolevo_arrMul
-- name    : SeqHolevo_arrMul
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:58.873212+00:00
-- url     : https://prove2.me/theorems/debdfc80-c3a8-46c3-adf8-24ba9b798788
-- title:
--   Product $XY$ of two coefficient arrays
-- statement:
--   For operators given by their coefficient arrays $X,Y$ on $\ell^2(J)$, the product is
--
--   $$(XY)_{ab}=\sum_{c\in J}X_{ac}Y_{cb}.$$
--
--   It is used for $\Pi\rho^{\otimes n}\Pi$, $\sqrt\Lambda\,\rho_x\sqrt\Lambda$ and the ordered products $\Pi_N\cdots\Pi_1$.
--
--   **Formalization Note** The sum is an unconditional series, which Lean sets to $0$ when it does not converge. Every product formed in the mission has a bounded left factor and a bounded or trace-class right factor, so the series converges absolutely.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix A, p.6 (Π ρ^{⊗n} Π, Lemma 9); Appendix B, p.7 (Sen's bound)

import Mathlib

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendices A–B, pp.6–7 (PDF pages): the operator product `XY` of two coefficient
arrays on ℓ²(J), `(XY)_{ab} = Σ_c X_{ac} Y_{cb}`. It is used for `Π ρ^{⊗n} Π` (p.6),
`√Λ ρ_x √Λ` (Lemma 9, p.6) and `Π_N ⋯ Π_1` (Sen's bound, p.7).

**Formalization Note.** The sum over `c` is an unconditional `tsum`, which is `0` when the
family is not summable. Every product the mission forms has a bounded left factor and a
bounded or trace-class right factor, so the rows of the left factor and the columns of the
right factor are square-summable and the series converges absolutely: no junk value occurs. -/
noncomputable def arrMul {J : Type} (X Y : Matrix J J ℂ) : Matrix J J ℂ :=
  fun a b => ∑' c, X a c * Y c b

end SeqHolevo


