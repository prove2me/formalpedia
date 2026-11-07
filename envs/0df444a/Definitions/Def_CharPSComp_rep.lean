-- Prove2me | Definitions.Def_CharPSComp_rep
-- name    : CharPSComp_rep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:16.825773+00:00
-- url     : https://prove2.me/theorems/24a71cac-d5ac-40b7-80f2-182163b9fc32
-- title:
--   The representative $\mathrm{rep}_h$, coefficient blocks and the block encoding $\widehat P(y)\in E[y]$
-- statement:
--   For a monic $h\in R[z]$ of positive degree, $\mathrm{rep}_h:R[z]/(h)\to R[z]_{<\deg h}$ selects the unique representative of degree less than $\deg h$ (§2.1). For a block width $s$, an entry $P\in R[z]$ is cut into blocks
--   $$P_i(z)\triangleq\sum_{j=0}^{s-1}([z^{si+j}]P)\,z^j,\qquad P=\sum_{i<\tau}z^{si}P_i\ \ (\deg P<s\tau),$$
--   and encoded as $\widehat P(y)\triangleq\sum_{i=0}^{\tau-1}P_i(\bar z)\,y^i\in E[y]$ with $E=R[z]/(h)$ and $\bar z=z\bmod h$ (§3.4).
--
--   This packing of $s$ consecutive coefficients into one element of $E$ is what lets the geometric transforms of §3.3 run on $O(N)$ base coordinates.
--
--   **Formalization Note** $E$ is `AdjoinRoot h`; $\mathrm{rep}_h(x)$ is any lift of $x$ reduced modulo $h$ (`%ₘ`), which for monic $h$ does not depend on the lift.
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §2.1, p.4 (PDF p.5); §3.4, pp.9–10 (PDF pp.10–11)

import Mathlib
import Definitions.Def_CharPSComp_J

namespace CharPSComp

open Polynomial

variable {R : Type*} [CommRing R]

/-- The reduced representative (Zhu, *Faster Power Series Composition in Fixed Positive
Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §2.1, p.4, PDF p.5): for monic
`h` of positive degree, `rep_h : R[z]/(h) → R[z]_{<deg h}` selects the unique polynomial
representative of degree less than `deg h`.

**Formalization Note** Computed as `q mod h` (`%ₘ`) for a chosen lift `q`; for monic `h` the
result does not depend on the lift. -/
noncomputable def rep (h : R[X]) (x : AdjoinRoot h) : R[X] :=
  (AdjoinRoot.mk_surjective x).choose %ₘ h

/-- Coefficient block `i` of width `s` (ibid., §3.4, p.9, PDF p.10):
`P_i(z) ≜ Σ_{j=0}^{s−1} ([z^{si+j}]P(z)) zʲ`. -/
noncomputable def blockOf (s : ℕ) (P : R[X]) (i : ℕ) : R[X] :=
  ∑ j ∈ Finset.range s, C (P.coeff (s * i + j)) * X ^ j

/-- The block encoding (ibid., §3.4, p.10, PDF p.11): `P̂(y) ≜ Σ_{i=0}^{τ−1} P_i(z̄) yⁱ ∈ E[y]`,
where `E = R[z]/(h)` and `z̄ = z mod h`. -/
noncomputable def blockEncode (h : R[X]) (s τ : ℕ) (P : R[X]) : (AdjoinRoot h)[X] :=
  ∑ i ∈ Finset.range τ, C (AdjoinRoot.mk h (blockOf s P i)) * X ^ i

end CharPSComp


