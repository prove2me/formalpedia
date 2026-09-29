-- Prove2me | Definitions.Def_AlgebraicCurve_CanonicalDivisor
-- name    : AlgebraicCurve_CanonicalDivisor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/cc2db6a8-1239-5e80-8950-f16390156697
-- title:
--   Canonical divisor, canonical class and genus of a function field
-- statement:
--   Throughout, $F/K$ is an extension of fields and $\Omega[F\!\restriction\!K]$ denotes Mathlib's module of Kähler differentials. Places, divisors and the Picard group are those of the project's divisor-class formalism: a place $v$ is a proper valuation subring of $F$ containing the image of $K$ whose ideals are principal, a divisor is a finitely supported function $\mathrm{Place}\,K\,F \to \mathbb{Z}$, $\mathrm{Pic}\,K\,F$ is the quotient of the divisor group by the subgroup of principal divisors, and $\deg$ sends $v$ to $[\,$residue field of $v : K\,]$. For a differential $\omega$, $v.\mathrm{ordDifferential}\,\omega$ is $\mathrm{ord}_v$ of the coefficient of $\omega$ with respect to the differential $d\pi_v$ of a chosen uniformiser at $v$ (and $\mathrm{ord}_v 0 = 0$ by convention).
--
--   The class `HasCanonicalDivisor` is a Prop-valued hypothesis class carrying one field: for every $\omega \neq 0$ there exists a divisor $D$ with $D(v) = v.\mathrm{ordDifferential}\,\omega$ at every place $v$ — that is, the family $(\mathrm{ord}_v \omega)_v$ has finite support. Under this assumption, `canonicalDivisorOf` extracts such a divisor from a proof that $\omega \neq 0$, and `canonicalDivisorOf_apply` records its defining property $(\omega)(v) = v.\mathrm{ordDifferential}\,\omega$.
--
--   `canonicalClass K F` is the image in $\mathrm{Pic}\,K\,F$ of the canonical divisor of a chosen nonzero differential, and is $0$ when $\Omega[F\!\restriction\!K]$ vanishes. `genus K F` is the natural number $\bigl\lfloor (\deg(\omega) + 2)^{+}/2 \bigr\rfloor$ for that same chosen $\omega$ (truncation of the integer to $\mathbb{N}$ followed by natural-number division by $2$), and $0$ when there is no nonzero differential; it inverts the relation $\deg(\omega) = 2g-2$. Independence of `canonicalClass` and `genus` of the chosen $\omega$ is not asserted here.
--
--   **Relation to Mathlib.** The module of Kähler differentials is Mathlib's; places, divisors, degrees and the Picard group are the project's own, and the canonical divisor, canonical class and genus of a function field have no Mathlib counterpart. The existence of the canonical divisor is taken here as a hypothesis class rather than proved.
--
--   **Where it is used.** These definitions supply the canonical class and the genus in the function-field language used for modular curves, where the genus and the degree of the canonical divisor enter the Riemann–Roch-type estimates of the modular-curve development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean

import Mathlib
import Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

class HasCanonicalDivisor : Prop where
  exists_divisor : ∀ ω : Ω[F⁄K], ω ≠ 0 → ∃ D : Divisor K F,
    ∀ v : Place K F, D v = v.ordDifferential ω

def canonicalDivisorOf [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Divisor K F :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose

theorem canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) :
    canonicalDivisorOf hω v = v.ordDifferential ω :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose_spec v

def canonicalClass (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : Pic K F :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0 then QuotientAddGroup.mk (canonicalDivisorOf h.choose_spec)
  else 0

def genus (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0
  then (Divisor.degree (canonicalDivisorOf h.choose_spec) + 2).toNat / 2
  else 0

end AlgebraicCurve

end


