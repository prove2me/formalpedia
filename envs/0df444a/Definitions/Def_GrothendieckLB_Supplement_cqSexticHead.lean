-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqSexticHead
-- name    : GrothendieckLB_Supplement_cqSexticHead
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T17:27:42.020544+00:00
-- url     : https://prove2.me/theorems/f50b26a1-298d-41c6-b953-d07b95c8a0c7
-- title:
--   Sextic moment representation for the finite cubic–quintic coefficient computation
-- statement:
--   The polynomials $P_{ab}$ are the polynomial factors of the one-dimensional sextic integrals obtained by Gaussian integration by parts. Applying a moment sequence $M_k$ to their monomials and dividing by $\pi\sqrt{a!b!}$ gives the Hermite coefficient used in the finite Taylor formula. The three rational cells of width $2^{-384}$ enclose $M_0,M_2,M_4$ at the published parameters.
-- source:
--   Saha et al., arXiv:2608.11158v2, Theorem 5.1 and Appendix C.1. The three starting intervals are obtained by a rational polynomial differential-residual certificate for the sextic density.

import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_GrothendieckLB_Supplement_cqRhoPoly

open Polynomial
namespace GrothendieckLB.Supplement

/-- The polynomial multiplying the common sextic weight after Gaussian integration by parts.
The first index is the Hermite degree in the threshold coordinate. -/
noncomputable def cqSexticPoly (s : ℝ) : ℕ → ℕ → ℝ[X]
  | 0, 0 => 0
  | 0, b+1 => C (3*s) * (X^2-1) * ((hermite b).map (Int.castRingHom ℝ))
  | a+1, b => ((hermite a).map (Int.castRingHom ℝ)).comp
      (C (-s) * (X^3-C 3*X)) * ((hermite b).map (Int.castRingHom ℝ))

/-- Recover one normalized Hermite coefficient by applying the moment functional to its polynomial. -/
noncomputable def cqHermiteFromMoments (s : ℝ) (M : ℕ → ℝ) (a b : ℕ) : ℝ :=
  (cqSexticPoly s a b).sum (fun k c => c*M k) /
    (Real.pi * Real.sqrt (a.factorial : ℝ) * Real.sqrt (b.factorial : ℝ))

/-- The finite Hermite formula for a head coefficient, evaluated on a sequence of sextic moments. -/
noncomputable def cqHeadFromMoments (M : ℕ → ℝ) (m : ℕ) : ℝ :=
  let s := 0.136419125 / Real.sqrt (6*(1+(0.34101124:ℝ)^2+0.05276111^2))
  Real.pi/2 * ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
    (-1:ℝ)^b * (cqHermiteFromMoments s M a b)^2 *
      (cqRhoPoly 0.34101124 0.05276111 ^ a).coeff (m-b)

/-- Rational enclosures for the three starting integrals, each of width two to the power minus 384. -/
def cqSexticSeedBounds (M : ℕ → ℝ) : Prop :=
  let cell (k lower : ℕ) := (lower:ℝ) ≤ 2^384*M k ∧ 2^384*M k ≤ (lower:ℝ)+1
  cell 0 98100829642129577717705252461250802877285043994588462406870607474137489297660729170734376455389328977175112900544138 ∧
  cell 2 95020680131779427752407447234488278202461530610309981184152310885588522728819096259031464439548105786990997297548714 ∧
  cell 4 262876500006536681973879627718902500274060155065983995563998798928285304964789315907500644382597812284962670046502317

end GrothendieckLB.Supplement


