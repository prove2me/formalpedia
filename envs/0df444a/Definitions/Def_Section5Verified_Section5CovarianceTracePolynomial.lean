-- Prove2me | Definitions.Def_Section5Verified_Section5CovarianceTracePolynomial
-- name    : Section5Verified_Section5CovarianceTracePolynomial
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:45.264498+00:00
-- url     : https://prove2.me/theorems/2e8d23a9-ad5d-42b6-837b-3f5230d1866f
-- title:
--   Section5CovarianceTracePolynomial — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5CovarianceTracePolynomial; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

namespace Section5SignMoments

variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]



noncomputable def covariancePolynomial (S : Matrix ι ι ℝ) :
    Matrix ι ι (MvPolynomial (J × ι) ℝ) := fun i j =>
  MvPolynomial.C ((Fintype.card J : ℝ)⁻¹)*
    (∑ r : J, MvPolynomial.X (r,i)*MvPolynomial.X (r,j))-MvPolynomial.C (S i j)

noncomputable def centeredCovariance (S : Matrix ι ι ℝ) (a : J → ι → ℝ) :
    Matrix ι ι ℝ := fun i j => (Fintype.card J : ℝ)⁻¹*(∑ r : J, a r i*a r j)-S i j





noncomputable def covarianceTracePolynomial (S : Matrix ι ι ℝ) (p : ℕ) :
    MvPolynomial (J × ι) ℝ := Matrix.trace ((covariancePolynomial S)^(2*p))





end Section5SignMoments

end


