-- Prove2me | Definitions.Def_BorderDiffEq_SigmaWedgeSigma
-- name    : BorderDiffEq_SigmaWedgeSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:05.143814+00:00
-- url     : https://prove2.me/theorems/f0e52379-816f-4ff1-b828-b6f7f8a7e740
-- title:
--   $\Sigma\wedge\Sigma$ circuits (sums of powers of affine forms)
-- statement:
--   A **$\Sigma\wedge\Sigma$ circuit** over a commutative ring $K$ computes
--   $$
--   \sum_{j=1}^{w}c_j\,\ell_j^{\,e_j},\qquad c_j\in K,\ \ell_j \text{ affine linear},\ e_j\in\mathbb N .
--   $$
--   Its **top fan-in** is $w$ and its **formal degree** is $\max_j e_j$. The class $\Sigma^{[w]}\wedge\Sigma$ has top fan-in at most $w$; $\Sigma\wedge\Sigma(w,e)$ additionally requires $e_j\le e$ for all $j$.
--
--   These circuits express the coefficients of the paper's differential equation (Lemma 5.3, Proposition 5.4) and are converted into ABPs by Lemma 4.10.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §4, p.23

import Mathlib
import Definitions.Def_BorderDiffEq_AffineForm

namespace BorderDiffEq

/-- **Σ∧Σ circuits (sums of powers of affine forms)** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), §4, p.23): polynomials of the form `∑_{j=1}^{w} cⱼ ℓⱼ^{eⱼ}` with `cⱼ ∈ K` and
`ℓⱼ` affine linear. The top fan-in is `w` and the formal degree is `maxⱼ eⱼ`.

**Formalization Note.** The class `Σ^{[w]}∧Σ` is "top fan-in at most `w`" and `Σ∧Σ(w, e)` adds
"every `eⱼ ≤ e`". -/
structure SigmaWedgeSigma (K : Type) (σ : Type) where
  /-- the number of summands (top fan-in) -/
  w : ℕ
  /-- the scalar coefficients -/
  c : Fin w → K
  /-- the affine forms -/
  ℓ : Fin w → AffineForm K σ
  /-- the exponents -/
  e : Fin w → ℕ

namespace SigmaWedgeSigma

variable {K σ : Type}

/-- The polynomial `∑ⱼ cⱼ ℓⱼ^{eⱼ}`. -/
noncomputable def eval [CommRing K] [Fintype σ] (Φ : SigmaWedgeSigma K σ) : MvPolynomial σ K :=
  ∑ j, MvPolynomial.C (Φ.c j) * (Φ.ℓ j).toPoly ^ Φ.e j

/-- The top fan-in. -/
def topFanIn (Φ : SigmaWedgeSigma K σ) : ℕ := Φ.w

/-- The formal degree `maxⱼ eⱼ` (`0` for the empty sum). -/
def formalDeg (Φ : SigmaWedgeSigma K σ) : ℕ := Finset.univ.sup Φ.e

end SigmaWedgeSigma

end BorderDiffEq


