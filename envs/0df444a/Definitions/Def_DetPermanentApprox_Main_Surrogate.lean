-- Prove2me | Definitions.Def_DetPermanentApprox_Main_Surrogate
-- name    : DetPermanentApprox_Main_Surrogate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:25.689115+00:00
-- url     : https://prove2.me/theorems/7a6a41a7-3eff-4763-878f-144f2807b74c
-- title:
--   Rational Taylor recurrence and regularized matching polynomial
-- statement:
--   For rational $K$, set $\rho=1/(4K)$, $z_\star=4K/(4K+1)$, $q=8K/(8K+1)$, and $\beta_m=400Kq^{m+1}/(1-q)$. The matching-size polynomials $M_j$ sum the weight monomials of all $j$-edge matchings. The coefficients $s_\ell$ and $\lambda_\ell$ are the explicit rational recurrence (3.2); $T_m=\sum_{\ell=1}^m z_\star^\ell\lambda_\ell$.
--
--   For positive accuracy $\eta$, $m$ is the least natural index with $2\beta_mK\le\eta$. The surrogate is zero on an empty edge set and otherwise $U=T_m+\beta_m\sum_e w_e$. The degree region requires the sum of incident exponential edge weights at each vertex to be at most $K$. Error and derivatives are functions on the full ambient space of logarithmic weights. This fixes the actual polynomial independently of every convexity or accuracy claim.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), §3, pp. 11–13, equations (3.1)–(3.5) (PDF pp. 11–13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Matchings

open scoped BigOperators

namespace DetPermanentApprox.Main

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev Poly (E : Type) := MvPolynomial E ℚ

noncomputable def rho (K : ℚ) : ℚ := 1 / (4 * K)
noncomputable def zstar (K : ℚ) : ℚ := 4 * K / (4 * K + 1)
noncomputable def qratio (K : ℚ) : ℚ := 8 * K / (8 * K + 1)
noncomputable def beta (K : ℚ) (m : ℕ) : ℚ :=
  400 * K * qratio K ^ (m + 1) / (1 - qratio K)

noncomputable def matchingPolynomial (G : Graph V E) (j : ℕ) : Poly E :=
  ∑ M : Matching G, if M.val.card = j then ∏ e ∈ M.val, MvPolynomial.X e else 0

noncomputable def sCoefficient (G : Graph V E) (K : ℚ) (l : ℕ) : Poly E :=
  ∑ j ∈ Finset.range l,
    MvPolynomial.C (rho K ^ (j + 1) * ((l - 1).choose j : ℚ)) *
      matchingPolynomial G (j + 1)

/-- List entry l-1 is λ_l, using the rational recurrence (3.2), p.12.
In the step l+1 the sum uses only the l already constructed entries. -/
noncomputable def lambdaCoefficients (G : Graph V E) (K : ℚ) : ℕ → List (Poly E)
  | 0 => []
  | l + 1 =>
    let prev := lambdaCoefficients G K l
    prev ++ [sCoefficient G K (l + 1) -
      MvPolynomial.C (1 / ((l + 1 : ℕ) : ℚ)) *
        ∑ j ∈ Finset.range l,
          MvPolynomial.C ((j + 1 : ℕ) : ℚ) * prev.getD j 0 * sCoefficient G K (l - j)]

noncomputable def taylorPolynomial (G : Graph V E) (K : ℚ) (m : ℕ) : Poly E :=
  ∑ j ∈ Finset.range m,
    MvPolynomial.C (zstar K ^ (j + 1)) * (lambdaCoefficients G K m).getD j 0

noncomputable def truncationDegree (K : ℚ) (η : ℝ) : ℕ :=
  sInf {j : ℕ | 2 * (beta K j : ℝ) * (K : ℝ) ≤ η}

noncomputable def surrogate (G : Graph V E) (K : ℚ) (η : ℝ) : Poly E :=
  if Fintype.card E = 0 then 0 else
    taylorPolynomial G K (truncationDegree K η) +
      MvPolynomial.C (beta K (truncationDegree K η)) * ∑ e, MvPolynomial.X e

noncomputable def evaluate (P : Poly E) (w : E → ℝ) : ℝ :=
  MvPolynomial.eval₂ (Rat.castHom ℝ) w P

noncomputable def expWeights (y : E → ℝ) : E → ℝ := fun e => Real.exp (y e)

open Classical in
noncomputable def degreeRegion (G : Graph V E) (K : ℝ) : Set (E → ℝ) :=
  {y | ∀ v, (∑ e, if Incident G v e then Real.exp (y e) else 0) ≤ K}

noncomputable def weightSum (w : E → ℝ) : ℝ := ∑ e, w e

noncomputable def errorFunction (G : Graph V E) (K : ℚ) (m : ℕ) (y : E → ℝ) : ℝ :=
  Real.log (Z G (expWeights y)) - evaluate (taylorPolynomial G K m) (expWeights y)

noncomputable def partialR (f : (E → ℝ) → ℝ) (y : E → ℝ) (e : E) : ℝ :=
  fderiv ℝ f y (Pi.single e 1)

noncomputable def partialC (f : (E → ℝ) → ℂ) (y : E → ℝ) (e : E) : ℂ :=
  fderiv ℝ f y (Pi.single e 1)

noncomputable def tau (K : ℚ) (z : ℂ) : ℂ := (rho K : ℂ) * z / (1 - z)

noncomputable def radius (K : ℚ) : ℝ := (1 + (zstar K : ℝ)) / 2

end DetPermanentApprox.Main


