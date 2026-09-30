-- Prove2me | Definitions.Def_TranscendenceTheory_AnalyticOrbitMultiplicityData
-- name    : TranscendenceTheory_AnalyticOrbitMultiplicityData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T19:01:07.640288+00:00
-- url     : https://prove2.me/theorems/7f7e0eb7-be15-4366-9ab9-5b22e8284792
-- title:
--   Analytic orbit data for transverse component multiplicities
-- statement:
--   For natural numbers $T,e$, `AnalyticOrbitMultiplicityData T e` consists of a commutative Noetherian $\mathbb Q$-algebra $R$, ideals $I,\mathfrak p$ with $\mathfrak p$ a minimal prime over $I$, and a $\mathbb Q$-derivation $D$ of $R$.
--
--   It also supplies an algebra homomorphism $\Phi:R\to (\mathbb C\to\mathbb C)$ and a point $z_0\in\mathbb C$. Multiplication and addition in the target are pointwise. For every $r\in R$, the germs of $\Phi(Dr)$ and $(\Phi r)'$ at $z_0$ agree. Every element of $\mathfrak p$ evaluates to zero at $z_0$.
--
--   There is an element $f\in\mathfrak p$ such that $\Phi f$ is analytic at $z_0$ and has finite analytic order there, equivalently an analytic germ which is not identically zero near $z_0$. No transverse equation $q\in\mathfrak p$ with $Dq\notin\mathfrak p$ is included in the data.
--
--   Finally, the data satisfy
--
--   $$
--   D^j g\in\mathfrak p\quad(g\in I,\ 0\le j\le T),
--   \qquad
--   \operatorname{length}_{R_{\mathfrak p}}(R_{\mathfrak p}/IR_{\mathfrak p})\le e.
--   $$
--
--   **Formalization Note.** The analytic transversality theorem constructs the missing transverse equation from these data. This is an explicit sufficient analytic-coordinate route. No converse for arbitrary abstract minimal-prime witnesses is asserted. Constructing these data from the Weierstrass geometric hypotheses, and bounding the sum of the local lengths by the bidegrees, remain obligations of the Open child theorem.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Lemma 4.6, p. 378, and Proposition 4.7, pp. 378-379. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. One-direction analytic auxiliary criterion for the transverse equation: a nonzero analytic germ on an orbit through the prime yields a first derivative leaving it. This is not the full tangent-rank assertion of Lemma 4.6. Taylor-order characterization: Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Analysis/Analytic/Order.lean, analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero. Geometric orbit and prime selection and the total degree budget remain open.

import Definitions.Def_TranscendenceTheory_MinimalPrimeMultiplicityData
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

open scoped Topology

noncomputable section
namespace TranscendenceTheory

/-- Minimal-prime multiplicity data with an analytic orbit through the prime.
The transverse equation is not supplied: it is constructed by the first
derivative iterate that leaves the prime. -/
structure AnalyticOrbitMultiplicityData (T e : ℕ) where
  R : Type
  [commRing : CommRing R]
  [algebra : Algebra ℚ R]
  [noetherian : IsNoetherianRing R]
  I : Ideal R
  p : Ideal R
  [prime : p.IsPrime]
  minimal : p ∈ I.minimalPrimes
  D : Derivation ℚ R R
  φ : R →ₐ[ℚ] (ℂ → ℂ)
  z : ℂ
  deriv_compat : ∀ r, φ (D r) =ᶠ[𝓝 z] deriv (φ r)
  point_on_prime : ∀ r ∈ p, φ r z = 0
  f : R
  f_mem : f ∈ p
  analytic : AnalyticAt ℂ (φ f) z
  nonzero_germ : analyticOrderAt (φ f) z ≠ ⊤
  jets : ∀ f ∈ I, ∀ k ≤ T, (D^[k]) f ∈ p
  length_le : Module.length (Localization.AtPrime p)
    ((Localization.AtPrime p) ⧸ I.map
      (algebraMap R (Localization.AtPrime p))) ≤ (e : ℕ∞)

attribute [instance] AnalyticOrbitMultiplicityData.commRing AnalyticOrbitMultiplicityData.algebra
  AnalyticOrbitMultiplicityData.noetherian AnalyticOrbitMultiplicityData.prime

end TranscendenceTheory


