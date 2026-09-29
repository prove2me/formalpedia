-- Prove2me | Definitions.Def_beukersLiftingData
-- name    : beukersLiftingData
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T16:29:40.886012+00:00
-- url     : https://prove2.me/theorems/7000e687-f0cd-445d-90fd-8de76b9ed962
-- title:
--   Polynomial relation bases and minimal scalar equations for Beukers lifting
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Lemma 3.1 and Theorem 3.2.

import Definitions.Def_rationalEArithmetic

noncomputable section
namespace ArithmeticE

/-- A polynomial relation basis with a polynomial left inverse. -/
def RelationBasis {m : ℕ} (f : Fin m → PowerSeries ℂ) : Prop :=
  ∃ (r : ℕ) (C U : Fin r → Fin m → Polynomial ℂ),
    (∀ j, ∑ i, (C j i : PowerSeries ℂ) * f i = 0) ∧
    (∀ p : Fin m → Polynomial ℂ, (∑ i, (p i : PowerSeries ℂ) * f i = 0) →
      ∃ b : Fin r → Polynomial ℂ, ∀ i, p i = ∑ j, b j * C j i) ∧
    (∀ j k, ∑ i, U j i * C k i = if j = k then 1 else 0)

/-- Applying a scalar polynomial differential operator to a formal series. -/
def operatorValue (p : ℕ → Polynomial ℂ) (n : ℕ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  ∑ k ∈ Finset.range (n+1), (p k : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[k] F

/-- A nonzero scalar equation with least possible differential order, over complex polynomials. -/
def MinimalEquation (p : ℕ → Polynomial ℂ) (n : ℕ) (F : PowerSeries ℂ) : Prop :=
  p n ≠ 0 ∧ operatorValue p n F = 0 ∧
    ∀ k < n, ∀ q : ℕ → Polynomial ℂ, q k ≠ 0 → operatorValue q k F ≠ 0

end ArithmeticE


