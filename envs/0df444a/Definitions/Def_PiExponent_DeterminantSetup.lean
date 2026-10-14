-- Prove2me | Definitions.Def_PiExponent_DeterminantSetup
-- name    : PiExponent_DeterminantSetup
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-14T07:53:06.28881+00:00
-- url     : https://prove2.me/theorems/7cde3776-46ac-4e3e-95e6-27e215b161a2
-- title:
--   Finite logarithmic jets, successive thresholds, and determinant budgets
-- statement:
--   The module defines surjectivity for finite logarithmic jets of complex multivariate polynomials. Polynomial support has weighted degree at most H, and prescribed jet coefficients have weighted degree strictly below H. The logarithm is represented by its polynomial truncation strictly below ceil(H/v0), which agrees with the formal logarithm on every retained coefficient when the weights are positive. Eventual surjectivity requires a positive divisibility modulus and a degree threshold. Successive separation records thresholds depending only on earlier weights. The determinant budget stores positive geometric and analytic parameters, strict volume inequalities, an explicit common error bound, and strict approximation and collision savings. It contains no approximation assertion or unproved theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.OfFn

open scoped BigOperators

/- Finite logarithmic jets. Polynomial degrees use <= H; jet degrees use < H.
The logarithm is truncated strictly below ceil(H/v0), so every retained jet
coefficient agrees with the coefficient of the formal logarithm. -/
noncomputable def OAI.PiExponent.logJetSurjective
    (m K : ℕ) (w0 v0 theta : ℚ) (w : Fin m → ℕ)
    (c : Fin K → Fin m → ℂ) (H : ℕ) : Prop :=
  let t : MvPolynomial (Fin (m + 1)) ℂ := MvPolynomial.X 0
  let L : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ k ∈ Finset.range (Nat.ceil ((H : ℝ) / (v0 : ℝ))),
      if k = 0 then 0 else
        MvPolynomial.C (((-1 : ℂ) ^ (k + 1)) / (k : ℂ)) * t ^ k
  let subst : Fin K → Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ :=
    fun j => Fin.cases (1 + t)
      (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i.succ + L)
  ∀ J : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ,
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      (∀ d ∈ P.support,
        (w0 : ℝ) * (d 0 : ℝ) +
          (∑ i : Fin m, (w i : ℝ) * (d i.succ : ℝ)) ≤ (H : ℝ)) ∧
      ∀ (j : Fin K) (d : Fin (m + 1) →₀ ℕ),
        (v0 : ℝ) * (d 0 : ℝ) +
          (∑ i : Fin m, ((w i : ℝ) / (theta : ℝ)) * (d i.succ : ℝ)) < (H : ℝ) →
        MvPolynomial.coeff d (MvPolynomial.aeval (subst j) P) = J j d

noncomputable def OAI.PiExponent.eventualLogJetSurjective
    (m K : ℕ) (w0 v0 theta : ℚ) (w : Fin m → ℕ)
    (c : Fin K → Fin m → ℂ) : Prop :=
  ∃ D : ℕ, 0 < D ∧ ∃ H0 : ℕ,
    ∀ H : ℕ, H0 ≤ H → D ∣ H →
      OAI.PiExponent.logJetSurjective m K w0 v0 theta w c H

/- A threshold at index i depends only on the weights before index i. -/
def OAI.PiExponent.separatedWeights (S : List ℕ → ℕ)
    {m : ℕ} (w : Fin m → ℕ) : Prop :=
  ∀ i : Fin m,
    S (List.ofFn (fun k : Fin i.val =>
      w ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩)) ≤ w i

/- Numerical data in the determinant comparison. The error bound replaces
sum_i (1/w_i) by m/wmin; this only increases the error. -/
structure OAI.PiExponent.DeterminantBudget (nu : ℝ) where
  m : ℕ
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  theta : ℚ
  A : ℝ
  eta : ℝ
  F0 : ℝ
  wmin : ℕ
  E : ℝ
  m_pos : 0 < m
  K_pos : 0 < K
  w0_pos : 0 < w0
  v0_pos : 0 < v0
  theta_pos : 0 < theta
  theta_lt_one : theta < 1
  volume_transverse : (K : ℚ) * theta ^ m < 1
  volume_full : (K : ℚ) * (w0 / v0) * theta ^ m < 1
  A_pos : 0 < A
  A_lt_one : A < 1
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  F0_pos : 0 < F0
  F0_large : 2 / (theta : ℝ) < F0
  wmin_pos : 0 < wmin
  E_nonneg : 0 ≤ E
  E_eq : E = nu / F0 +
    ((4 * Real.log 2) * F0 * (m : ℝ) + 2 * Real.log 2) / (v0 : ℝ) +
    100 * (K : ℝ) / (w0 : ℝ) +
    ((4 * Real.log 2) * (m : ℝ) + (theta : ℝ) + Real.log 4 +
      Real.log (2 * (K : ℝ)) + nu + Real.log (200 * (K : ℝ))) / (wmin : ℝ)
  gap_pos : 0 < nu * (A * (1 - eta) - (theta : ℝ)) - (1 - (theta : ℝ))
  error_gap : E < nu * (A * (1 - eta) - (theta : ℝ)) - (1 - (theta : ℝ))
  collision_gap : 1 + E < (Real.log 2 / 4) *
    (eta ^ 2 * (K : ℝ) * (theta : ℝ) ^ m /
      (((m : ℝ) + 1) * (v0 : ℝ) * A ^ m))


