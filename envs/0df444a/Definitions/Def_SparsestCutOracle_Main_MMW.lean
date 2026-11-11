-- Prove2me | Definitions.Def_SparsestCutOracle_Main_MMW
-- name    : SparsestCutOracle_Main_MMW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:43:51.640577+00:00
-- url     : https://prove2.me/theorems/583618df-31e8-48cf-b264-e1211ea3c02b
-- title:
--   Exponential Gram iterates, general dual multipliers, and Gram accuracy
-- statement:
--   Let $\Gamma=D_\pi^{-1/2}$. The exponential Gram matrix and the zero-based current iterate are
--
--   $$X(A)=\Pi\Gamma\frac{\exp A}{\operatorname{Tr}(\exp A)}\Gamma,\qquad
--   X^{(t)}=X\!\left(-\frac\eta\rho\Gamma\sum_{s<t}Z^{(s)}\Gamma\right).$$
--
--   Matrix exponential is a mathematical definition, not a free machine instruction. General dual variables include path multipliers, the centering multiplier, and both normalization multipliers. The corrected average adds $\alpha/(5\Pi)$ to the multiplier of $-D_\pi$. Gram accuracy records exact weighted normalization and multiplicative errors in every squared norm and pairwise squared distance. Positive weights and nonzero denominators are supplied by the theorem hypotheses.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 15, 17, 25–26, 55–57, Algorithm 1 and Lemmas 8–9

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Geometry

namespace SparsestCutOracle.Main

noncomputable def Gamma {n : ℕ} (π : Fin n → ℝ) : Mat n :=
  Matrix.diagonal fun i => (Real.sqrt (π i))⁻¹

noncomputable def matrixExp {n : ℕ} (A : Mat n) : Mat n := NormedSpace.exp A

noncomputable def exponentialGram {n : ℕ} (π : Fin n → ℝ) (A : Mat n) : Mat n :=
  totalWeight π • (Gamma π * ((Matrix.trace (matrixExp A))⁻¹ • matrixExp A) * Gamma π)

/-- Arbitrary dual multipliers, including the distinguished upper-normalization coordinate.
They are not restricted to the oracle's special x=α/Π, u=0 responses. -/
structure DualVariables (n : ℕ) where
  paths : List (Fin n) →₀ ℝ
  z : ℝ
  x : ℝ
  u : ℝ

def DualNonnegative {n : ℕ} (cP : ℕ) (y : DualVariables n) : Prop :=
  (∀ p, 0 ≤ y.paths p) ∧ (∀ p, y.paths p ≠ 0 → p.length ≤ cP * n) ∧
  0 ≤ y.z ∧ 0 ≤ y.x ∧ 0 ≤ y.u

noncomputable def dualMatrix {n : ℕ} (π : Fin n → ℝ) (y : DualVariables n) : Mat n :=
  y.paths.sum (fun p f => f • pathMatrix p) - y.z • J π + (y.x - y.u) • D π

def dualValue {n : ℕ} (π : Fin n → ℝ) (y : DualVariables n) : ℝ :=
  (y.x - y.u) * totalWeight π

/-- Algorithm 1, with zero-based iteration t: the sum is over s<t, so the first matrix is I/n. -/
noncomputable def mmwIterate {n : ℕ} (π : Fin n → ℝ) (ρ η : ℝ)
    (Z : ℕ → Mat n) (t : ℕ) : Mat n :=
  exponentialGram π ((-(η / ρ)) • (Gamma π * (∑ s ∈ Finset.range t, Z s) * Gamma π))

/-- The final correction is α/(5Π) on the multiplier of -Dπ, exactly as in Lemma 9's proof. -/
noncomputable def correctedAverage {n : ℕ} (π : Fin n → ℝ) (α : ℝ)
    (y : ℕ → DualVariables n) (T : ℕ) : DualVariables n where
  paths := (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (y t).paths
  z := (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (y t).z
  x := (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (y t).x
  u := (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, (y t).u) + α / (5 * totalWeight π)

/-- Multiplicative Gram accuracy is stated in terms of norms and squared distances, independently
of a chosen Gram representation or its ambient dimension. -/
def GramAccuracy {n : ℕ} (π : Fin n → ℝ) (X Xtilde : Mat n) (γ : ℝ) : Prop :=
  Xtilde.PosSemidef ∧ dot (D π) Xtilde = totalWeight π ∧
  (∀ i, |Xtilde i i - X i i| ≤ γ * Xtilde i i) ∧
  (∀ i j, |sqdist Xtilde i j - sqdist X i j| ≤ γ * sqdist Xtilde i j)

noncomputable def vectorDimension (s : State) : ℕ := (outInt s 0).toNat

noncomputable def vectorGram (n : ℕ) (s : State) : Mat n :=
  fun i j => ∑ k ∈ Finset.range (vectorDimension s),
    outReal s (i.val * vectorDimension s + k) * outReal s (j.val * vectorDimension s + k)

noncomputable def gramInput {n : ℕ} (π : Fin n → ℝ) (L γ : ℝ) : State :=
  init [(n : ℤ)] (((List.finRange n).map π) ++ [L, γ])

end SparsestCutOracle.Main


