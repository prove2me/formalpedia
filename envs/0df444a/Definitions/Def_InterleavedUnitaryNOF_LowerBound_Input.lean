-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_Input
-- name    : InterleavedUnitaryNOF_LowerBound_Input
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:23.32559+00:00
-- url     : https://prove2.me/theorems/49969efc-2cc2-4d65-88c0-9790ca9ad761
-- title:
--   Complex IUP inputs, exact decoder and dimension schedules
-- statement:
--   The IUP input model uses all complex square matrices, with $W=A_1B_1C_1D_1E_1A_2B_2C_2D_2E_2$. It defines the Frobenius near-unitarity promise and the partial answer at normalized real trace thresholds $0.1$ and $0.9$.
--
--   $$\operatorname{dec}(a)=-2a_{b+2}+\sum_{r=1}^{b+1}2^{r-1-b}a_r,\qquad b=\lceil\log_2n\rceil.$$
--
--   Two consecutive blocks give a complex entry, in row-major matrix order. The eventual dimension schedule includes every fitting power-of-two $\Theta(\sqrt{n/\log_2n})$ choice. Off-length bit access is zero only to make the unused small-length convention total.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Definitions 1.1, 2.1 and §2, pp.2,6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib

namespace InterleavedUnitaryNOF.LowerBound

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℂ
abbrev MatrixInput (m : ℕ) := (Fin 4 → Mat m) × (Fin 4 → Mat m) × (Fin 2 → Mat m)

/-- Exact integer ceiling of log₂ n; the unused small-length convention is b(0)=0. -/
def precision (n : ℕ) : ℕ := Nat.clog 2 n

/-- Out-of-range bits are zero. Fitting schedules never use this convention eventually. -/
def bitAt {n : ℕ} (x : Bits n) (k : ℕ) : ℝ :=
  if h : k < n then if x ⟨k,h⟩ then 1 else 0 else 0

/-- Two's complement, with the sign in the final position of a block. -/
noncomputable def decodeReal {n : ℕ} (x : Bits n) (start : ℕ) : ℝ :=
  -2 * bitAt x (start + precision n + 1) +
    ∑ r ∈ Finset.range (precision n + 1),
      (2 : ℝ)^r / (2 : ℝ)^(precision n) * bitAt x (start + r)

noncomputable def decodeMatrix {n : ℕ} (m : ℕ) (x : Bits n) (a : ℕ) : Mat m :=
  fun i j =>
    let start := 2 * (precision n + 2) * (a * m * m + i.val * m + j.val)
    ⟨decodeReal x start, decodeReal x (start + precision n + 2)⟩

noncomputable def decode {n : ℕ} (m : ℕ) (x y z : Bits n) : MatrixInput m :=
  (fun a => decodeMatrix m x a.val, fun a => decodeMatrix m y a.val,
   fun a => decodeMatrix m z a.val)

/-- A₁ B₁ C₁ D₁ E₁ A₂ B₂ C₂ D₂ E₂, exactly in the source order. -/
noncomputable def word {m : ℕ} (u : MatrixInput m) : Mat m :=
  u.1 0 * u.2.1 0 * u.1 1 * u.2.1 1 * u.2.2 0 *
  u.1 2 * u.2.1 2 * u.1 3 * u.2.1 3 * u.2.2 1

noncomputable def frobenius {m : ℕ} (a : Mat m) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖a i j‖^2)

noncomputable def nearUnitary {m : ℕ} (a : Mat m) : Prop :=
  frobenius (a.conjTranspose * a - 1) ≤ (1 : ℝ)/10000

noncomputable def promisedMatrices {m : ℕ} (u : MatrixInput m) : Prop :=
  (∀ a, nearUnitary (u.1 a)) ∧ (∀ a, nearUnitary (u.2.1 a)) ∧
  (∀ a, nearUnitary (u.2.2 a))

noncomputable def normalizedTrace {m : ℕ} (u : MatrixInput m) : ℝ :=
  (Matrix.trace (word u)).re / m

/-- The partial Boolean promise problem, including both threshold endpoints. -/
noncomputable def iup {n : ℕ} (m : ℕ) (x y z : Bits n) : Option Bool := by
  classical
  let u := decode m x y z
  exact if promisedMatrices u then
    if normalizedTrace u ≤ (1 : ℝ)/10 then some false
    else if (9 : ℝ)/10 ≤ normalizedTrace u then some true else none
    else none

/-- Every eventually fitting power-of-two Θ(√(n/log₂ n)) schedule is allowed. -/
def AdmissibleSchedule (m : ℕ → ℕ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
    (∃ q : ℕ, m n = 2^q) ∧
    8 * (precision n + 2) * (m n)^2 ≤ n ∧
    a * Real.sqrt ((n : ℝ) / Real.logb 2 n) ≤ m n ∧
    (m n : ℝ) ≤ b * Real.sqrt ((n : ℝ) / Real.logb 2 n)

end InterleavedUnitaryNOF.LowerBound


