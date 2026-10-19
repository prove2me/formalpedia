-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
-- name    : QAlgorithms_Papers_Independent_Information100_P49
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:48:07.349251+00:00
-- url     : https://prove2.me/theorems/1b34480e-e6b3-4f58-85e4-69929fb59476
-- title:
--   Definitions for Classical Capacity of Single-Mode Bosonic Gaussian Channels
-- statement:
--   The objects the formalized statements of *Classical Capacity of Single-Mode Bosonic Gaussian Channels* (arXiv:2610.22308) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CanonicalParameters`: The nondegenerate canonical parameters of Eq. (6), PDF p.2. The transfer strength is `|tau|`; its sign does not enter the scalar entropy formulas.
--   - `thermalEntropy`: Thermal entropy `g`, Eq. (A3), PDF p.9; `0 log 0 = 0`.
--   - `symplecticEntropy`: The symplectic-eigenvalue entropy `G`, Eq. (7), PDF p.2. Used only at `mu ≥ 1`.
--   - `outputEntropy`: The entropy `h(z,w)` of Eq. (8), PDF p.3.
--   - `selectedSqueezing`: The clamped squeezing parameter of Eq. (9), PDF p.3.
--   - `momentEntropy`: The moment-resolved minimum entropy `epsilon`, Eq. (9), PDF p.3.
--   - `momentDomain`: The admissible raw-second-moment domain, PDF p.3.
--   - `affineEntropyValues`: The constant branch and both tangent regimes in Eq. (18), PDF p.4. The supremum is in `EReal`, so neither emptiness nor unboundedness defaults to a real zero. Derivatives apply to the entire one-variable squeezed-state entropy.
--   - `realChoose`: Generalized real binomial coefficient, used for the polynomial variable in Eq. (H36), PDF p.19. It is a falling factorial divided by `l!`.
--   - `hahnPolynomial`: The actual Hahn polynomial of Eq. (H36), PDF p.19, for `j ≤ n`.
--   - `hahnWeight`: Uniform-grid Hahn weight, Eq. (H36), PDF p.19, used for `j ≤ n`.
--   - `hahnRatio`: The factorial ratio `Z_D` of Eq. (H37), PDF p.19, used for `D < n`.
--   - `hahnFilter`: The constructed filter `p_{n,D}`, Eq. (H37), PDF p.19.
--   - `hahnRate`: The strictly positive rate `r_0(t)` in Eq. (H39), PDF p.19, for `0 < t < 1`.
--   - `newtonCoefficient`: Newton coefficients (forward differences at zero) for the binomial-basis expansion used in Eq. (H23), PDF p.18, and after Eq. (H39), PDF p.19.
-- source:
--   Classical Capacity of Single-Mode Bosonic Gaussian Channels, arXiv:2610.22308v1, https://arxiv.org/abs/2610.22308v1

import Mathlib

/-!
Scalar results from Adesso–Lami–Giovannetti, arXiv:2610.22308v1.
The infinite-dimensional channel results are explicitly deferred in the unit's HARD.md.
All new definitions are local to this paper. Entropies use natural logarithms.
-/

namespace QAlgorithms.Papers.Independent.Information100.P49

open scoped BigOperators

/-- The nondegenerate canonical parameters of Eq. (6), PDF p.2.
The transfer strength is `|tau|`; its sign does not enter the scalar entropy formulas. -/
structure CanonicalParameters where
  tau : ℝ
  xi : ℝ
  y : ℝ
  tau_ne_zero : tau ≠ 0
  xi_pos : 0 < xi
  xi_le_one : xi ≤ 1
  y_pos : 0 < y
  cp : |1 - tau| ≤ y

/-- Thermal entropy `g`, Eq. (A3), PDF p.9; `0 log 0 = 0`. -/
noncomputable def thermalEntropy (v : ℝ) : ℝ :=
  (v + 1) * Real.log (v + 1) - v * Real.log v

/-- The symplectic-eigenvalue entropy `G`, Eq. (7), PDF p.2. Used only at `mu ≥ 1`. -/
noncomputable def symplecticEntropy (mu : ℝ) : ℝ :=
  thermalEntropy ((mu - 1) / 2)

/-- The entropy `h(z,w)` of Eq. (8), PDF p.3. -/
noncomputable def outputEntropy (c : CanonicalParameters) (z w : ℝ) : ℝ :=
  symplecticEntropy (Real.sqrt ((|c.tau| * z + c.y / c.xi) *
    (|c.tau| * w + c.y * c.xi)))

/-- The clamped squeezing parameter of Eq. (9), PDF p.3. -/
noncomputable def selectedSqueezing (c : CanonicalParameters) (z w : ℝ) : ℝ :=
  min z (max (1 / w) (1 / c.xi))

/-- The moment-resolved minimum entropy `epsilon`, Eq. (9), PDF p.3. -/
noncomputable def momentEntropy (c : CanonicalParameters) (z w : ℝ) : ℝ :=
  outputEntropy c (selectedSqueezing c z w) (1 / selectedSqueezing c z w)

/-- The admissible raw-second-moment domain, PDF p.3. -/
def momentDomain : Set (ℝ × ℝ) :=
  {q | 0 < q.1 ∧ 0 < q.2 ∧ 1 ≤ q.1 * q.2}

/-- The constant branch and both tangent regimes in Eq. (18), PDF p.4.
The supremum is in `EReal`, so neither emptiness nor unboundedness defaults to a real zero.
Derivatives apply to the entire one-variable squeezed-state entropy. -/
noncomputable def affineEntropyValues (c : CanonicalParameters) (z w : ℝ) : Set EReal :=
  {a | a = (symplecticEntropy (|c.tau| + c.y) : EReal) ∨
    (∃ u : ℝ, 0 < u ∧ u < 1 / c.xi ∧
      a = ((outputEntropy c u (1 / u) +
        deriv (fun q : ℝ => outputEntropy c q (1 / q)) u * (z - u) : ℝ) : EReal)) ∨
    (∃ v : ℝ, 0 < v ∧ v < c.xi ∧
      a = ((outputEntropy c (1 / v) v +
        deriv (fun q : ℝ => outputEntropy c (1 / q) q) v * (w - v) : ℝ) : EReal))}

example : thermalEntropy 0 = 0 := by
  simp [thermalEntropy]

example : symplecticEntropy 1 = 0 := by
  simp [symplecticEntropy, thermalEntropy]

example (c : CanonicalParameters) : selectedSqueezing c 1 1 = 1 := by
  simp only [selectedSqueezing, div_one]
  exact min_eq_left (le_max_left _ _)

example : ((1, 1) : ℝ × ℝ) ∈ momentDomain := by
  norm_num [momentDomain]

/-- Generalized real binomial coefficient, used for the polynomial variable in
Eq. (H36), PDF p.19. It is a falling factorial divided by `l!`. -/
noncomputable def realChoose (x : ℝ) (l : ℕ) : ℝ :=
  (∏ i ∈ Finset.range l, (x - (i : ℝ))) / (l.factorial : ℝ)

/-- The actual Hahn polynomial of Eq. (H36), PDF p.19, for `j ≤ n`. -/
noncomputable def hahnPolynomial (n j : ℕ) (x : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1), (-1 : ℝ) ^ l *
    (j.choose l : ℝ) * ((j + l).choose l : ℝ) * realChoose x l / (n.choose l : ℝ)

/-- Uniform-grid Hahn weight, Eq. (H36), PDF p.19, used for `j ≤ n`. -/
noncomputable def hahnWeight (n j : ℕ) : ℝ :=
  ((2 * j + 1 : ℕ) : ℝ) * (n.factorial : ℝ) ^ 2 /
    (((n - j).factorial : ℝ) * ((n + j + 1).factorial : ℝ))

/-- The factorial ratio `Z_D` of Eq. (H37), PDF p.19, used for `D < n`. -/
noncomputable def hahnRatio (n D : ℕ) : ℝ :=
  (n.factorial : ℝ) ^ 2 /
    (((n - D - 1).factorial : ℝ) * ((n + D + 1).factorial : ℝ))

/-- The constructed filter `p_{n,D}`, Eq. (H37), PDF p.19. -/
noncomputable def hahnFilter (n D : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (D + 1), hahnWeight n j * hahnPolynomial n j x) /
    (1 - hahnRatio n D)

/-- The strictly positive rate `r_0(t)` in Eq. (H39), PDF p.19, for `0 < t < 1`. -/
noncomputable def hahnRate (t : ℝ) : ℝ :=
  ((1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t)) / 2

/-- Newton coefficients (forward differences at zero) for the binomial-basis
expansion used in Eq. (H23), PDF p.18, and after Eq. (H39), PDF p.19. -/
noncomputable def newtonCoefficient (p : ℝ → ℝ) (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (s + 1), (-1 : ℝ) ^ (s - i) * (s.choose i : ℝ) * p (i : ℝ)

example (x : ℝ) : realChoose x 0 = 1 := by
  simp [realChoose]

example (n : ℕ) (x : ℝ) : hahnPolynomial n 0 x = 1 := by
  simp [hahnPolynomial, realChoose]

example (x : ℝ) : hahnFilter 1 0 x = 1 := by
  norm_num [hahnFilter, hahnRatio, hahnWeight, hahnPolynomial, realChoose,
    Nat.factorial]

example (p : ℝ → ℝ) : newtonCoefficient p 0 = p 0 := by
  simp [newtonCoefficient]

end QAlgorithms.Papers.Independent.Information100.P49


