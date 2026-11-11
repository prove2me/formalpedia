-- Prove2me | Definitions.Def_SpectralFeedback_rewardSet
-- name    : SpectralFeedback_rewardSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:23.379201+00:00
-- url     : https://prove2.me/theorems/a12d015d-25bc-4641-abeb-9f84d36f9541
-- title:
--   Admissible rewards $F$, spectral reward $f_{F,s}$ and the value $\mathcal G^F_{m,s}(R)$
-- statement:
--   Fix an integer $s\ge1$ and write $\mathbb R^s_+=\{x\in\mathbb R^s: x\ge0\}$.
--
--   1. A function $F:\mathbb R^s_+\to\mathbb R_+$ is **admissible** if it is continuous, symmetric ($F(x_{\sigma(1)},\dots,x_{\sigma(s)})=F(x)$ for every permutation $\sigma$), concave, coordinatewise nondecreasing, and $F(0)=0$. Homogeneity is not assumed.
--   2. For a positive semidefinite matrix $A\in\mathbb C^{d\times d}$ the **spectral reward** is
--   $$
--   f_{F,s}(A)=F\bigl(\lambda_1(A),\dots,\lambda_s(A)\bigr),
--   $$
--   with eigenvalues decreasing and padded with zeros.
--   3. For $R\succeq0$ and $m\ge1$ the **achievable rewards** of $m$-atom decompositions form the set
--   $$
--   \Bigl\{\sum_{h=1}^m f_{F,s}(A_h)\;:\;A_h\succeq0\ (1\le h\le m),\ \sum_h A_h=R\Bigr\},
--   $$
--   and the paper's value $\mathcal G^F_{m,s}(R)$ is its maximum. The atoms have no rank constraint, empty symbols are zero atoms, and $R$ need not have trace one.
--
--   The value $\mathcal G^F_{2,s}$ is the object of the mission's goal, Theorem H.2.
--
--   **Formalization Note** $F$ is a function on all of $\mathbb R^s$ (`Fin s → ℝ`) and every property is required on the orthant only (`ContinuousOn`, `ConcaveOn`, `MonotoneOn` for the pointwise order, symmetry for $x\in\mathbb R^s_+$). Nonnegativity of $F$ is not a separate clause: it follows from monotonicity and $F(0)=0$. "$\mathcal G^F_{m,s}(R)=v$" is written `IsGreatest (rewardSet s F m R) v` (the maximum exists and equals $v$), never as a supremum, which would return a junk $0$ on an empty or unbounded set.
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), §H.1.1, p.108 (PDF p.110)

import Mathlib
import Definitions.Def_SpectralFeedback_eigDesc

open scoped ComplexOrder

namespace SpectralFeedback

/-- The nonnegative orthant `ℝ^s_+ = {x ∈ ℝ^s | x ≥ 0}` (Qi, manuscript (Nov. 2026), §H.1.1, p.108
(PDF p.110)), the domain of the reward function `F`. -/
def orthant (s : ℕ) : Set (Fin s → ℝ) := Set.Ici 0

/-- **The admissible reward class** (Qi, *Spectral Structure and Exact Arithmetic of Finite-Feedback
Measurement Discrimination*, manuscript (Nov. 2026), §H.1.1, p.108 (PDF p.110)): "Let
`F : ℝ^s_+ → ℝ_+` be continuous, symmetric, concave, and coordinatewise nondecreasing, with
`F(0) = 0`. Homogeneity is not assumed."

**Formalization Note** `F` is a function on all of `ℝ^s` (`Fin s → ℝ`), and every hypothesis is
imposed on the orthant `ℝ^s_+` only (`ContinuousOn`, `ConcaveOn`, `MonotoneOn`, symmetry for
`x ∈ ℝ^s_+`); values off the orthant are irrelevant. "Coordinatewise nondecreasing" is
`MonotoneOn` for the pointwise order, which is equivalent on the orthant. The codomain `ℝ_+` is not
a separate clause: `F x ≥ F 0 = 0` for `x ≥ 0` follows from monotonicity and `F(0) = 0`. -/
def Admissible (s : ℕ) (F : (Fin s → ℝ) → ℝ) : Prop :=
  ContinuousOn F (orthant s) ∧
  (∀ σ : Equiv.Perm (Fin s), ∀ x ∈ orthant s, F (x ∘ σ) = F x) ∧
  ConcaveOn ℝ (orthant s) F ∧
  MonotoneOn F (orthant s) ∧
  F 0 = 0

/-- The spectral reward `f_{F,s}(A) = F(λ₁(A), …, λ_s(A))` of a positive matrix `A` (Qi,
manuscript (Nov. 2026), §H.1.1, p.108 (PDF p.110)), with the eigenvalues decreasing and padded with
zeros (`eigDesc`, 0-based). -/
noncomputable def reward {d : ℕ} (s : ℕ) (F : (Fin s → ℝ) → ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ℝ :=
  F (fun i : Fin s => eigDesc A (i : ℕ))

/-- **The achievable rewards of an `m`-atom decomposition** (Qi, *Spectral Structure and Exact
Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), §H.1.1, p.108
(PDF p.110)):
`{ ∑_{h=1}^m f_{F,s}(A_h) | A_h ⪰ 0 (1 ≤ h ≤ m), ∑_h A_h = R }`.

The paper's value `G^F_{m,s}(R)` is the maximum of this set; "`G^F_{m,s}(R) = v`" is stated as
`IsGreatest (rewardSet s F m R) v` (the maximum exists and equals `v`).

**Formalization Note** The atoms are complex `d × d` positive semidefinite matrices
(`Matrix.PosSemidef`) with no rank constraint; empty symbols are zero atoms, as in the paper. The
maximum is never written as `sSup`, which would return a junk `0` on an empty or unbounded set. -/
def rewardSet {d : ℕ} (s : ℕ) (F : (Fin s → ℝ) → ℝ) (m : ℕ) (R : Matrix (Fin d) (Fin d) ℂ) :
    Set ℝ :=
  {v | ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
    (∀ h, (A h).PosSemidef) ∧ ∑ h, A h = R ∧ v = ∑ h, reward s F (A h)}

end SpectralFeedback


