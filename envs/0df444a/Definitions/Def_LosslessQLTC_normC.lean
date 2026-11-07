-- Prove2me | Definitions.Def_LosslessQLTC_normC
-- name    : LosslessQLTC_normC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:15:40.687115+00:00
-- url     : https://prove2.me/theorems/6c14280f-e64a-47df-870d-715247ed5116
-- title:
--   The weighted norm $\|f\|_X$, its reversed form, and the distance to a code
-- statement:
--   Write $D_I=\prod_{i\in I}D_i$ and $D'_I=\prod_{i\in I}D'_i$, with empty products equal to $1$. A vertex $v\in V_I$ has weight $\|v\|_X=D_I^{-1}$, and an $\mathbb F_2$-valued cochain has norm
--
--   $$\|f\|_X=\sum_{v\in\operatorname{supp}f}\|v\|_X,$$
--
--   which is (2.1). The reversed norm of $f\in C_s(X)$ gives $v\in V_I$ the weight $1/D'_{[k]\setminus I}$. For a linear code $C$, $\operatorname{dist}(f,C)=\min_{c\in C}\|f+c\|$. These norms measure words and syndromes throughout the mission.
--
--   **Formalization Note.** Weights are real numbers. The minimum runs over the finite set of elements of $C$, which contains $0$, so it is a true minimum.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Norms, p.17, eq. (2.1); p.18; Definition 5.1, p.40

import Mathlib
import Definitions.Def_LosslessQLTC_Level

namespace LosslessQLTC

variable {k : ℕ}

/-- `D_I = ∏_{i ∈ I} D_i`, with `D_∅ = 1` (arXiv:2610.00525, held version, sha256 d61f0ed9…,
p.17). The same product gives `D′_I` when applied to `D′`. -/
def prodD (D : Fin k → ℕ) (I : Finset (Fin k)) : ℕ := ∏ i ∈ I, D i

/-- The weight `∥v∥_X = D_I⁻¹` of `v ∈ V_I` (p.17). -/
noncomputable def weight (X : SquareComplex k) (v : X.Vtx) : ℝ :=
  1 / (prodD X.D (X.type v) : ℝ)

/-- The reversed weight `1 / D′_{[k] ∖ I}` of `v ∈ V_I` (p.18). -/
noncomputable def weightRev (X : SquareComplex k) (v : X.Vtx) : ℝ :=
  1 / (prodD X.D' (Finset.univ \ X.type v) : ℝ)

/-- The norm (2.1) of an `F₂`-valued cochain: the total weight of its support (p.17). -/
noncomputable def normC (X : SquareComplex k) {s : ℕ} (f : Level X s → ZMod 2) : ℝ :=
  ∑ v : Level X s, if f v ≠ 0 then weight X v.1 else 0

/-- The reversed norm `∥f∥_{X^rev}` of `f ∈ C_s(X)` (p.18). -/
noncomputable def normRev (X : SquareComplex k) {s : ℕ} (f : Level X s → ZMod 2) : ℝ :=
  ∑ v : Level X s, if f v ≠ 0 then weightRev X v.1 else 0

/-- `∥A∥ = Σ_{v ∈ A} ∥v∥` for a vertex set `A` (p.17: "We identify a set with its indicator"). -/
noncomputable def setNorm (X : SquareComplex k) (A : Finset X.Vtx) : ℝ :=
  ∑ v ∈ A, weight X v

/-- `∥V_s∥`, the norm of the whole level `s` (p.27, p.43). -/
noncomputable def levelMass (X : SquareComplex k) (s : ℕ) : ℝ :=
  ∑ v : Level X s, weight X v.1

/-- `∥V_s∥_{X^rev}`, the reversed norm of the whole level `s` of `X`. -/
noncomputable def levelMassRev (X : SquareComplex k) (s : ℕ) : ℝ :=
  ∑ v : Level X s, weightRev X v.1

/-- `dist(f, C) = min_{c ∈ C} ∥f + c∥` for a linear code `C` and a norm `nrm` (p.17, p.40). The
minimum is over the finite set of elements of `C`, which contains `0`. -/
noncomputable def distTo {ι : Type} [Fintype ι] [DecidableEq ι] (nrm : (ι → ZMod 2) → ℝ)
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (f : ι → ZMod 2) : ℝ := by
  classical
  exact (Finset.univ.filter (· ∈ C)).inf' ⟨0, by simp⟩ fun c => nrm (f + c)

end LosslessQLTC


