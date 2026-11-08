-- Prove2me | Definitions.Def_ProperHalfspace_InfluencePCA
-- name    : ProperHalfspace_InfluencePCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:50.473125+00:00
-- url     : https://prove2.me/theorems/6f78f169-b73b-4ed1-b6f2-90314f0e7922
-- title:
--   The Boolean influence PCA matrix $M_\rho(f)$
-- statement:
--   Let $z\in\{\pm1,*\}^n$ have independent coordinates, $z_i=*$ with probability $1-\rho$ and $z_i=\pm1$ with probability $\rho/2$ each, and let $S(z)=\{i:z_i=*\}$. For $i\in S(z)$ the degree-1 coefficient of the restricted function is
--   $$\hat f_z(i)=\sum_{T\subseteq[n],\ T\cap S(z)=\{i\}}\hat f(T)\prod_{j\in T\setminus\{i\}}z_j.$$
--   The vector $X_{\rho,f}\in\mathbb R^n$ has $i$-th entry $\hat f_z(i)$ for $i\in S(z)$ and $0$ otherwise, and the influence PCA matrix is
--   $$M_\rho(f)=\mathbf E\bigl[X_{\rho,f}X_{\rho,f}^\top\bigr].$$
--   It is the second-moment matrix of the degree-1 Fourier vector of a random restriction.
--
--   **Formalization Note** A restriction is `Fin n → Option ℤˣ`, and the expectation is the finite sum over restrictions with weight $(1-\rho)^{\#\text{free}}(\rho/2)^{\#\text{fixed}}$. The matrix is defined by the expectation, not by the entry formulas of Proposition 12.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Definition 11, p.18

import Mathlib
import Definitions.Def_ProperHalfspace_Fourier

namespace ProperHalfspace

/-!
# The Boolean influence PCA matrix

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), Definition 11, p.18.

**Formalization Note.** A restriction `z ∈ {±1, ∗}ⁿ` is `Fin n → Option ℤˣ`, with `none` for `∗`. The expectation (1) is the
finite sum over restrictions with weight `(1−ρ)^{#free} (ρ/2)^{#fixed}`. The matrix is defined by (1), not by the entry
formulas (2)–(3), which are Proposition 12.
-/

/-- A restriction `z ∈ {±1, ∗}ⁿ`. -/
abbrev Restriction (n : ℕ) := Fin n → Option ℤˣ

/-- The probability of `z` under `μ_{ρ,∗}^{⊗n}`: `zᵢ = ∗` with probability `1 − ρ`, `±1` with probability `ρ/2` each. -/
noncomputable def restrictionWeight {n : ℕ} (ρ : ℝ) (z : Restriction n) : ℝ :=
  ∏ i, match z i with
    | none => 1 - ρ
    | some _ => ρ / 2

/-- The free coordinates `S(z) = {i : zᵢ = ∗}`. -/
def freeSet {n : ℕ} (z : Restriction n) : Finset (Fin n) := Finset.univ.filter fun i => z i = none

/-- The value `zⱼ` of a fixed coordinate, as a real number (`0` on a free coordinate, which `restrictedCoeff` never reads). -/
def fixedVal : Option ℤˣ → ℝ
  | some u => ((u : ℤ) : ℝ)
  | none => 0

/-- The degree-1 coefficient of the restricted function,
`f̂_z(i) = Σ_{T : T ∩ S(z) = {i}} f̂(T) Π_{j ∈ T∖{i}} zⱼ`. -/
noncomputable def restrictedCoeff {n : ℕ} (f : Cube n → ℝ) (z : Restriction n) (i : Fin n) : ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T ∩ freeSet z = {i}),
    fourier f T * ∏ j ∈ T.erase i, fixedVal (z j)

/-- The vector `X_{ρ,f}`: its `i`-th entry is `f̂_z(i)` if `i ∈ S(z)`, and `0` otherwise. -/
noncomputable def pcaVector {n : ℕ} (f : Cube n → ℝ) (z : Restriction n) (i : Fin n) : ℝ :=
  if i ∈ freeSet z then restrictedCoeff f z i else 0

/-- The influence PCA matrix `M_ρ(f) = E[X_{ρ,f} X_{ρ,f}^⊤]`, (1), p.18. -/
noncomputable def pcaMatrix {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ z : Restriction n, restrictionWeight ρ z * (pcaVector f z i * pcaVector f z j)

end ProperHalfspace


