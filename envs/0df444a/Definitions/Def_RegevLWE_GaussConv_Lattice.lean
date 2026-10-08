-- Prove2me | Definitions.Def_RegevLWE_GaussConv_Lattice
-- name    : RegevLWE_GaussConv_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:36.032758+00:00
-- url     : https://prove2.me/theorems/ac4074c8-a90f-4c03-9f4c-dfa488ddcbcc
-- title:
--   Definition 2.10 and Eq. (6) — dual lattice, Gaussian lattice sums, smoothing parameter η_ε(L), discrete Gaussian D_{L+u,r}, and the density of Y
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice (a discrete subgroup spanning $\mathbb{R}^n$, i.e. the integer combinations of $n$ linearly independent vectors), and let $\rho_s$, $\rho_{s,c}$, $\nu_s$ be as in Eqs. (4)–(5).
--
--   1. **Dual lattice** (p. 34:17). $L^* := \{ y \in \mathbb{R}^n : \langle x, y\rangle \in \mathbb{Z} \text{ for all } x \in L\}$.
--   2. **Gaussian mass of a coset.** For $c \in \mathbb{R}^n$, $\rho_s(L + c) := \sum_{x \in L} \rho_s(x + c)$, and $\rho_{s,c}(L) := \sum_{x \in L} \rho_s(x - c)$; thus $\rho_{s,-c}(L) = \rho_s(L + c)$.
--   3. **Mass of the nonzero dual vectors.** $\rho_s(L^* \setminus \{0\}) := \sum_{y \in L^*,\, y \ne 0} \rho_s(y)$.
--   4. **Smoothing parameter** (Definition 2.10). For $\epsilon > 0$, $\eta_\epsilon(L)$ is the smallest $s$ such that $\rho_{1/s}(L^* \setminus \{0\}) \le \epsilon$; here
--   $$\eta_\epsilon(L) := \inf\{ s > 0 : \rho_{1/s}(L^* \setminus \{0\}) \le \epsilon \}.$$
--   5. **Discrete Gaussian on a coset** (Eq. (6)). For $u \in \mathbb{R}^n$ and $r > 0$, $D_{L+u,r}$ is the probability distribution on $L + u$ with
--   $$D_{L+u,r}(y) := \frac{\rho_r(y)}{\rho_r(L + u)}, \qquad y \in L + u,$$
--   and mass $0$ off $L + u$.
--   6. **The distribution $Y$ of Claim 3.9.** Sample $y$ from $D_{L+u,r}$ and add an independent noise vector with density $\nu_s$. The result has density
--   $$Y(x) := \sum_{y \in L + u} D_{L+u,r}(y)\, \nu_s(x - y), \qquad x \in \mathbb{R}^n .$$
--
--   The smoothing parameter is the width above which the discrete Gaussian on $L$ behaves like a continuous Gaussian; $Y$ is the object whose closeness to a continuous Gaussian is the goal of this mission.
--
--   **Formalization Note** A lattice is `L : Submodule ℤ (EuclideanSpace ℝ (Fin n))` with `[DiscreteTopology L] [IsZLattice ℝ L]` (imposed by the theorems, not by these definitions). $L^*$ is `LinearMap.BilinForm.dualSubmodule (innerₗ _) L`. All lattice sums are real `tsum`s; Gaussian sums over a lattice, its cosets and its dual are summable, so the `tsum` is the true sum. "The smallest $s$" is written as the real infimum of the set of admissible $s > 0$; for $\epsilon > 0$ this set is nonempty and bounded below by $0$, so the infimum is the genuine one, and the fact that it is attained is the separate remark after Definition 2.10 (a milestone). $D_{L+u,r}$ is the indicator of the coset $L + u$ times $\rho_r(y)/\rho_r(L+u)$. $Y$ is defined by the density the proof of Claim 3.9 writes down (p. 34:25), as a sum over $v \in L$ with $y = v + u$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:15 (ρ_s(A)), p. 34:16 Eq. (6), p. 34:17 (dual lattice), p. 34:19 Definition 2.10, p. 34:25 (Claim 3.9 and the first line of its proof)

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian

namespace RegevLWE.GaussConv

/-- The dual lattice `L* = {y ∈ ℝⁿ | ∀ x ∈ L, ⟨x, y⟩ ∈ ℤ}` (p. 34:17). -/
noncomputable abbrev dual {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) L

/-- The Gaussian mass of a lattice coset, `ρ_s(L + c) = ∑_{x ∈ L} ρ_s(x + c)` (p. 34:15). -/
noncomputable def rhoCoset {n : ℕ} (s : ℝ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑' x : L, rho s ((x : EuclideanSpace ℝ (Fin n)) + c)

/-- The shifted Gaussian mass of a lattice, `ρ_{s,c}(L) = ∑_{x ∈ L} ρ_s(x - c)` (p. 34:15). -/
noncomputable def rhoShiftLattice {n : ℕ} (s : ℝ) (c : EuclideanSpace ℝ (Fin n))
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∑' x : L, rhoShift s c (x : EuclideanSpace ℝ (Fin n))

/-- The Gaussian mass of the nonzero dual vectors, `ρ_s(L* \ {0}) = ∑_{y ∈ L*, y ≠ 0} ρ_s(y)`. -/
noncomputable def rhoDualNonzero {n : ℕ} (s : ℝ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    ℝ :=
  ∑' y : {y : dual L // y ≠ 0}, rho s ((y : dual L) : EuclideanSpace ℝ (Fin n))

/-- The smoothing parameter (Definition 2.10, p. 34:19): `η_ε(L)` is the least `s > 0` with
`ρ_{1/s}(L* \ {0}) ≤ ε`, written as the infimum of the set of such `s`. -/
noncomputable def smoothingParam {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (ε : ℝ) :
    ℝ :=
  sInf {s : ℝ | 0 < s ∧ rhoDualNonzero (1 / s) L ≤ ε}

/-- The discrete Gaussian distribution `D_{L+u,r}` on the coset `L + u` (p. 34:16, Eq. (6)):
mass `ρ_r(y) / ρ_r(L + u)` at `y ∈ L + u`, and `0` off the coset. -/
noncomputable def discreteGaussian {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) (r : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Set.indicator {z | z - u ∈ L} (fun z => rho r z / rhoCoset r L u) y

/-- The density of the distribution `Y` of Claim 3.9 (p. 34:25): sample `y` from `D_{L+u,r}` and
add an independent noise vector with density `ν_s`, so
`Y(x) = ∑_{y ∈ L+u} D_{L+u,r}(y) ν_s(x - y)`. -/
noncomputable def Ydensity {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) (r s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑' v : L, discreteGaussian L u r ((v : EuclideanSpace ℝ (Fin n)) + u) *
    nu s (x - ((v : EuclideanSpace ℝ (Fin n)) + u))

end RegevLWE.GaussConv


