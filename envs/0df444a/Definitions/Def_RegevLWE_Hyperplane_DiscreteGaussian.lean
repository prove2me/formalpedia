-- Prove2me | Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
-- name    : RegevLWE_Hyperplane_DiscreteGaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:55.242196+00:00
-- url     : https://prove2.me/theorems/81e24627-3686-4a82-a20b-e959acd4b774
-- title:
--   Eqs. (4), (6) and Definition 2.10 — Gaussian ρ_s, dual lattice L*, Gaussian lattice sums, smoothing parameter η_ε(L), discrete Gaussian D_{L,r}
-- statement:
--   Work in $\mathbb{R}^n$ with its Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. Let $L \subset \mathbb{R}^n$ be a lattice, i.e. the set of integer combinations of $n$ linearly independent vectors.
--
--   1. **Gaussian function** (Eq. (4)). For $s > 0$ and $x \in \mathbb{R}^n$,
--   $$\rho_s(x) := \exp\bigl(-\pi\|x/s\|^2\bigr) = \exp\Bigl(-\frac{\pi\|x\|^2}{s^2}\Bigr).$$
--   2. **Dual lattice** (p. 34:17). $L^* := \{y \in \mathbb{R}^n : \langle x, y\rangle \in \mathbb{Z} \text{ for all } x \in L\}$.
--   3. **Gaussian masses.** For a countable set $A$, $\rho_s(A) := \sum_{x \in A}\rho_s(x)$. In particular $\rho_s(L)$, $\rho_s(L^*)$ and $\rho_s(L^* \setminus \{0\})$.
--   4. **Smoothing parameter** (Definition 2.10). For $\epsilon > 0$, $\eta_\epsilon(L)$ is the smallest $s$ such that $\rho_{1/s}(L^* \setminus \{0\}) \le \epsilon$; here
--   $$\eta_\epsilon(L) := \inf\{s > 0 : \rho_{1/s}(L^* \setminus \{0\}) \le \epsilon\}.$$
--   5. **Discrete Gaussian** (Eq. (6)). For $r > 0$, $D_{L,r}$ is the probability distribution on $L$ with
--   $$D_{L,r}(x) := \frac{\rho_r(x)}{\rho_r(L)}, \qquad x \in L .$$
--
--   The smoothing parameter is the width above which the discrete Gaussian on $L$ behaves like a continuous Gaussian; the goal of this mission shows that a sample from $D_{L,r}$ at such a width is not concentrated on any proper subspace.
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. A lattice is `L : Submodule ℤ (EuclideanSpace ℝ (Fin n))`; the theorems add `[DiscreteTopology L] [IsZLattice ℝ L]` (discrete and of full rank). $L^*$ is `LinearMap.BilinForm.dualSubmodule (innerₗ _) L`. All sums are real `tsum`s; Gaussian sums over a lattice and its dual are summable, so the value is the true sum. "The smallest $s$" is written as the real infimum of the admissible $s > 0$; for $\epsilon > 0$ this set is nonempty and bounded below, and that the infimum is attained is the separate remark after Definition 2.10 (a milestone). For $\epsilon \le 0$ the set is empty and the infimum is $0$ in Lean, which is why every theorem assumes $\epsilon > 0$. $D_{L,r}$ is a function on the points of $L$; $\rho_s$ is written for all real $s$, and the theorems assume $s > 0$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:15 Eq. (4) and ρ_s(A), p. 34:16 Eq. (6), p. 34:17 (dual lattice), p. 34:19 Definition 2.10

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

namespace RegevLWE.Hyperplane

/-- The Gaussian mass of a lattice, `ρ_s(L) = ∑_{x ∈ L} ρ_s(x)` (p. 34:15). -/
noncomputable def rhoLattice {n : ℕ} (s : ℝ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∑' x : L, RegevLWE.GaussConv.rho s (x : EuclideanSpace ℝ (Fin n))

/-- The Gaussian mass of the RegevLWE.GaussConv.dual lattice, `ρ_s(L*) = ∑_{y ∈ L*} ρ_s(y)`. -/
noncomputable def rhoDual {n : ℕ} (s : ℝ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∑' y : RegevLWE.GaussConv.dual L, RegevLWE.GaussConv.rho s (y : EuclideanSpace ℝ (Fin n))

/-- The discrete Gaussian distribution `D_{L,r}` on the lattice `L` (p. 34:16, Eq. (6)):
the mass of `x ∈ L` is `ρ_r(x) / ρ_r(L)`. -/
noncomputable def discreteGaussian {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (r : ℝ)
    (x : L) : ℝ :=
  RegevLWE.GaussConv.rho r (x : EuclideanSpace ℝ (Fin n)) / rhoLattice r L

end RegevLWE.Hyperplane


