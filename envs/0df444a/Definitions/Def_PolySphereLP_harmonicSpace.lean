-- Prove2me | Definitions.Def_PolySphereLP_harmonicSpace
-- name    : PolySphereLP_harmonicSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:23.373674+00:00
-- url     : https://prove2.me/theorems/72f4086e-5256-46ed-872a-5e0ddec2ad29
-- title:
--   The space $\mathcal H_{n,k}$ of real homogeneous harmonic polynomials
-- statement:
--   For integers $n,k\ge0$, $\mathcal H_{n,k}$ is the real vector space of polynomials $p\in\mathbb R[x_1,\dots,x_n]$ that are homogeneous of degree $k$ and harmonic, $\Delta p=0$. These are the spherical harmonics of degree $k$ on $S^{n-1}$; the paper identifies them with their restrictions to the sphere.
--
--   **Formalization Note** Elements are polynomials rather than restrictions; a homogeneous polynomial is determined by its restriction to $S^{n-1}$ when $n\ge1$. The Laplacian is the published `SphereSOS.Rate.laplacian`. Variables and coordinates are indexed by `Fin n` (from $0$).
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), §2.1, p.10

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

namespace PolySphereLP

/-- **The space `ℋ_{n,k}` of real homogeneous harmonic polynomials of degree `k`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), §2.1,
p.10: "let ℋ_{n,j} denote the space of real homogeneous harmonic polynomials of degree j, identified
with their restrictions to the sphere".

`harmonicSpace n k` is the real subspace of `ℝ[x₁,…,xₙ]` of polynomials that are homogeneous of
degree `k` and satisfy `Δp = 0`, with `Δ = SphereSOS.Rate.laplacian`.

**Formalization Note.** Elements are polynomials, not their restrictions: a homogeneous polynomial is
determined by its restriction to `S^{n−1}` (for `n ≥ 1`), so nothing changes. Variables are `Fin n`
(0-based). -/
noncomputable def harmonicSpace (n k : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) where
  carrier := {p | p.IsHomogeneous k ∧ SphereSOS.Rate.laplacian p = 0}
  add_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    refine ⟨hp.add hq, ?_⟩
    simp only [SphereSOS.Rate.laplacian, map_add, Finset.sum_add_distrib] at hp' hq' ⊢
    rw [hp', hq', add_zero]
  zero_mem' := ⟨MvPolynomial.isHomogeneous_zero _ _ _, by simp [SphereSOS.Rate.laplacian]⟩
  smul_mem' := by
    rintro c p ⟨hp, hp'⟩
    refine ⟨(MvPolynomial.mem_homogeneousSubmodule _ _).1
      (Submodule.smul_mem _ c ((MvPolynomial.mem_homogeneousSubmodule _ _).2 hp)), ?_⟩
    simp only [SphereSOS.Rate.laplacian, Derivation.map_smul, ← Finset.smul_sum] at hp' ⊢
    rw [hp', smul_zero]

end PolySphereLP


