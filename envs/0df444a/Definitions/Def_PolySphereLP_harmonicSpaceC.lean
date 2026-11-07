-- Prove2me | Definitions.Def_PolySphereLP_harmonicSpaceC
-- name    : PolySphereLP_harmonicSpaceC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:13.16362+00:00
-- url     : https://prove2.me/theorems/4d3f1253-8ba3-41cd-a20c-112cdb011748
-- title:
--   The complexified harmonic space $\mathcal H^{\mathbb C}_{n,k}$
-- statement:
--   $\mathcal H^{\mathbb C}_{n,k}=\mathcal H_{n,k}\otimes_{\mathbb R}\mathbb C$ is the complex vector space of polynomials $p\in\mathbb C[x_1,\dots,x_n]$ that are homogeneous of degree $k$ with $\Delta p=0$.
--
--   **Formalization Note** The tensor product is identified with the complex homogeneous harmonic polynomials: the Laplacian has real coefficients, so a complex polynomial is harmonic exactly when its real and imaginary coefficient parts are, and $p\otimes c\mapsto cp$ is an isomorphism onto this space.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Theorem 2.2, p.12; Lemma 2.1, p.12

import Mathlib
import Definitions.Def_PolySphereLP_lapC

namespace PolySphereLP

/-- **The complexified harmonic space `ℋ^ℂ_{n,k} = ℋ_{n,k} ⊗_ℝ ℂ`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Theorem 2.2, p.12, and
Lemma 2.1, p.12 ("a real or complex homogeneous harmonic polynomial of degree k").

`harmonicSpaceC n k` is the complex subspace of `ℂ[x₁,…,xₙ]` of polynomials homogeneous of degree
`k` with `lapC p = 0`.

**Formalization Note.** `ℋ_{n,k} ⊗_ℝ ℂ` is identified with the complex homogeneous harmonic
polynomials: the Laplacian has real coefficients, so a complex polynomial is harmonic iff its real
and imaginary coefficient parts are, and `p ⊗ c ↦ c·p` is an isomorphism onto this space. -/
noncomputable def harmonicSpaceC (n k : ℕ) : Submodule ℂ (MvPolynomial (Fin n) ℂ) where
  carrier := {p | p.IsHomogeneous k ∧ lapC p = 0}
  add_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    refine ⟨hp.add hq, ?_⟩
    simp only [lapC, map_add, Finset.sum_add_distrib] at hp' hq' ⊢
    rw [hp', hq', add_zero]
  zero_mem' := ⟨MvPolynomial.isHomogeneous_zero _ _ _, by simp [lapC]⟩
  smul_mem' := by
    rintro c p ⟨hp, hp'⟩
    refine ⟨(MvPolynomial.mem_homogeneousSubmodule _ _).1
      (Submodule.smul_mem _ c ((MvPolynomial.mem_homogeneousSubmodule _ _).2 hp)), ?_⟩
    simp only [lapC, Derivation.map_smul, ← Finset.smul_sum] at hp' ⊢
    rw [hp', smul_zero]

end PolySphereLP


