-- Prove2me | Definitions.Def_SuperRamanujan227_Main_Spectra
-- name    : SuperRamanujan227_Main_Spectra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:29:01.381495+00:00
-- url     : https://prove2.me/theorems/c6f63b64-bffe-48b9-bc0d-47d5b4ac9d54
-- title:
--   Real-rootedness, $k$-th largest roots $\alpha_k$, eigenvalues $\lambda_k$ and permutation-averaged characteristic polynomials
-- statement:
--   A real polynomial $p$ is **real-rooted** if it is nonzero and all of its roots are real, i.e. it has exactly $\deg p$ real roots counted with multiplicity.
--
--   For a real polynomial $p$ and an integer $k\ge 1$, $\alpha_k(p)$ denotes the $k$-th largest real root of $p$, counted with multiplicity, so that $\alpha_1(p)\ge\alpha_2(p)\ge\cdots$. For a real square matrix $A$ whose eigenvalues are all real, $\lambda_k(A)$ is its $k$-th largest eigenvalue counted with algebraic multiplicity, that is,
--   $$\lambda_k(A)=\alpha_k\big(\chi_x(A)\big),\qquad \chi_x(A)=\det(xI-A).$$
--
--   For a function $F$ from $m\times m$ permutation matrices to polynomials, $\mathbb E_P[F(P)]$ is the expected polynomial for $P$ uniformly random, taken in coefficient space: the average of $F(P)$ over the $m!$ permutation matrices. The two instances used in the mission are
--   $$\mathbb E_P\big[\chi_x(A+PBP^{\mathsf T})\big]\quad\text{and}\quad\mathbb E_P\big[\chi_x(APBP^{\mathsf T})\big].$$
--
--   These are the spectral notations of §2.1 shared by every statement of the mission.
--
--   **Formalization Note** $\alpha_k$ sorts the multiset of real roots in decreasing order and reads position $k-1$; it returns the junk value $0$ for $k=0$ or when $p$ has fewer than $k$ real roots. Every statement uses it only where at least $k$ real roots exist (real-rooted polynomials of degree $\ge k$), or asserts real-rootedness as part of its conclusion.
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, §2.1, p. 7 (definitions of $\chi_x$, $\lambda_k$, $\alpha_k$ and the expected polynomial in coefficient space)

import Mathlib

open Polynomial

namespace SuperRamanujan227.Main

/-- Real-rootedness (§2.1, p. 7): `p` is a nonzero real polynomial all of whose complex roots
are real, i.e. its multiset of real roots, counted with multiplicity, has `natDegree p`
elements. -/
def RealRooted (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ Multiset.card p.roots = p.natDegree

/-- `α_k(p)` (§2.1, p. 7): the `k`-th largest real root of `p`, counted with multiplicity, with
the paper's 1-based index (`kthLargestRoot p 1` is the largest root). Junk value `0` when
`k = 0` or when `p` has fewer than `k` real roots; every statement uses it only on polynomials
having at least `k` real roots. -/
noncomputable def kthLargestRoot (p : ℝ[X]) (k : ℕ) : ℝ :=
  if 1 ≤ k then (p.roots.sort (· ≥ ·)).getD (k - 1) 0 else 0

/-- `λ_k(A)` (§2.1, p. 7): the `k`-th largest eigenvalue, counted with algebraic multiplicity, of a
real square matrix whose eigenvalues are all real, i.e. the `k`-th largest real root of its
characteristic polynomial `χ_x(A) = det(xI - A)`. -/
noncomputable def matrixEig {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (k : ℕ) : ℝ :=
  kthLargestRoot A.charpoly k

/-- The real `m × m` permutation matrix of `σ`. -/
noncomputable def permMat {m : ℕ} (σ : Equiv.Perm (Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  σ.permMatrix ℝ

/-- `E_P[F(P)]` for `P` a uniformly random `m × m` permutation matrix, taken in coefficient
space (§2.1, p. 7): the average of the polynomials `F σ` over all `m!` permutations. -/
noncomputable def permAvg {m : ℕ} (F : Equiv.Perm (Fin m) → ℝ[X]) : ℝ[X] :=
  ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin m), F σ

/-- `E_P[χ_x(A + P B Pᵀ)]` over a uniformly random permutation matrix `P`. -/
noncomputable def expCharpolyAdd {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) : ℝ[X] :=
  permAvg fun σ => (A + permMat σ * B * (permMat σ).transpose).charpoly

/-- `E_P[χ_x(A P B Pᵀ)]` over a uniformly random permutation matrix `P`. -/
noncomputable def expCharpolyMul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) : ℝ[X] :=
  permAvg fun σ => (A * permMat σ * B * (permMat σ).transpose).charpoly

end SuperRamanujan227.Main


