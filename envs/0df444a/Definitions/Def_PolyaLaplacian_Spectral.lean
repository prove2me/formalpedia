-- Prove2me | Definitions.Def_PolyaLaplacian_Spectral
-- name    : PolyaLaplacian_Spectral
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-17T02:16:43.82886+00:00
-- url     : https://prove2.me/theorems/71f7b42e-a08f-423c-927c-b16d9f612639
-- title:
--   Dirichlet eigenvalues, Rayleigh quotient and area
-- statement:
--   This file builds the Dirichlet spectral infrastructure for the positive Laplacian on a bounded domain $\Omega\subset\mathbb R^n$, used throughout the mission.
--
--   It defines the open disk $\{x:\|x\|<R\}$ and annulus $\{x:r<\|x\|<1\}$, the **area** $|\Omega|$ as the Lebesgue measure of $\Omega$ (returned as a real number), and the space of smooth compactly-supported **test functions** supported in the interior of $\Omega$. For a test function $u$ it defines the **Dirichlet energy** $\int|\nabla u|^2$, the **$L^2$ mass** $\int u^2$, and the **Rayleigh quotient**
--   $$\mathcal R[u]=\frac{\int_\Omega|\nabla u|^2}{\int_\Omega u^2}.$$
--   The **$k$-th Dirichlet eigenvalue** is then given by the Courant min–max principle
--   $$\lambda_k(\Omega)=\inf_{\substack{V\subset C_c^\infty(\Omega)\\ \dim V=k}}\ \sup_{0\ne u\in V}\ \mathcal R[u].$$
--   For a bounded open set this recovers the $k$-th eigenvalue of the Dirichlet Laplacian counted with multiplicity, and it is the variational characterization used in all the mission's eigenvalue bounds.
--
--   **Formalization Note.** The gradient squared is written as the sum of squares of the partial derivatives in the standard orthonormal basis. The eigenvalue is an infimum over $k$-dimensional submodules of test functions of a supremum of Rayleigh quotients; the test-function space is taken over the interior of the input set, which equals the set when it is open.
-- source:
--   https://epoch.ai/frontiermath/open-problems/polya-laplacian-spectrum ; Courant min–max characterization of the Dirichlet Laplacian spectrum.

import Mathlib

noncomputable section

namespace PolyaLaplacian

open MeasureTheory Set TopologicalSpace

variable {n : ℕ}

/-- The open ball of radius `R` centered at the origin in `ℝ^n`. -/
def disk (R : ℝ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ‖x‖ < R}

/-- The annulus `{x | r < ‖x‖ < 1}` in `ℝ^n`. -/
def annulus (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) := {x | r < ‖x‖ ∧ ‖x‖ < 1}

/-- Lebesgue measure of a set, as a real number. For a bounded measurable set this is its usual
measure; `ENNReal.toReal` sends `⊤` to `0`. -/
def area (s : Set (EuclideanSpace ℝ (Fin n))) : ℝ := (volume s).toReal

/-- The space of smooth compactly-supported test functions whose support lies in the interior of
`Ω`. For open `Ω` this is `C_c^∞(Ω)`. -/
abbrev TestFn (Ω : Set (EuclideanSpace ℝ (Fin n))) : Type _ :=
  TestFunction (⟨interior Ω, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤

/-- The Dirichlet energy `∫ |∇u|²` of a test function, with `|∇u|²` written as the sum of the
squares of the partial derivatives in the standard orthonormal basis. -/
def dirichletEnergy (Ω : Set (EuclideanSpace ℝ (Fin n))) (u : TestFn Ω) : ℝ :=
  ∫ x in interior Ω,
    ∑ i : Fin n, (fderiv ℝ (u : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.single i 1)) ^ 2

/-- The `L²` mass `∫ u²` of a test function. -/
def l2Mass (Ω : Set (EuclideanSpace ℝ (Fin n))) (u : TestFn Ω) : ℝ :=
  ∫ x in interior Ω, ((u : EuclideanSpace ℝ (Fin n) → ℝ) x) ^ 2

/-- The Rayleigh quotient `∫ |∇u|² / ∫ u²`. -/
def rayleighQuotient (Ω : Set (EuclideanSpace ℝ (Fin n))) (u : TestFn Ω) : ℝ :=
  dirichletEnergy Ω u / l2Mass Ω u

/-- The `k`-th Dirichlet eigenvalue of the positive Laplacian on `Ω`, defined by the Courant
min–max principle over `k`-dimensional subspaces of test functions. For a bounded open set this is
the `k`-th eigenvalue counted with multiplicity. -/
def dirichletEigenvalue (Ω : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : ℝ :=
  ⨅ (V : Submodule ℝ (TestFn Ω)) (_ : Module.finrank ℝ V = k),
    ⨆ (u : V) (_ : (u : TestFn Ω) ≠ 0), rayleighQuotient Ω (u : TestFn Ω)

end PolyaLaplacian


