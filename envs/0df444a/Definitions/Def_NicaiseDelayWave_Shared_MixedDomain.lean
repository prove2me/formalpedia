-- Prove2me | Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
-- name    : NicaiseDelayWave_Shared_MixedDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T17:17:00.047309+00:00
-- url     : https://prove2.me/theorems/29b27d76-aa27-483c-945a-5a736f193349
-- title:
--   Bounded C² domain with boundary split Γ = Γ_D ∪ Γ_N, outer normal and surface measure
-- statement:
--   Let $n \ge 1$. A **mixed domain** in $\mathbb R^n$ consists of
--
--   1. a bounded open set $\Omega \subset \mathbb R^n$ whose boundary $\Gamma = \partial\Omega$ is of class $C^2$, described by a global $C^2$ defining function $\psi : \mathbb R^n \to \mathbb R$ with
--   $$\Omega = \{x : \psi(x) < 0\}, \qquad \partial\Omega = \{x : \psi(x) = 0\}, \qquad \nabla\psi(x) \neq 0 \ \text{ for } x \in \partial\Omega;$$
--   2. a splitting $\Gamma = \Gamma_D \cup \Gamma_N$ of the boundary into a Dirichlet part and a Neumann (feedback) part with $\overline{\Gamma_D} \cap \overline{\Gamma_N} = \emptyset$ and $\Gamma_D \neq \emptyset$;
--   3. the surface measure $d\Gamma$ on $\partial\Omega$: a finite Borel measure $\sigma$ carried by $\partial\Omega$ for which the Gauss–Green formula
--   $$\int_\Omega \operatorname{div} F(x)\,dx = \int_{\partial\Omega} F(x)\cdot\nu(x)\,d\Gamma(x)$$
--   holds for every $C^1$ vector field $F : \mathbb R^n \to \mathbb R^n$, where $\nu = \nabla\psi/|\nabla\psi|$ is the outer unit normal.
--
--   The outer unit normal $\nu(x) = \nabla\psi(x)/|\nabla\psi(x)|$ is defined alongside, and the divergence is $\operatorname{div} F = \sum_{i} \partial_i F_i$.
--
--   This is the standing geometric setting of Nicaise and Pignotti (2006): every statement of the mission is posed on such a domain.
--
--   **Formalization Note** Every bounded $C^2$ domain admits a global $C^2$ defining function, so describing the boundary through $\psi$ is not a restriction. The Gauss–Green identity over all $C^1$ fields determines $\sigma$ uniquely as the $(n-1)$-dimensional surface measure on $\partial\Omega$; it is therefore part of the setting, not an extra assumption, and it fixes the normalisation of $d\Gamma$ on which the energy (1.9) and condition (1.10) depend. The sets $\Gamma_D$, $\Gamma_N$ are automatically closed and disjoint.
--
--   It serves all four missions of the series, each posed on this standing setting of p. 1561 (PDF p. 1): `01-boundary-stability` (Theorem 1.1, boundary delay: §1, pp. 1561–1563, PDF 1–3; §3, pp. 1569–1574, PDF 9–14), `02-internal-stability` (Theorem 1.3, internal delay: §1, pp. 1561–1563, PDF 1–3; §4, pp. 1574–1579, PDF 14–19), `03-boundary-instability` (Theorem 1.2: §1, pp. 1561–1563, PDF 1–3; (3.7), p. 1571, PDF 11; §5.1, pp. 1579–1582, PDF 19–22) and `04-internal-instability` (Theorem 1.4: §1, p. 1563, PDF 3; §5.2, pp. 1583–1585, PDF 23–25). It is reviewed once for all four.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1561, §1 (standing assumptions on Ω, Γ_D, Γ_N; outer normal ν)

import Mathlib

open MeasureTheory

namespace NicaiseDelayWave.Shared

/-- The divergence `div F = ∑ᵢ ∂ᵢ Fᵢ` of a vector field `F : ℝⁿ → ℝⁿ`. -/
noncomputable def divergence {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) i

/-- A bounded open set `Ω ⊂ ℝⁿ` with boundary of class `C²`, given by a global `C²` defining
function `ψ` (`Ω = {ψ < 0}`, `∂Ω = {ψ = 0}`, `∇ψ ≠ 0` on `∂Ω`), whose boundary is split as
`∂Ω = Γ_D ∪ Γ_N` with `closure Γ_D ∩ closure Γ_N = ∅` and `Γ_D ≠ ∅`, together with the surface
measure `σ` on `∂Ω`, pinned down by the Gauss–Green formula with the outer unit normal
`ν = ∇ψ / ‖∇ψ‖`. -/
structure MixedDomain (n : ℕ) where
  /-- The domain `Ω`. -/
  Ω : Set (EuclideanSpace ℝ (Fin n))
  /-- The Dirichlet part `Γ_D` of the boundary. -/
  ΓD : Set (EuclideanSpace ℝ (Fin n))
  /-- The Neumann (feedback) part `Γ_N` of the boundary. -/
  ΓN : Set (EuclideanSpace ℝ (Fin n))
  /-- A global `C²` defining function of `Ω`. -/
  ψ : EuclideanSpace ℝ (Fin n) → ℝ
  /-- The surface measure `dΓ` on `∂Ω`. -/
  σ : Measure (EuclideanSpace ℝ (Fin n))
  isOpen_Ω : IsOpen Ω
  isBounded_Ω : Bornology.IsBounded Ω
  contDiff_ψ : ContDiff ℝ 2 ψ
  Ω_eq : Ω = {x | ψ x < 0}
  frontier_eq : frontier Ω = {x | ψ x = 0}
  gradient_ne_zero : ∀ x ∈ frontier Ω, gradient ψ x ≠ 0
  union_eq : ΓD ∪ ΓN = frontier Ω
  disjoint_closure : Disjoint (closure ΓD) (closure ΓN)
  ΓD_nonempty : ΓD.Nonempty
  isFiniteMeasure_σ : IsFiniteMeasure σ
  σ_compl_frontier : σ (frontier Ω)ᶜ = 0
  /-- Gauss–Green formula: `∫_Ω div F dx = ∫_{∂Ω} F · ν dΓ` for every `C¹` vector field `F`. -/
  gaussGreen : ∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), ContDiff ℝ 1 F →
    ∫ x in Ω, divergence F x =
      ∫ x, inner ℝ (F x) (‖gradient ψ x‖⁻¹ • gradient ψ x) ∂σ

/-- The outer unit normal `ν(x) = ∇ψ(x) / ‖∇ψ(x)‖` (meaningful on `∂Ω`). -/
noncomputable def MixedDomain.ν {n : ℕ} (D : MixedDomain n) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ‖gradient D.ψ x‖⁻¹ • gradient D.ψ x

end NicaiseDelayWave.Shared


