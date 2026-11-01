-- Prove2me | Definitions.Def_AccessibleMaps_AffineAssignment
-- name    : AccessibleMaps_AffineAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:55.174767+00:00
-- url     : https://prove2.me/theorems/080b3fd2-378b-4527-b829-b3b8fbb12614
-- title:
--   Affine assignment map $E_{\mathcal V}(\rho)=g+G\rho$ (Eqs. (5), (21))
-- statement:
--   An **affine assignment** on the system $\mathbb C^{a}$ with environment $\mathcal H$ consists of
--
--   1. an admissible domain $\mathcal V\subseteq\mathcal M_A$,
--   2. a bounded operator $g$ on $\mathbb C^{a}\otimes\mathcal H$, and
--   3. a real-linear map $G$ from $a\times a$ complex matrices to bounded operators on $\mathbb C^{a}\otimes\mathcal H$,
--
--   such that for every $\rho\in\mathcal V$ the operator $E_{\mathcal V}(\rho)=g+G\rho$ is a density operator (positive, trace class, trace one) and extends $\rho$:
--   $$
--   \operatorname{tr}_B\big(g+G\rho\big)=\rho .
--   $$
--   This is the paper's most general affine assignment, Eq. (21): in the Fano form (3) of $\tau_{AB}$, the environment coefficients $\beta_j=b_j+\sum_k B_{jk}\alpha_k$ and the correlation coefficients $\gamma_{ij}=g_{ij}+\sum_k G_{ijk}\alpha_k$ are affine in the Bloch vector $\alpha$ of $\rho$, which is the same as $\tau_{AB}$ being affine in $\rho$. The positivity requirement is the paper's "positivity constraints".
--
--   **Formalization Note** Fano coefficients are not used, since they have no finite form for an infinite-dimensional environment. $\mathcal H$ is any complex Hilbert space. Only the values of $G$ on Hermitian matrices matter; $G$ is defined on all matrices for convenience. $g$ and $G\rho$ need not be trace class separately.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (5), p.1 and Eq. (21), p.4

import Mathlib
import Definitions.Def_HayashiHoeffding_IsDensityOp
import Definitions.Def_AccessibleMaps_trB
import Definitions.Def_AccessibleMaps_IsFiniteVolumeDomain

open HayashiHoeffding

namespace AccessibleMaps

/-- An affine assignment map `E_𝒱 : ρ ↦ τ_AB = g + G ρ`: a domain `𝒱`, a constant operator `g` and a
real-linear map `G` from matrices to operators on the composite space, such that for every `ρ ∈ 𝒱`
the operator `g + G ρ` is a density operator with `tr_B (g + G ρ) = ρ`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (5), p.1 (PDF p.1) and Eq. (21), p.4 (PDF p.4):
"β_j^lin = b_j + ∑_k B_jk α_k, γ_ij^lin = g_ij + ∑_k G_ijk α_k, which is actually the most general
form of an affine assignment map, where the constants are subject to the positivity constraints".

**Formalization Note.** This is coordinate-free Eq. (21): the coefficients `β`, `γ` of the Fano form
(3) are affine in `α` exactly when `E` is affine in `ρ`. Fano coefficients are not used, because
they have no finite form for infinite-dimensional `H`. Only the values of `G` on Hermitian matrices
are constrained; `G` is taken on all matrices for convenience. The ancilla `H` is any complex
Hilbert space. `g` and `G ρ` need not be trace class separately. The system is finite-dimensional
as on p.1 (PDF p.1), and `IsFiniteVolumeDomain` forces `a` to be nonempty. -/
structure AffineAssignment (a H : Type*) [Fintype a] [DecidableEq a] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The domain `𝒱`. -/
  V : Set (Matrix a a ℂ)
  /-- The constant term of the assignment. -/
  g : Composite a H →L[ℂ] Composite a H
  /-- The linear term of the assignment. -/
  G : Matrix a a ℂ →ₗ[ℝ] (Composite a H →L[ℂ] Composite a H)
  /-- `𝒱` is an admissible domain. -/
  domain : IsFiniteVolumeDomain V
  /-- The positivity constraints: every assigned operator is a density operator. -/
  isDensityOp : ∀ ρ ∈ V, IsDensityOp (g + G ρ)
  /-- Eq. (5): the assignment extends `ρ`. -/
  trB_eq : ∀ ρ ∈ V, trB (g + G ρ) = ρ

end AccessibleMaps


