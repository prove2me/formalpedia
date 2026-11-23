-- Prove2me | Definitions.Def_NoHair_regularStaticVacuumSlice
-- name    : NoHair_regularStaticVacuumSlice
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T07:11:09.014485+00:00
-- url     : https://prove2.me/theorems/f0232008-2cbf-4e93-b8bc-397657cfca8a
-- title:
--   Regular one-ended static vacuum slice with a nondegenerate horizon
-- statement:
--   A global static chart realizes the exterior as $\mathbb R\times\Omega$ with metric $-N^2dt^2+h$ and vanishing spacetime Ricci tensor. The connected open set $\Omega\subset\mathbb R^3$ has compact complement and a nonempty connected boundary. The lapse and spatial metric extend smoothly across the boundary, where $N=0$ and $dN\ne0$, and the extension of $h$ is positive definite. The physical side has $N>0$. For every derivative order $k$, the Cartesian derivatives of $h-\delta$ and $N-1$ are $O(r^{-1-k})$ at infinity. Time translation agrees with the given flow. These are coordinate hypotheses for the one-ended, nondegenerate static vacuum problem.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_conformalVacuumExterior

noncomputable section

open Set
open scoped ContDiff Manifold BigOperators

namespace NoHair

/-- A single asymptotically flat, regular static vacuum slice in a global spatial chart.
The lapse is a defining function for a compact nondegenerate horizon. The
spatial metric extends smoothly and positively through the boundary.
Ricci flatness is imposed in the static spacetime chart. -/
def HasRegularStaticVacuumSlice {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M) : Prop :=
  let X := EuclideanSpace ℝ (Fin 3)
  IsOpen D ∧ ∃ (Ω W : Set X) (N : X → ℝ) (h : X → Matrix (Fin 3) (Fin 3) ℝ) (ψ : E4 → M),
    IsOpen Ω ∧ IsConnected Ω ∧ IsCompact Ωᶜ ∧ (frontier Ω).Nonempty ∧
    IsConnected (frontier Ω) ∧ IsOpen W ∧ closure Ω ⊆ W ∧
    (∀ x ∈ W, x ∈ Ω ↔ 0 < N x) ∧
    (∀ x ∈ frontier Ω, N x = 0 ∧ fderiv ℝ N x ≠ 0) ∧
    ContDiffOn ℝ ∞ N W ∧ (∀ i j, ContDiffOn ℝ ∞ (fun x => h x i j) W) ∧
    (∀ x ∈ W, (h x).PosDef) ∧
    (∀ k : ℕ, ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : X, R < ‖x‖ →
      ‖iteratedFDeriv ℝ k (fun y => N y - 1) x‖ ≤ C / ‖x‖^(k+1) ∧
      ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
        ≤ C / ‖x‖^(k+1)) ∧
    IsDiffeoOnto ψ (conformalSpatialPoint ⁻¹' Ω) D ∧
    (∀ t : ℝ, ∀ z ∈ conformalSpatialPoint ⁻¹' Ω, ψ (z + t • coordBasis 0) = φ t (ψ z)) ∧
    (∀ z ∈ conformalSpatialPoint ⁻¹' Ω, ∀ v w : E4,
      g (ψ z) (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) ψ z v) (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) ψ z w) =
      -(N (conformalSpatialPoint z)) ^ 2 * v 0 * w 0 +
        ∑ i : Fin 3, ∑ j : Fin 3, h (conformalSpatialPoint z) i j * v i.succ * w j.succ) ∧
    (∀ z ∈ conformalSpatialPoint ⁻¹' Ω, ∀ i j, ricci (pullbackCoeffs g ψ) z i j = 0)

end NoHair


