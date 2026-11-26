-- Prove2me | Definitions.Def_B1s_fried_cluster_matrices_9_10
-- name    : B1s_fried_cluster_matrices_9_10
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:39:52.274125+00:00
-- url     : https://prove2.me/theorems/ab37cdde-bf6e-5274-96ee-eca04d877840
-- title:
--   fried cluster matrices 9 10
-- statement:
--   Definitions and structural lemmas for fried cluster matrices 9 10, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology Matrix Polynomial
namespace ClusterMatrix
section Smoothness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
end Smoothness
end ClusterMatrix
namespace Regularity
end Regularity
namespace HQuot
end HQuot
namespace Ledger
structure ClusterC1 (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Prop where
  deriv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ
  cont : ∀ i j, ContinuousAt (fun q : ℝ × ℝ => M' q.1 q.2 i j) (0, 0)
structure TraceDetC1 (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (a' b' : ℝ → ℝ → ℝ) : Prop where
  deriv_a : ∀ θ τ, HasDerivAt (fun τ => (Hadamard.Ndiv M M' sStar θ τ).trace) (a' θ τ) τ
  deriv_b : ∀ θ τ, HasDerivAt (fun τ => (Hadamard.Ndiv M M' sStar θ τ).det) (b' θ τ) τ
  cont_a' : ContinuousAt (Function.uncurry a') (0, 0)
  cont_b' : ContinuousAt (Function.uncurry b') (0, 0)
structure PureSumC2 (e₁ e₁τ e₁θτ : ℝ → ℝ → ℝ) (K₁ ε : ℝ) : Prop where
  K_pos : 0 < K₁
  ε_pos : 0 < ε
  deriv_τ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ
  deriv_θτ : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ
  bound : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁
structure PureProdC3 (e₂ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) (K₂ ε : ℝ) : Prop where
  K_pos : 0 < K₂
  deriv_τ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ
  deriv_ττ : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ
  deriv_θττ : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ
  bound : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂
structure ClusterC3 (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  deg1 : ∀ i j, ContDiff ℝ 3 fun q : ℝ × ℝ => M q.1 q.2 i j
  deg2 : ∀ i j, ContDiff ℝ 3 fun q : ℝ × ℝ => A q.1 q.2 i j
end Ledger
namespace Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
end Derived
namespace Spectral
open ClusterMatrix
noncomputable def Qpoly (e₁ e₂ : ℝ) : ℝ[X] := X ^ 2 - C e₁ * X + C e₂
end Spectral
namespace Derived
end Derived
namespace Branch
open TwinRate PureZeros
end Branch
namespace Capstone
open TwinRate Hadamard FirstVariation Derived Spectral ClusterMatrix Ledger OrderCount TorsionCore
  Regularity Branch
end Capstone
end FriedCrossing


