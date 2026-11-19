-- Prove2me | Definitions.Def_SymplecticBallPacking
-- name    : SymplecticBallPacking
-- status  : Definition
-- author  : @LG
-- created : 2026-11-17T02:55:55.131209+00:00
-- url     : https://prove2.me/theorems/33772ed8-67b3-4313-98b8-a4a75e6e4676
-- title:
--   Phase-space balls, Hamiltonian vector field and flow for symplectic ball packing
-- statement:
--   Defines the Euclidean-radius balls, the input-ball centers, the Hamiltonian vector field, the time-$1$ Hamiltonian flow predicate, and global symplectomorphisms used to state the FrontierMath symplectic ball-packing problem. Phase space $\mathbb C^n\cong\mathbb R^{2n}$, the standard symplectic form, capacity balls and symplectic embeddings are reused from the platform's `BallPacking` definitions; this file adds the Euclidean-radius convention and the Hamiltonian-flow machinery. The Hamiltonian convention is $\omega(X_H,\cdot)=dH$, i.e. $X_H=(\partial H/\partial p,-\partial H/\partial q)$. These definitions are reusable for any Hamiltonian/symplectic formalization on $\mathbb R^{2n}$.
-- source:
--   Epoch AI, FrontierMath: Open Problems — Symplectic Ball Packing, https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing (Prompt: balls, Hamiltonian flow); McDuff–Salamon, Introduction to Symplectic Topology, 3rd ed., §3.2 (Hamiltonian vector fields).

import Mathlib
import Definitions.Def_BallPacking

namespace SymplecticBallPacking
open OAI.HigherDimensionalBallPacking
open Set

def euclClosedBall {n : ℕ} (c : Phase n) (r : ℝ) : Set (Phase n) :=
  {z | ∑ j, Complex.normSq (z j - c j) ≤ r ^ 2}

def inputCenter {k : ℕ} (i : Fin k) : Phase 2 :=
  Pi.single 0 ((3 * i.val : ℕ) : ℂ)

noncomputable def hamiltonianVectorField {n : ℕ} (H : Phase n → ℝ) (z : Phase n) : Phase n :=
  fun j => (↑(fderiv ℝ H z (Pi.single j Complex.I)) : ℂ) -
    Complex.I * (↑(fderiv ℝ H z (Pi.single j (1 : ℂ))) : ℂ)

def IsHamiltonianFlow {n : ℕ} (H : Phase n → ℝ → ℝ) (Φ : ℝ → Phase n → Phase n) : Prop :=
  (∀ x, Φ 0 x = x) ∧
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    HasDerivWithinAt (fun s => Φ s x)
      (hamiltonianVectorField (fun z => H z t) (Φ t x)) (Icc (0 : ℝ) 1) t

def IsSymplectomorphism {n : ℕ} (f : Phase n → Phase n) : Prop :=
  SymplecticOn (Set.univ : Set (Phase n)) f ∧ Function.Bijective f

end SymplecticBallPacking


