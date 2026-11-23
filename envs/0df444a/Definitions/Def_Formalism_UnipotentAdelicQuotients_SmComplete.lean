-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
-- name    : Formalism_UnipotentAdelicQuotients_SmComplete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:53.172389+00:00
-- url     : https://prove2.me/theorems/a76ef1e6-7ffd-4078-9ec5-39e15fe957d9
-- title:
--   Sm Complete
-- statement:
--   Definitions and structural lemmas for Sm Complete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/SmComplete.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped ContDiff
noncomputable section
namespace SmoothVectors
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsClosedMatrixGroup (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G ∧ (∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) ∧
    ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1
def IsIsomRep (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (∀ g ∈ G, ∀ h ∈ G, σ (g * h) = (σ g).comp (σ h)) ∧ (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧
    ∀ v : H, ContinuousOn (fun g => σ g v) G
def lieAlg (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G}
def SmoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀ ∈ G, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ G → f g = F g
def smoothVecs (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  {v | SmoothOn G (fun g => σ g v)}
def dsig (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0
def dsigW (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)
def SmComplete : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsClosedMatrixGroup G → IsIsomRep G σ →
    ∀ v : ℕ → H, (∀ m, v m ∈ smoothVecs G σ) →
      (∀ w : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ w, X ∈ lieAlg G) →
        CauchySeq fun m => dsigW σ w (v m)) →
      ∃ v₀ ∈ smoothVecs G σ, ∀ w : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ w, X ∈ lieAlg G) →
        Tendsto (fun m => dsigW σ w (v m)) atTop (𝓝 (dsigW σ w v₀))
end SmoothVectors
end


