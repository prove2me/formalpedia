-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:28.975694+00:00
-- url     : https://prove2.me/theorems/685447b6-ca9c-43a6-8c87-ef7274e62ec0
-- title:
--   Top Comp S
-- statement:
--   Definitions and structural lemmas for Top Comp S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TopCompS.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def IterAffine : Prop :=
  ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω → ∀ c ∈ Ω, ∀ (L : W →L[ℂ] V) (k : ℕ),
      iteratedFDeriv ℂ k (fun w => F (c + L w)) 0 = (iteratedFDeriv ℂ k F c).compContinuousLinearMap (fun _ => L)
def IterSymm : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω →
    ∀ c ∈ Ω, ∀ (k : ℕ) (v : Fin k → V) (σ : Equiv.Perm (Fin k)), iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v
def IterNested : Prop :=
  ∀ (V W1 W2 : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W1] [NormedSpace ℂ W1]
    [NormedAddCommGroup W2] [NormedSpace ℂ W2] (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω → ∀ c ∈ Ω,
    ∀ (L1 : W1 →L[ℂ] V) (L2 : W2 →L[ℂ] V) (a b : ℕ) (u : Fin a → W1) (w : Fin b → W2),
      iteratedFDeriv ℂ a (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) 0 u =
        iteratedFDeriv ℂ (a + b) F c (Fin.append (fun i => L1 (u i)) (fun i => L2 (w i)))
variable {n : ℕ}
def bdiag (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ blkA j ∧ b ∈ blkA j then c * t a b else if a ∈ blkB j ∧ b ∈ blkB j then c' * t a b else 0
def resOn (s : Finset (Fin n)) (t : Matrix (Fin n) (Fin n) ℂ) : Matrix s s ℂ := fun a b => t a b
def DetDBlock : Prop :=
  ∀ (n j : ℕ) (c c' : ℂ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ) (Ω : Set (Matrix (Fin n) (Fin n) ℂ)), IsOpen Ω → 0 ∈ Ω →
    ContDiffOn ℂ ∞ ψ Ω →
    detD (fun t => ψ (bdiag j c c' t)) =
      c ^ (blkA (n := n) j).card * c' ^ (blkB (n := n) j).card *
        detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          ψ (embOn (blkA j) T + embOn (blkB j) S)))
def CmI (n : ℕ) : M2 n := ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks 1 (Complex.I • 1) (-1) (Complex.I • 1)
def rot (j : ℕ) (θ : ℝ) : M2 n :=
  Cm n * fromBlocks (diagonal fun a => if a ∈ blkA j then Complex.exp (θ * Complex.I) else Complex.exp (-θ * Complex.I)) 0 0
    (diagonal fun a => if a ∈ blkA j then Complex.exp (-θ * Complex.I) else Complex.exp (θ * Complex.I)) * CmI n
def zTop (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then fromBlocks 0 (single r s 1) 0 0
     else if r ∈ blkB j ∧ s ∈ blkB j then -fromBlocks 0 0 (single r s 1) 0
     else if r ∈ blkA j then fromBlocks (single r s 1) 0 0 0 else -fromBlocks 0 0 0 (single r s 1))
def zMid (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then fromBlocks (single r s 1) 0 0 (-single r s 1)
     else if r ∈ blkB j ∧ s ∈ blkB j then fromBlocks (single r s 1) 0 0 (-single r s 1)
     else if r ∈ blkA j then fromBlocks 0 (single r s 1) (-single r s 1) 0 else fromBlocks 0 (single r s 1) (-single r s 1) 0)
def zLow (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then -fromBlocks 0 0 (single r s 1) 0
     else if r ∈ blkB j ∧ s ∈ blkB j then fromBlocks 0 (single r s 1) 0 0
     else if r ∈ blkA j then -fromBlocks 0 0 0 (single r s 1) else fromBlocks (single r s 1) 0 0 0)
def MatAlg : Prop :=
  ∀ (n j : ℕ),
    Cm n * CmI n = 1 ∧ CmI n * Cm n = 1 ∧
    (∀ θ : ℝ, InG (rot (n := n) j θ) ∧ InG (rot (n := n) j θ)⁻¹) ∧
    (∀ (θ : ℝ) (r s : Fin n), Complex.exp (2 * θ * Complex.I) •
        (rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1) =
      Cm n * (zLow j r s + Complex.exp (2 * θ * Complex.I) • zMid j r s +
        Complex.exp (2 * θ * Complex.I) ^ 2 • zTop j r s) * CmI n) ∧
    (∀ P Q R S : Matrix (Fin n) (Fin n) ℂ, (∀ a b, P a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j) →
      (∀ a b, S a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) → (∀ a b, Q a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkA j) →
      (∀ a b, R a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkB j) →
      mX (1 + P) Q R (1 + S) = mX 1 Q R 1 * mX (1 + P) 0 0 (1 + S)) ∧
    (∀ g H : M2 n, InG g → InG H → InG (g * H) ∧ InG g⁻¹)
end PositivityTheory.Rg.Sw.LVs.TC


