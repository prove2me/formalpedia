-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:41.801483+00:00
-- url     : https://prove2.me/theorems/cae0a4eb-d73a-4f01-81aa-93f928d24555
-- title:
--   Is Chain
-- statement:
--   Definitions and structural lemmas for Is Chain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/IsChain.lean

import Mathlib
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
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
section Chain
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
def IsChain (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W) : Prop :=
  ∀ a (i : Fin (l a)), N (B ⟨a, i⟩) = if h : (i : ℕ) + 1 < l a then B ⟨a, ⟨i + 1, h⟩⟩ else 0
end Chain
variable {k : Type} [Field k] {n : ℕ}
structure Frame (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (M : Type) [Fintype M] (L : M → Type)
    [∀ m, Fintype (L m)] (R : Z → (m : M) → L m → L m → k) (o : (m : M) → L m → k)
    (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k) where
  ι : M → Type
  [fι : ∀ m, Fintype (ι m)]
  l : (m : M) → ι m → ℕ
  s : (m : M) → ι m → ℕ
  β : Module.Basis (Σ m, L m × (Σ a : ι m, Fin (l m a))) k (Fin n → k)
  hl : ∀ m a, 0 < l m a
  hs : ∀ m a, s m a ≤ l m a
  hZ : ∀ (z : Z) m (p : L m) (j : Σ a : ι m, Fin (l m a)),
    (z : Matrix (Fin n) (Fin n) k) *ᵥ β ⟨m, (p, j)⟩ = ∑ q, R z m p q • β ⟨m, (q, j)⟩
  hN : ∀ m (p : L m) (a : ι m) (i : Fin (l m a)), N *ᵥ β ⟨m, (p, ⟨a, i⟩)⟩ =
    if h : (i : ℕ) + 1 < l m a then β ⟨m, (p, ⟨a, ⟨i + 1, h⟩⟩)⟩ else 0
  hv : v = ∑ m, ∑ p, ∑ a, if h : s m a < l m a then o m p • β ⟨m, (p, ⟨a, ⟨s m a, h⟩⟩)⟩ else 0
  hA : ∀ A : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * A = A * z) → A * N = N * A →
    ∀ m (p : L m) (a : ι m) (i : Fin (l m a)), (i : ℕ) < s m a → β.repr (A *ᵥ v) ⟨m, (p, ⟨a, i⟩)⟩ = 0
attribute [instance] Frame.fι
end PositivityTheory.RgUd.T.Nil.Orb.BReps


