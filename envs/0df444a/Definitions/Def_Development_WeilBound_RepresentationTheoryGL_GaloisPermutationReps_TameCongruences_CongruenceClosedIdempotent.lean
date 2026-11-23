-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_GaloisPermutationReps_TameCongruences_CongruenceClosedIdempotent
-- name    : Development_WeilBound_RepresentationTheoryGL_GaloisPermutationReps_TameCongruences_CongruenceClosedIdempotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:16.040117+00:00
-- url     : https://prove2.me/theorems/3a2bcaae-6d2e-4f89-896f-349978b296af
-- title:
--   Congruence Closed Idempotent
-- statement:
--   Definitions and structural lemmas for Congruence Closed Idempotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/GaloisPermutationReps/TameCongruences/CongruenceClosedIdempotent.lean

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
open Polynomial
namespace PositivityTheory.Rg.DzCong
def permRep (G X : Type) [Group G] [MulAction G X] : Representation ℂ G (X → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun x => g⁻¹ • x
  map_one' := by ext f x; simp [LinearMap.funLeft_apply]
  map_mul' g h := by ext f x; simp [LinearMap.funLeft_apply, mul_smul]
def Free (G X : Type) [Group G] [MulAction G X] : Prop := ∀ (g : G) (x : X), g • x = x → g = 1
structure Fam (G : Type) {X I : Type} [Group G] [MulAction G X] [Fintype X] (T : I → Matrix X X ℤ) : Prop where
  comm : ∀ i j, T i * T j = T j * T i
  equi : ∀ i (g : G) x y, T i (g • x) (g • y) = T i x y
def Eig {X I : Type} [Fintype X] (T : I → Matrix X X ℤ) (θ : I → ℂ) : Submodule ℂ (X → ℂ) where
  carrier := {f | ∀ i, ((T i).map (Int.cast : ℤ → ℂ)).mulVec f = θ i • f}
  add_mem' := fun {f g} hf hg i => by rw [Matrix.mulVec_add, hf i, hg i, smul_add]
  zero_mem' := fun i => by simp
  smul_mem' := fun c f hf i => by rw [Matrix.mulVec_smul, hf i, smul_comm]
def GenEig {F X I : Type} [Field F] [Fintype X] [DecidableEq X] (T : I → Matrix X X F) (θ : I → F) : Submodule F (X → F) :=
  ⨅ i, Module.End.maxGenEigenspace (Matrix.toLin' (T i)) (θ i)
open Classical in

def StableSubspaceMobius : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype (Submodule K V)],
    ∃ μ : Module.End K V → Submodule K V → ℤ,
      (∀ g, μ g ⊥ = 1) ∧
      (∀ g W, W ≠ ⊥ → W.map g ≤ W →
        ∑ W' ∈ Finset.univ.filter (fun W' : Submodule K V => W' ≤ W ∧ W'.map g ≤ W'), μ g W' = 0) ∧
      (∀ g g' W, W.map g ≤ W → (∀ v ∈ W, g v = g' v) → μ g W = μ g' W) ∧
      (∀ u, u ≠ 1 → IsNilpotent (u - 1) → μ u ⊤ = 0) ∧
      μ 1 ⊤ ≠ 0
def FreeActionIdempotentTrace : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (G X : Type) [Group G] [Finite G] [MulAction G X] [Fintype X] [DecidableEq X], Free G X →
    ∀ e : Matrix X X (PadicAlgCl l), (∀ x y, ‖e x y‖ ≤ 1) → e * e = e → (∀ (g : G) x y, e (g • x) (g • y) = e x y) →
    ∀ g : G, l ∣ orderOf g → ∑ x, e x (g • x) = 0
def CongruenceClosedIdempotent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (X I : Type) [Fintype X] [DecidableEq X] (T : I → Matrix X X (PadicAlgCl l)),
    (∀ i x y, ‖T i x y‖ ≤ 1) → (∀ i j, T i * T j = T j * T i) →
    ∀ W : (I → PadicAlgCl l) → Prop,
      (∀ θ θ', GenEig T θ ≠ ⊥ → GenEig T θ' ≠ ⊥ → (∀ i, ‖θ i - θ' i‖ < 1) → W θ → W θ') →
      ∃ e : Matrix X X (PadicAlgCl l), (∀ x y, ‖e x y‖ ≤ 1) ∧ e * e = e ∧
        e ∈ Algebra.adjoin (PadicAlgCl l) (Set.range T) ∧
        (∀ θ, W θ → ∀ f ∈ GenEig T θ, e.mulVec f = f) ∧ ∀ θ, ¬ W θ → ∀ f ∈ GenEig T θ, e.mulVec f = 0
def StOcc : Prop :=
  ∀ (G X I W : Type) [Group G] [Finite G] [MulAction G X] [Fintype X] [Nonempty X] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Nontrivial W] (τ : Representation ℂ G W) (T : I → Matrix X X ℤ), Free G X → Fam G T →
    ∃ (θ : I → ℂ) (j : W →ₗ[ℂ] (X → ℂ)), j ≠ 0 ∧ (∀ v, j v ∈ Eig T θ) ∧ ∀ g v, j (τ g v) = permRep G X g (j v)
end PositivityTheory.Rg.DzCong
end


