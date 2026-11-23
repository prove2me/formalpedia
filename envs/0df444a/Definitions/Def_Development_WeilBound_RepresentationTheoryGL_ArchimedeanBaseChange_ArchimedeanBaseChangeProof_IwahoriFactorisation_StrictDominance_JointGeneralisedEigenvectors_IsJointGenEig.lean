-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_StrictDominance_JointGeneralisedEigenvectors_IsJointGenEig
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_StrictDominance_JointGeneralisedEigenvectors_IsJointGenEig
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:07.604806+00:00
-- url     : https://prove2.me/theorems/f35214d3-c78d-4b52-b578-82dbff4f3d6a
-- title:
--   Is Joint Gen Eig
-- statement:
--   Definitions and structural lemmas for Is Joint Gen Eig, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/IwahoriFactorisation/StrictDominance/JointGeneralisedEigenvectors/IsJointGenEig.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
namespace PositivityTheory.SphericalProduct
structure CassData (G : Type) [Group G] [TopologicalSpace G] where

  N : Subgroup G

  Nm : Subgroup G

  T : Subgroup G

  J : Subgroup G
  isOpen_J : IsOpen (J : Set G)
  isCompact_J : IsCompact (J : Set G)
  isClosed_N : IsClosed (N : Set G)
  isClosed_Nm : IsClosed (Nm : Set G)
  isClosed_alt : IsClosed (T : Set G)
  norm_N : ∀ t ∈ T, t ∈ Subgroup.normalizer (N : Set G)
  norm_Nm : ∀ t ∈ T, t ∈ Subgroup.normalizer (Nm : Set G)

  fact_low : ∀ x ∈ J, ∃ a ∈ J ⊓ Nm, ∃ b ∈ J ⊓ T, ∃ c ∈ J ⊓ N, x = a * b * c

  fact_up : ∀ x ∈ J, ∃ c ∈ J ⊓ N, ∃ b ∈ J ⊓ T, ∃ a ∈ J ⊓ Nm, x = c * b * a
variable {G : Type} [Group G] [TopologicalSpace G]
namespace CassData
def JT (D : CassData G) : Subgroup D.T := D.J.comap D.T.subtype
def IsDom (D : CassData G) (t : D.T) : Prop :=
  (∀ n ∈ D.J ⊓ D.N, (t : G) * n * (t : G)⁻¹ ∈ D.J ⊓ D.N) ∧
  (∀ n ∈ D.J ⊓ D.Nm, (t : G)⁻¹ * n * (t : G) ∈ D.J ⊓ D.Nm) ∧
  (∀ x ∈ D.J ⊓ D.T, (t : G) * x * (t : G)⁻¹ ∈ D.J ⊓ D.T ∧ (t : G)⁻¹ * x * (t : G) ∈ D.J ⊓ D.T)
def IsStrDom (D : CassData G) (t : D.T) : Prop :=
  D.IsDom t ∧ (∀ n ∈ D.N, ∃ j : ℕ, (t : G) ^ j * n * ((t : G) ^ j)⁻¹ ∈ D.J ⊓ D.N) ∧
    ∀ U : Set G, IsOpen U → (1 : G) ∈ U → ∃ j : ℕ, ∀ n ∈ D.J ⊓ D.Nm, ((t : G) ^ j)⁻¹ * n * (t : G) ^ j ∈ U
def piN (D : CassData G) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) :
    Representation ℂ D.T (Jacquet π D.N) :=
  jacquet π D.N D.T.subtype (fun m => D.norm_N m m.2)
abbrev proj (D : CassData G) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : V) :
    Jacquet π D.N :=
  Submodule.Quotient.mk v
end CassData
open CassData
variable (G) [IsTopologicalGroup G]
def A1 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J),
      PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' →
      PositivityTheory.Lbc.IsHeckeOpG π D.J ((t : G) * t') (U * U')
def A2 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t : D.T, D.IsDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U →
      ∀ v : fixed π D.J, D.proj π ((U v : fixed π D.J) : V) = D.piN π t (D.proj π (v : V))
def A3 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U →
      ∀ v : fixed π D.J, (D.proj π (v : V) = 0 ↔ ∃ j : ℕ, (U ^ j) v = 0)
def A4 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π →
    (∃ t : D.T, D.IsStrDom t) →
    (∀ v : fixed π D.J, D.proj π (v : V) ∈ fixed (D.piN π) D.JT) ∧
    ∀ w ∈ fixed (D.piN π) D.JT, ∃ v : fixed π D.J, D.proj π (v : V) = w
def IsJointGenEig (D : CassData G) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (U : D.T → Module.End ℂ (fixed π D.J)) (ξ : D.T → ℂ) : Prop :=
  ∃ v : fixed π D.J, v ≠ 0 ∧ ∀ t : D.T, D.IsDom t → ∃ k : ℕ, ((U t - ξ t • 1) ^ k) v = 0
def IsExponent (D : CassData G) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (χ : D.T →* ℂˣ) : Prop :=
  ∃ w ∈ fixed (D.piN π) D.JT, w ≠ 0 ∧ ∀ s : D.T, ∃ k : ℕ, ((D.piN π s - (χ s : ℂ) • 1) ^ k) w = 0
def A5 : Prop :=
  ∀ (D : CassData G), (∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π →
    ∀ U : D.T → Module.End ℂ (fixed π D.J), (∀ t, D.IsDom t → PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) (U t)) →
    ∀ ξ : D.T → ℂ, (∀ t t', D.IsDom t → D.IsDom t' → ξ (t * t') = ξ t * ξ t') →
    ∀ t₀ : D.T, D.IsStrDom t₀ → ξ t₀ ≠ 0 →
      (IsJointGenEig G D π U ξ ↔ ∃ χ : D.T →* ℂˣ, IsExponent G D π χ ∧ ∀ t, D.IsDom t → ξ t = χ t)
def A5tr : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π →
    ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U →
    ∀ A : Module.End ℂ (fixed (D.piN π) D.JT), (∀ w, ((A w : fixed (D.piN π) D.JT) : Jacquet π D.N) = D.piN π t w) →
      LinearMap.trace ℂ _ U = LinearMap.trace ℂ _ A
end PositivityTheory.SphericalProduct
end


