-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_JointTheoremALoc
-- name    : Formalism_PieriBlockIdeals_JointTheoremALoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:41.148946+00:00
-- url     : https://prove2.me/theorems/57e4d960-3147-40c2-878b-760f165599d8
-- title:
--   Joint Theorem ALoc
-- statement:
--   Definitions and structural lemmas for Joint Theorem ALoc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/JointTheoremALoc.lean

import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace Formalism.CohomologicalDescent
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization
def exactExp {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) : ℕ := sInf {e : ℕ | LatIncl l B e}
def JointTheoremA : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k),
    (∀ i, ∃ e, LatIncl l (B i) e) →
    (∀ f ∈ AMFK k Γ K ρK, l ^ (∑ i, exactExp l (B i)) • f ∈ formsIn Γ K ρK (tensSub B)) ∧
    sInf {J : ℕ | ∀ f ∈ AMFK k Γ K ρK, l ^ J • f ∈ formsIn Γ K ρK (tensSub B)} ≤
      ∑ i, exactExp l (B i)
def JointTheoremALoc : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k)
    (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K ρK)]
    [IsScalarTower k T (AMFK k Γ K ρK)] (S : Submonoid T),
    (∀ i, ∃ e, LatIncl l (B i) e) →
    (∀ y : LocalizedModule S (AMFK k Γ K ρK),
        (algebraMap k T l) ^ (∑ i, exactExp l (B i)) • y ∈
          locSet S {x : AMFK k Γ K ρK | (x : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)}) ∧
    sInf {J : ℕ | ∀ y : LocalizedModule S (AMFK k Γ K ρK),
        (algebraMap k T l) ^ J • y ∈
          locSet S {x : AMFK k Γ K ρK | (x : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)}} ≤
      ∑ i, exactExp l (B i)
end Formalism.CohomologicalDescent


