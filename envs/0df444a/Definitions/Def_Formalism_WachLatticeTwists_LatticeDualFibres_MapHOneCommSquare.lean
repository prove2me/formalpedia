-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_MapHOneCommSquare
-- name    : Formalism_WachLatticeTwists_LatticeDualFibres_MapHOneCommSquare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:11.697203+00:00
-- url     : https://prove2.me/theorems/65dc9108-dd62-4947-aa9f-23c6f2213f7f
-- title:
--   Map HOne Comm Square
-- statement:
--   Definitions and structural lemmas for Map HOne Comm Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/MapHOneCommSquare.lean

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory.Gal
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.LOC
def MapHOneCommSquare : Prop :=
  ∀ (R G M M₁ M₂ M₃ : Type u) [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M]
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [IsTopologicalAddGroup M₁]
    [ContinuousConstSMul R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [IsTopologicalAddGroup M₂]
    [ContinuousConstSMul R M₂]
    [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [IsTopologicalAddGroup M₃]
    [ContinuousConstSMul R M₃]
    (ρ : Representation R G M) (ρ₁ : Representation R G M₁) (ρ₂ : Representation R G M₂)
    (ρ₃ : Representation R G M₃)
    (u : M →ₗ[R] M₁) (v : M₁ →ₗ[R] M₃) (u' : M →ₗ[R] M₂) (v' : M₂ →ₗ[R] M₃)
    (hu : Continuous u) (hv : Continuous v) (hu' : Continuous u') (hv' : Continuous v')
    (eu : ∀ g m, u (ρ g m) = ρ₁ g (u m)) (ev : ∀ g m, v (ρ₁ g m) = ρ₃ g (v m))
    (eu' : ∀ g m, u' (ρ g m) = ρ₂ g (u' m)) (ev' : ∀ g m, v' (ρ₂ g m) = ρ₃ g (v' m)),
    (∀ m, v (u m) = v' (u' m)) →
    ∀ x : H1 ρ, mapH1 ρ₁ ρ₃ v hv ev (mapH1 ρ ρ₁ u hu eu x) =
      mapH1 ρ₂ ρ₃ v' hv' ev' (mapH1 ρ ρ₂ u' hu' eu' x)
def StatCupSquare : Prop :=
  ∀ (R G M₁ M₁' M M' P M₂ M₂' P₂ : Type u) [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [IsTopologicalAddGroup M₁]
    [ContinuousConstSMul R M₁]
    [AddCommGroup M₁'] [Module R M₁'] [TopologicalSpace M₁'] [IsTopologicalAddGroup M₁']
    [ContinuousConstSMul R M₁']
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    [ContinuousConstSMul R M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [ContinuousConstSMul R P]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [IsTopologicalAddGroup M₂]
    [ContinuousConstSMul R M₂]
    [AddCommGroup M₂'] [Module R M₂'] [TopologicalSpace M₂'] [IsTopologicalAddGroup M₂']
    [ContinuousConstSMul R M₂']
    [AddCommGroup P₂] [Module R P₂] [TopologicalSpace P₂] [IsTopologicalAddGroup P₂]
    [ContinuousConstSMul R P₂]
    (ρ₁ : Representation R G M₁) (ρ₁' : Representation R G M₁')
    (ρ : Representation R G M) (ρ' : Representation R G M') (ρP : Representation R G P)
    (ρ₂ : Representation R G M₂) (ρ₂' : Representation R G M₂') (ρP₂ : Representation R G P₂)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (ρ g x) (ρ' g y) = ρP g (b x y)) (hρ' : ContAction ρ')
    (b₂ : M₂ →ₗ[R] M₂' →ₗ[R] P₂) (hb₂ : Continuous fun p : M₂ × M₂' => b₂ p.1 p.2)
    (hbe₂ : ∀ g x y, b₂ (ρ₂ g x) (ρ₂' g y) = ρP₂ g (b₂ x y)) (hρ₂' : ContAction ρ₂')
    (α : M₁ →ₗ[R] M) (hα : Continuous α) (eα : ∀ g m, α (ρ₁ g m) = ρ g (α m))
    (β : M₁' →ₗ[R] M') (hβ : Continuous β) (eβ : ∀ g m, β (ρ₁' g m) = ρ' g (β m))
    (α₂ : M₁ →ₗ[R] M₂) (hα₂ : Continuous α₂) (eα₂ : ∀ g m, α₂ (ρ₁ g m) = ρ₂ g (α₂ m))
    (β₂ : M₁' →ₗ[R] M₂') (hβ₂ : Continuous β₂) (eβ₂ : ∀ g m, β₂ (ρ₁' g m) = ρ₂' g (β₂ m))
    (γ : P₂ →ₗ[R] P) (hγ : Continuous γ) (eγ : ∀ g m, γ (ρP₂ g m) = ρP g (γ m)),
    (∀ a a', b (α a) (β a') = γ (b₂ (α₂ a) (β₂ a'))) →
    ∀ (x : H1 ρ₁) (y : H1 ρ₁'),
      cupProductH1H1 ρ ρ' ρP b hb hbe hρ' (mapH1 ρ₁ ρ α hα eα x) (mapH1 ρ₁' ρ' β hβ eβ y) =
        mapH2 ρP₂ ρP γ hγ eγ
          (cupProductH1H1 ρ₂ ρ₂' ρP₂ b₂ hb₂ hbe₂ hρ₂' (mapH1 ρ₁ ρ₂ α₂ hα₂ eα₂ x)
            (mapH1 ρ₁' ρ₂' β₂ hβ₂ eβ₂ y))
def StatConnTors : Prop :=
  ∀ (O G T V A : Type u) [CommRing O] [IsDomain O] [Group G] [TopologicalSpace G]
    [AddCommGroup T] [Module O T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul O T]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul O V]
    [AddCommGroup A] [Module O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul O A]
    (ρT : Representation O G T) (ρV : Representation O G V) (ρA : Representation O G A)
    (j : T →ₗ[O] V) (q : V →ₗ[O] A),
    Topology.IsEmbedding j → (∀ g m, j (ρT g m) = ρV g (j m)) → (∀ g m, q (ρV g m) = ρA g (q m)) →
    Function.Surjective q → LinearMap.ker q = LinearMap.range j → ContAction ρV →
    (∀ c : O, c ≠ 0 → Function.Bijective fun v : V => c • v) →
    (∀ a : A, ∃ c : O, c ≠ 0 ∧ c • a = 0) →
    ∃ δ : H0 ρA →ₗ[O] H1 ρT, LinearMap.range δ = Submodule.torsion O (H1 ρT)
end Formalism.RepresentationBoundsCohomology.LOC


