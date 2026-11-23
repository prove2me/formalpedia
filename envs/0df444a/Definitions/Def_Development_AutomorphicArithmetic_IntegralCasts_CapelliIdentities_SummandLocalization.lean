-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummandLocalization
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummandLocalization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:33.154922+00:00
-- url     : https://prove2.me/theorems/0487301c-003f-4cf9-bff5-33b626d88b0e
-- title:
--   Summand Localization
-- statement:
--   Definitions and structural lemmas for Summand Localization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SummandLocalization.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := (let p2m_original_helper : ∀ {R : Type _} [inst : CommRing R] {W : Type _} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
                  (S : Submonoid R) (L : Submodule R W) {x y : W},
                  x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := (by
              rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
              refine ⟨s * t, S.mul_mem hs ht, ?_⟩
              rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
              exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
            ); @p2m_original_helper R inst W inst_1 inst_2 S L _ _),
        zero_mem' := (show ∀ {R : Type _} [inst : CommRing R] {W : Type _} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
                  (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L from by
              intro R _ W _ _ S L
              exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
            ) S L, smul_mem' := (show ∀ {R : Type _} [inst : CommRing R] {W : Type _} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
                  (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
                  x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} from by
              rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
              refine ⟨s, hs, ?_⟩
              rw [smul_comm]
              exact L.smul_mem r hx
            ) S L : Submodule R W }
noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locF :
    {K F W : Type} →
      [inst : Field K] →
        [inst_1 : Field F] →
          [Algebra F K] →
            [inst_3 : AddCommGroup W] →
              [inst_4 : _root_.Module (NumberField.RingOfIntegers K) W] →
                Ideal (NumberField.RingOfIntegers F) →
                  Submodule (NumberField.RingOfIntegers K) W → Submodule (NumberField.RingOfIntegers K) W :=
    fun {K F W : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup W] [_root_.Module (NumberField.RingOfIntegers K) W]
        (𝔭 : Ideal (NumberField.RingOfIntegers F)) (L : Submodule (NumberField.RingOfIntegers K) W) ↦
      UpperTheory.Reformulated.B.SummandLocalization.locS
        (Submonoid.closure
          {s : NumberField.RingOfIntegers K |
            ∃ t ∉ 𝔭,
              (Algebra.algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) :
                    NumberField.RingOfIntegers F → NumberField.RingOfIntegers K)
                  t =
                s})
        L
noncomputable def UpperTheory.Reformulated.B.SummandLocalization.SummandLoc :
    Prop :=
    ∀ (K F V : Type) [inst : Field K] [NumberField K] [inst_2 : Field F] [NumberField F] [inst_4 : Algebra F K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [FiniteDimensional K V]
      [inst_8 : _root_.Module (NumberField.RingOfIntegers K) V] [inst_9 : IsScalarTower (NumberField.RingOfIntegers K) K V]
      (X : Submodule K V) (𝔭 : Ideal (NumberField.RingOfIntegers F)),
      𝔭.IsMaximal →
        ∀ (Λ : Submodule (NumberField.RingOfIntegers K) V),
          (∃ (Λ₀ : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsLattice K Λ₀ ∧ UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 Λ₀ = Λ) →
            ∃ (π : V →ₗ[K] V), (∀ (v : V), (π : V → V) v ∈ X) ∧ (∀ x ∈ X, (π : V → V) x = x) ∧ ∀ y ∈ Λ, (π : V → V) y ∈ Λ


