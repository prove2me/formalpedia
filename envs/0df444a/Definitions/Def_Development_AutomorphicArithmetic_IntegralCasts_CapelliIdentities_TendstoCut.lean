-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TendstoCut
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TendstoCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:55.090844+00:00
-- url     : https://prove2.me/theorems/33d7c4ee-0dc7-492b-8439-05de8e887bee
-- title:
--   Tendsto Cut
-- statement:
--   Definitions and structural lemmas for Tendsto Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TendstoCut.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi11.Af :
    (F : Type) → [inst : Field F] → [NumberField F] → Type :=
    fun (F : Type) [Field F] [NumberField F] ↦ IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F
theorem UpperTheory.Reformulated.B.Qi11.aux2 :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v),
      ∀ᶠ (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
        Pi.single v a x ∈
          (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F x) :
            Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F x)) := by
  intro F _ _ v a
  refine (Set.finite_singleton v).subset fun x hx => ?_
  by_contra h
  apply hx
  have hne : x ≠ v := h
  simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hne]
  exact zero_mem _
noncomputable def UpperTheory.Reformulated.B.Qi11.sglV :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
        (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ↦
      (⟨Pi.single v a, UpperTheory.Reformulated.B.Qi11.aux2 v a⟩ :
        { x :
          (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
              i //
          ∀ᶠ (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
            x i ∈
              (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                  (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) :
                    Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)))
                i })
noncomputable def UpperTheory.Reformulated.B.Qi11.sglS :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F]
        (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
      ∑ v ∈ A, UpperTheory.Reformulated.B.Qi11.sglV v (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)


