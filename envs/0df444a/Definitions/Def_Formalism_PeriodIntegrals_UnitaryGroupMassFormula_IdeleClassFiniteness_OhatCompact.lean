-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:05.79879+00:00
-- url     : https://prove2.me/theorems/b97a102e-8206-4457-a9c3-63c3c31df969
-- title:
--   Ohat Compact
-- statement:
--   Definitions and structural lemmas for Ohat Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/OhatCompact.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_ClassNumberFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.ClassFinD
open NumberField IsDedekindDomain
def Ohat (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun {a b} ha hb v => by have h := mul_mem (ha v) (hb v); exact h
  one_mem' := fun v => (v.adicCompletionIntegers F).one_mem
  add_mem' := fun {a b} ha hb v => by have h := add_mem (ha v) (hb v); exact h
  zero_mem' := fun v => (v.adicCompletionIntegers F).zero_mem
  neg_mem' := fun {a} ha v => by have h := neg_mem (ha v); exact h
def MatInt {F : Type} [Field F] [NumberField F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  ∀ i j, M i j ∈ Ohat F
theorem matInt_one (F : Type) [Field F] [NumberField F] (n : ℕ) :
    MatInt (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (Ohat F).one_mem
  · exact (Ohat F).zero_mem
theorem matInt_mul {F : Type} [Field F] [NumberField F] {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)} (hM : MatInt M) (hN : MatInt N) :
    MatInt (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (Ohat F).sum_mem fun k _ => (Ohat F).mul_mem (hM i k) (hN k j)
def KGL (F : Type) [Field F] [NumberField F] (n : ℕ) :
    Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) where
  carrier := {g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F) | MatInt g.val ∧ MatInt g⁻¹.val}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · exact matInt_one F n
    · rw [inv_one]; exact matInt_one F n
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact matInt_mul ha hb
    · rw [mul_inv_rev, Units.val_mul]; exact matInt_mul hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩
abbrev glIncl (F : Type) [Field F] [NumberField F] (n : ℕ) :
    GL (Fin n) F →* GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
  Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom
def Kloc {F : Type} [Field F] [NumberField F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : HeckeCharacterZeroLocus.IsGroupLocus S) : Subgroup (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) :=
  (KGL F n).comap (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)).subtype
def BorelK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : HeckeCharacterZeroLocus.IsGroupLocus S),
    ∃ T : Finset (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, γ ∈ HeckeCharacterZeroLocus.zeroLocusGL S F ∧
        ∃ s ∈ T, ∃ u ∈ Kloc S hS,
          (x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) = glIncl F n γ * (s : GL (Fin n) _) * (u : GL (Fin n) _)
def BorelKGL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ),
    ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, ∃ s ∈ T, ∃ k ∈ KGL F n,
        x = glIncl F n γ * s * k
def BorelRed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : HeckeCharacterZeroLocus.IsGroupLocus S) (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
    ∃ T : Finset (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F),
        (∃ γ : GL (Fin n) F, ∃ k ∈ KGL F n, (x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) = glIncl F n γ * g * k) →
        ∃ δ : GL (Fin n) F, δ ∈ HeckeCharacterZeroLocus.zeroLocusGL S F ∧ ∃ s ∈ T, ∃ u ∈ Kloc S hS,
          (x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) = glIncl F n δ * (s : GL (Fin n) _) * (u : GL (Fin n) _)
def KlocCompact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : HeckeCharacterZeroLocus.IsGroupLocus S), IsCompact (Kloc S hS : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)))
def OhatCompact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], IsCompact (Ohat F : Set (FiniteAdeleRing (𝓞 F) F))
end PIW.ClassFinD
end


