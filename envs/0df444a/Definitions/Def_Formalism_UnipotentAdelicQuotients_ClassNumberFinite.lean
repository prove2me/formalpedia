-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_ClassNumberFinite
-- name    : Formalism_UnipotentAdelicQuotients_ClassNumberFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:47.638735+00:00
-- url     : https://prove2.me/theorems/01c8f3c8-328c-41a8-a9bd-a8992971eda3
-- title:
--   Class Number Finite
-- statement:
--   Definitions and structural lemmas for Class Number Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/ClassNumberFinite.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace HeckeCharacterZeroLocus
open NumberField IsDedekindDomain
def zeroLocusGL {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (R : Type) [CommRing R] [Algebra F R] : Set (GL (Fin n) R) :=
  {g | ∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) R) ij.1 ij.2) P = 0}
def IsGroupLocus {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F)) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra F R],
    1 ∈ zeroLocusGL S R ∧ (∀ g ∈ zeroLocusGL S R, ∀ h ∈ zeroLocusGL S R, g * h ∈ zeroLocusGL S R) ∧
      (∀ g ∈ zeroLocusGL S R, g⁻¹ ∈ zeroLocusGL S R)
def locusSubgroup {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (R : Type) [CommRing R] [Algebra F R] : Subgroup (GL (Fin n) R) where
  carrier := zeroLocusGL S R
  one_mem' := (hS R).1
  mul_mem' := fun {a b} ha hb => (hS R).2.1 a ha b hb
  inv_mem' := fun {a} ha => (hS R).2.2 a ha
def ClassNumberFinite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (U : Subgroup (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))),
    IsOpen (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    IsCompact (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    ∃ T : Finset (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, γ ∈ zeroLocusGL S F ∧
        ∃ s ∈ T, ∃ u ∈ U,
          (x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) =
            Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ *
              (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) * ((u : locusSubgroup S hS _) : GL (Fin n) _)
end HeckeCharacterZeroLocus


