-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:19.460064+00:00
-- url     : https://prove2.me/theorems/c98ca0fa-7c34-4894-8b42-cf22726d9c15
-- title:
--   Mem Zero Locus GLIff
-- statement:
--   Definitions and structural lemmas for Mem Zero Locus GLIff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentApproximation/MemZeroLocusGLIff.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_UnipotentStrongApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace PI.UnipApproxD
def Pts {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F)) (R : Type) [CommRing R]
    [Algebra F R] (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2) P = 0
noncomputable def mexp (F : Type) [Field F] {R : Type} [CommRing R] [Algebra F R] (n : ℕ)
    (X : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  ∑ k ∈ Finset.range n, ((k.factorial : F)⁻¹) • X ^ k
def lc {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R] {n d : ℕ}
    (X : Fin d → Matrix (Fin n) (Fin n) F) (a : Fin d → R) : Matrix (Fin n) (Fin n) R :=
  ∑ i, a i • (X i).map (algebraMap F R)
def ExpParam (F : Type) [Field F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) : Prop :=
  ∃ (d : ℕ) (X : Fin d → Matrix (Fin n) (Fin n) F),
    (∀ (R : Type) [CommRing R] [Algebra F R] (a : Fin d → R),
      (lc X a) ^ n = 0 ∧ Pts S R (mexp F n (lc X a))) ∧
    (∀ (R : Type) [CommRing R] [Algebra F R],
      (∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S R, ((g : Matrix (Fin n) (Fin n) R) - 1) ^ n = 0) →
      ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S R, ∃ a : Fin d → R, (g : Matrix (Fin n) (Fin n) R) = mexp F n (lc X a))
def CoreExp : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    HeckeCharacterZeroLocus.IsGroupLocus S →
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ExpParam F n S
def UnipAdele : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S (FiniteAdeleRing (𝓞 F) F),
      ((g : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) - 1) ^ n = 0
def AddDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F))
end PI.UnipApproxD


