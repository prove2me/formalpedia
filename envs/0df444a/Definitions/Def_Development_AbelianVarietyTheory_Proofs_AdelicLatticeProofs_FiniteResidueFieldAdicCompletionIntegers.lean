-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:53:09.903955+00:00
-- url     : https://prove2.me/theorems/aadf14a9-5d88-4a8d-b12a-ea974c91fc9e
-- title:
--   Finite Residue Field Adic Completion Integers
-- statement:
--   Definitions and structural lemmas for Finite Residue Field Adic Completion Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
namespace GlobalTheory.SelfDualGenus
section Completion
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
end Completion
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
section LocalAlgebra
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
abbrev LocAlg : Type := v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] E
def locEmb : E →+* LocAlg v :=
  (Algebra.TensorProduct.includeRight : E →ₐ[(maximalRealSubfield E)] LocAlg v)
def locConj : LocAlg v →+* LocAlg v :=
  (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion (maximalRealSubfield E)) (v.adicCompletion (maximalRealSubfield E)))
    (IsCMField.complexConj E).toAlgHom : LocAlg v →ₐ[v.adicCompletion (maximalRealSubfield E)] LocAlg v)
theorem locConj_algebraMap (a : v.adicCompletion (maximalRealSubfield E)) :
    locConj v (algebraMap _ (LocAlg v) a) = algebraMap _ (LocAlg v) a :=
  AlgHom.commutes (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion (maximalRealSubfield E)) (v.adicCompletion (maximalRealSubfield E)))
    (IsCMField.complexConj E).toAlgHom) a
def locOrder : Subalgebra (v.adicCompletionIntegers (maximalRealSubfield E)) (LocAlg v) :=
  Algebra.adjoin _ (Set.range fun a : 𝓞 E => locEmb v a)
theorem locEmb_mem_locOrder (a : 𝓞 E) : locEmb v a ∈ locOrder v :=
  Algebra.subset_adjoin ⟨a, rfl⟩
theorem locConj_algebraMap' (a : v.adicCompletionIntegers (maximalRealSubfield E)) :
    locConj v (algebraMap _ (LocAlg v) a) = algebraMap _ (LocAlg v) a :=
  locConj_algebraMap v (a : v.adicCompletion (maximalRealSubfield E))
theorem locConj_mem {z : LocAlg v} (hz : z ∈ locOrder v) : locConj v z ∈ locOrder v := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact locEmb_mem_locOrder v (IsCMField.ringOfIntegersComplexConj E a)
  | algebraMap a => rw [locConj_algebraMap']; exact Subalgebra.algebraMap_mem _ a
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
def locOrderConj : locOrder v →+* locOrder v :=
  (locConj v).restrict (locOrder v).toSubring (locOrder v).toSubring fun _ => locConj_mem v
end LocalAlgebra
section SemiLocal
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
theorem algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl ≤ (𝓞 E)⁰ :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors
def semiLoc : Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)
    (algebraMapSubmonoid_le v)
instance isLocalization_semiLoc :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl) (semiLoc v) :=
  Localization.subalgebra.isLocalization_ofField E _ _
instance isFractionRing_semiLoc : IsFractionRing (semiLoc v) E :=
  Localization.subalgebra.isFractionRing_ofField E _ _
instance isPrincipalIdealRing_semiLoc : IsPrincipalIdealRing (semiLoc v) :=
  haveI : IsDedekindDomain (semiLoc v) :=
    IsLocalization.isDedekindDomain (𝓞 E) (algebraMapSubmonoid_le v) _
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot
end SemiLocal
section Gram
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
variable {G : Matrix (Fin r) (Fin r) E} {L : Submodule (𝓞 E) (Fin r → E)}
  {𝔟 : FractionalIdeal (𝓞 E)⁰ E} {g : GL (Fin r) E} {b : E}
end Gram
section LocalLattice
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
def locLattice (L : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (v.adicCompletionIntegers (maximalRealSubfield E)) (Fin r → LocAlg v) :=
  Submodule.span _ ((fun x i => locEmb v (x i)) '' (L : Set (Fin r → E)))
variable {L : Submodule (𝓞 E) (Fin r → E)}
end LocalLattice
section NormalForm
variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
end NormalForm
def IsLocalIsometry (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E))
    (G' : Matrix (Fin r) (Fin r) E) (L' : Submodule (𝓞 E) (Fin r → E))
    (γ : GL (Fin r) (LocAlg v)) : Prop :=
  G'.map (locEmb v) = (γ : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * G.map (locEmb v) *
      (γ : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) ∧
    ∀ x, x ∈ locLattice v L' ↔ (γ : Matrix (Fin r) (Fin r) (LocAlg v)) *ᵥ x ∈ locLattice v L
variable {G G' : Matrix (Fin r) (Fin r) E} {L L' : Submodule (𝓞 E) (Fin r → E)}
section Modular
variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {𝔟 : FractionalIdeal (𝓞 E)⁰ E}
end Modular
variable (E r) in

def signMatrix (p : ℕ) : Matrix (Fin r) (Fin r) E :=
  Matrix.diagonal fun a => if (a : ℕ) < p then 1 else -1
end GlobalTheory.SelfDualGenus
namespace GlobalTheory
open SelfDualGenus
end GlobalTheory


