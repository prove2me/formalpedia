-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:17.280015+00:00
-- url     : https://prove2.me/theorems/db354028-c284-4d39-a89e-db091344fa85
-- title:
--   Exists Nsmul Mem
-- statement:
--   Definitions and structural lemmas for Exists Nsmul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
section Alg
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def lsm (c : K) : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V c).restrictScalars (𝓞 K)
end Alg
section Ht
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end Ht
section Max
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end Max
section Pow
variable {K : Type} [Field K] [NumberField K]
end Pow
section Loc
variable {R : Type} [CommRing R]
def locLen (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q] : ℕ∞ :=
  Module.length (Localization.AtPrime w) (LocalizedModule w.primeCompl Q)
end Loc
section Len
end Len
section Span
end Span
section Tests
example : ∃ (K V ι : Type) (_ : Field K) (_ : NumberField K) (_ : StarRing K)
    (_ : IsTotallyComplex K) (_ : AddCommGroup V) (_ : Module K V) (_ : Module (𝓞 K) V)
    (_ : IsScalarTower (𝓞 K) K V) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (M : Submodule (𝓞 K) V),
    (∀ v, IsUnit (X v).det) ∧ M.FG ∧ M ≠ ⊥ := by
  have hne : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
  have hcyc : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  refine ⟨CyclotomicField 5 ℚ, CyclotomicField 5 ℚ, Unit, inferInstance, inferInstance,
    starRingOfComm, IsCyclotomicExtension.Rat.isTotallyComplex (n := 5) _ (by norm_num),
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Basis.singleton Unit _, fun _ => 1, Submodule.span _ {1}, fun v => by simp,
    Submodule.fg_span (Set.finite_singleton _), ?_⟩
  rw [Ne, Submodule.span_singleton_eq_bot]
  exact one_ne_zero
end Tests
section LocPow
variable {K : Type} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
def HalfUnit (w : Ideal (𝓞 K)) (J : FI) : Prop :=
  ∃ t : 𝓞 K, t ∉ w ∧ ∀ x ∈ J, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * x
def WUnit (w : Ideal (𝓞 K)) (J : FI) : Prop := J ≠ 0 ∧ HalfUnit w J ∧ HalfUnit w J⁻¹
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end LocPow
section Local
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Local
section LocalTest
def rlocToK {K : Type} [Field K] [NumberField K] (w : FinPl K) : Rloc w →+* K :=
  haveI := w.2.isPrime
  IsLocalization.lift (M := w.1.primeCompl) (S := Rloc w) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ fun h0 => y.2 ?_
    have : (y : 𝓞 K) = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0)
    rw [this]; exact Ideal.zero_mem _)
end LocalTest
end Formalism.LFunctionChainParameters.slopeLatticeData


