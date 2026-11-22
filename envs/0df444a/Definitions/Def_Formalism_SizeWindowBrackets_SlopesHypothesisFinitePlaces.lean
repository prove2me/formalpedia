-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
-- name    : Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:41.646993+00:00
-- url     : https://prove2.me/theorems/eb69750b-fc96-4d50-8954-94fd4410d9db
-- title:
--   Slopes Hypothesis Finite Places
-- statement:
--   Definitions and structural lemmas for Slopes Hypothesis Finite Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/SlopesHypothesisFinitePlaces.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
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
open Formalism.HN
abbrev FinPl (K : Type) [Field K] [NumberField K] := {p : Ideal (𝓞 K) // p.IsMaximal}
def idealPow {K : Type} [Field K] [NumberField K] (n : FinPl K →₀ ℤ) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  n.prod fun w k => ((w.1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) ^ k
def ell {K : Type} [Field K] [NumberField K] (w : FinPl K) : ℝ :=
  Real.log (Ideal.absNorm w.1 : ℝ) / (Module.finrank ℚ K : ℝ)
open Classical in

def sgSum {K : Type} [Field K] [NumberField K] (σ τ : FinPl K →₀ ℤ) : ℝ :=
  ∑ w ∈ σ.support ∪ τ.support, 2 * ell w * ((σ w : ℝ) - (τ w : ℝ))
def modLat {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (σ : FinPl K →₀ ℤ) (N : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Formalism.HermitianLatticesTheory.idealSmul ((idealPow (-σ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) N
def SlopeRelationsIndex : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (σ τ : FinPl K →₀ ℤ) (M N : Submodule (𝓞 K) V), M.FG → M ≠ ⊥ →
      N ≤ Formalism.HermitianLatticesTheory.idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
        Submodule (𝓞 K) K) M →
      rkK N = rkK M →
      muMaxDef b X (modLat σ N) ≤ muMaxDef b X M + sgSum σ τ ∧
      muDef b X (modLat σ N) = muDef b X M + sgSum σ τ -
        2 * Real.log (N.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.idealSmul
          ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)
            M).toAddSubgroup : ℝ) / ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ))
def lenAt {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (w : FinPl K) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  haveI := w.2.isPrime
  Module.length (Localization.AtPrime w.1)
    (LocalizedModule w.1.primeCompl (A ⧸ B.comap A.subtype))
def IndexLen : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V), B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 →
      (∀ w : FinPl K, lenAt w A B ≠ ⊤) ∧
      (Function.support fun w : FinPl K => lenAt w A B).Finite ∧
      B.toAddSubgroup.relIndex A.toAddSubgroup =
        ∏ᶠ w : FinPl K, Ideal.absNorm w.1 ^ (lenAt w A B).toNat
def LenAtSpan : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] (w : FinPl K),
    haveI := w.2.isPrime
    ∀ [Module (Localization.AtPrime w.1) V] [IsScalarTower (𝓞 K) (Localization.AtPrime w.1) V]
      (A B : Submodule (𝓞 K) V), B ≤ A →
      lenAt w A B = Module.length (Localization.AtPrime w.1)
        (Submodule.span (Localization.AtPrime w.1) (A : Set V) ⧸
          (Submodule.span (Localization.AtPrime w.1) (B : Set V)).comap
            (Submodule.span (Localization.AtPrime w.1) (A : Set V)).subtype)
def LocIdealPow : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : FinPl K),
    haveI := w.2.isPrime
    ∀ [Module (Localization.AtPrime w.1) V] [IsScalarTower (𝓞 K) (Localization.AtPrime w.1) V]
      (ϖ : 𝓞 K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 → ∀ (n : FinPl K →₀ ℤ) (M : Submodule (𝓞 K) V),
      Submodule.span (Localization.AtPrime w.1) ((Formalism.HermitianLatticesTheory.idealSmul
        ((idealPow n : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M :
          Submodule (𝓞 K) V) : Set V) =
      Submodule.span (Localization.AtPrime w.1)
        ((fun x : V => (algebraMap (𝓞 K) K ϖ ^ n w) • x) '' (M : Set V))
def SlopeRelationsLength : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (σ τ : FinPl K →₀ ℤ) (M N : Submodule (𝓞 K) V) (β : FinPl K → ℝ), M.FG → M ≠ ⊥ →
      N ≤ Formalism.HermitianLatticesTheory.idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
        Submodule (𝓞 K) K) M →
      rkK N = rkK M →
      (∀ w : FinPl K, ((lenAt w (Formalism.HermitianLatticesTheory.idealSmul
        ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M)
          N).toNat : ℝ) = (rkK M : ℝ) * β w) →
      (∀ w : FinPl K, lenAt w (Formalism.HermitianLatticesTheory.idealSmul
        ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M) N ≠ ⊤) ∧
      (Function.support β).Finite ∧
      muMaxDef b X (modLat σ N) ≤ muMaxDef b X M + sgSum σ τ ∧
      muDef b X (modLat σ N) = muDef b X M + sgSum σ τ - ∑ᶠ w : FinPl K, 2 * ell w * β w
abbrev Rloc {K : Type} [Field K] [NumberField K] (w : FinPl K) : Type :=
  @Localization.AtPrime (𝓞 K) _ w.1 w.2.isPrime
def locScal {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (w : FinPl K) [Module (Rloc w) V] (c : K) (L : Submodule (𝓞 K) V) :
    Submodule (Rloc w) V :=
  Submodule.span (Rloc w) ((fun x : V => c • x) '' (L : Set V))
def SlopeRelationsLocal : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    [∀ w : FinPl K, Module (Rloc w) V] [∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (ϖ : FinPl K → 𝓞 K), (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) →
    ∀ (σ τ : FinPl K →₀ ℤ) (M N N' : Submodule (𝓞 K) V) (β : FinPl K → ℝ), M.FG → M ≠ ⊥ →
      rkK N = rkK M →
      (∀ w, locScal w 1 N ≤ locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M) →
      (∀ w, locScal w 1 N' = locScal w (algebraMap (𝓞 K) K (ϖ w) ^ (-σ w)) N) →
      (∀ w, ((Module.length (Rloc w) (locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M ⧸
        (locScal w 1 N).comap (locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M).subtype)).toNat : ℝ) =
          (rkK M : ℝ) * β w) →
      (∀ w, Module.length (Rloc w) (locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M ⧸
        (locScal w 1 N).comap (locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M).subtype) ≠ ⊤) ∧
      (Function.support β).Finite ∧
      muMaxDef b X N' ≤ muMaxDef b X M + sgSum σ τ ∧
      muDef b X N' = muDef b X M + sgSum σ τ - ∑ᶠ w : FinPl K, 2 * ell w * β w
def SlopesHypothesisFinitePlaces : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (J : Type)
    (V ι : J → Type) [∀ u, AddCommGroup (V u)] [∀ u, Module K (V u)] [∀ u, Module (𝓞 K) (V u)]
    [∀ u, IsScalarTower (𝓞 K) K (V u)] [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)]
    (b : ∀ u, Basis (ι u) K (V u)) (X : ∀ u, InfinitePlace K → Matrix (ι u) (ι u) ℂ),
    (∀ u v, IsUnit (X u v).det) →
    ∀ (σ τ : J → FinPl K →₀ ℤ) (M N : ∀ u, Submodule (𝓞 K) (V u)) (β : J → FinPl K → ℝ)
      (Sg0 : ℝ) (dr : J → ℝ),
      (∀ u, (M u).FG) → (∀ u, M u ≠ ⊥) →
      (∀ u, N u ≤ Formalism.HermitianLatticesTheory.idealSmul
        ((idealPow (τ u) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M u)) →
      (∀ u, rkK (N u) = rkK (M u)) →
      (∀ u (w : FinPl K), ((lenAt w (Formalism.HermitianLatticesTheory.idealSmul
        ((idealPow (τ u) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M u))
          (N u)).toNat : ℝ) = (rkK (M u) : ℝ) * β u w) →
      (∀ u, sgSum (σ u) (τ u) = Sg0 - dr u) →
      Formalism.LFunctionChainParameters.WeightedMeanLemmas.Slopes2 (fun u => muMaxDef (b u) (X u) (modLat (σ u) (N u)))
        (fun u => muDef (b u) (X u) (modLat (σ u) (N u))) (fun u => muMaxDef (b u) (X u) (M u))
        (fun u => muDef (b u) (X u) (M u)) dr (fun u => ∑ᶠ w : FinPl K, 2 * ell w * β u w) Sg0
def LemmaUFinitePlaceFamily : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (J : Type) [Fintype J]
    [Nonempty J]
    (V ι : J → Type) [∀ u, AddCommGroup (V u)] [∀ u, Module K (V u)] [∀ u, Module (𝓞 K) (V u)]
    [∀ u, IsScalarTower (𝓞 K) K (V u)] [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)]
    (b : ∀ u, Basis (ι u) K (V u)) (X : ∀ u, InfinitePlace K → Matrix (ι u) (ι u) ℂ),
    (∀ u v, IsUnit (X u v).det) →
    ∀ (σ τ : J → FinPl K →₀ ℤ) (M N : ∀ u, Submodule (𝓞 K) (V u)) (β : J → FinPl K → ℝ)
      (Sg0 : ℝ) (dr h : J → ℝ),
      (∀ u, (M u).FG) → (∀ u, M u ≠ ⊥) →
      (∀ u, N u ≤ Formalism.HermitianLatticesTheory.idealSmul
        ((idealPow (τ u) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M u)) →
      (∀ u, rkK (N u) = rkK (M u)) →
      (∀ u (w : FinPl K), ((lenAt w (Formalism.HermitianLatticesTheory.idealSmul
        ((idealPow (τ u) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M u))
          (N u)).toNat : ℝ) = (rkK (M u) : ℝ) * β u w) →
      (∀ u, sgSum (σ u) (τ u) = Sg0 - dr u) → (∀ u, 0 ≤ dr u) →
      Formalism.LFunctionChainParameters.WeightedMeanLemmas.uF (fun u => (rkK (M u) : ℝ))
                (fun u => muMaxDef (b u) (X u) (modLat (σ u) (N u)))
                (fun u => muDef (b u) (X u) (modLat (σ u) (N u))) h ≤
        Formalism.LFunctionChainParameters.WeightedMeanLemmas.rhsU (fun u => (rkK (M u) : ℝ)) (fun u => muMaxDef (b u) (X u) (M u))
          (fun u => muDef (b u) (X u) (M u)) h dr (fun u => ∑ᶠ w : FinPl K, 2 * ell w * β u w)
end Formalism.LFunctionChainParameters.slopeLatticeData


