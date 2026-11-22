-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_JointCSlopeExists
-- name    : Formalism_SizeWindowBrackets_JointCSlopeExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:01:17.201906+00:00
-- url     : https://prove2.me/theorems/c66156d6-4014-474b-844c-340c449d11f7
-- title:
--   Joint CSlope Exists
-- statement:
--   Definitions and structural lemmas for Joint CSlope Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/JointCSlopeExists.lean

import Definitions.Def_Formalism_SizeWindowBrackets_CutFailsForRSubmodule
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Pointwise
noncomputable section
namespace Formalism.LFunctionChainParameters.LJC
open Formalism.HN Formalism.LFunctionChainParameters.slopeLatticeData Formalism.LFunctionChainParameters.DiagonalSublatticeLength
section Str
variable {K : Type} [Field K] [NumberField K]
def rlocToK (w : FinPl K) : Rloc w →+* K :=
  haveI := w.2.isPrime
  IsLocalization.lift (M := w.1.primeCompl) (S := Rloc w) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ fun h0 => y.2 ?_
    have : (y : 𝓞 K) = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0)
    rw [this]; exact Ideal.zero_mem _)
@[reducible] def rlocAlgebra (w : FinPl K) : Algebra (Rloc w) K := (rlocToK w).toAlgebra
@[reducible] def rlocModule (w : FinPl K) (V : Type) [AddCommGroup V] [Module K V] : Module (Rloc w) V :=
  Module.compHom V (rlocToK w)
end Str
def RlocDVR : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : FinPl K),
    IsDiscreteValuationRing (Rloc w) ∧
    (∀ ϖ : 𝓞 K, ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 → Irreducible (algebraMap (𝓞 K) (Rloc w) ϖ)) ∧
    ∀ [Algebra (Rloc w) K] [IsScalarTower (𝓞 K) (Rloc w) K], IsFractionRing (Rloc w) K
def RlocStr : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : FinPl K),
    letI := rlocAlgebra w
    letI := rlocModule w V
    IsScalarTower (𝓞 K) (Rloc w) K ∧ IsScalarTower (𝓞 K) (Rloc w) V ∧ IsScalarTower (Rloc w) K V
def RlocUnique : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : FinPl K) [Module (Rloc w) V] [IsScalarTower (𝓞 K) (Rloc w) V]
    (r : Rloc w) (x : V), r • x = rlocToK w r • x
section Defs
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
def SmithLoc (w : FinPl K) [Module (Rloc w) V] (ϖ : 𝓞 K) (M N : Submodule (𝓞 K) V) {d : ℕ}
    (e : Fin d → ℕ) : Prop :=
  ∃ c : Basis (Fin d) (Rloc w) (Submodule.span (Rloc w) (M : Set V)),
    Submodule.span (Rloc w) (N : Set V) =
      Submodule.span (Rloc w) (Set.range fun i => ϖ ^ e i • (c i : V))
def SmithAt (w : FinPl K) (ϖ : 𝓞 K) (M N : Submodule (𝓞 K) V) {d : ℕ} (e : Fin d → ℕ) : Prop :=
  letI := rlocModule w V
  SmithLoc w ϖ M N e
def idl (τ : FinPl K →₀ ℤ) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Formalism.HermitianLatticesTheory.idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) L
def cutG [IsScalarTower (𝓞 K) K V] (τ : FinPl K →₀ ℤ) (M N : Submodule (𝓞 K) V)
    (V' : Submodule K V) : Submodule (𝓞 K) V :=
  N ⊓ idl τ M ⊓ V'.restrictScalars (𝓞 K)
def posSum {d : ℕ} (e : Fin d → ℕ) (t : ℤ) : ℕ := ∑ i, ((e i : ℤ) - t).toNat
end Defs
def SmithAtIff : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : FinPl K) [Module (Rloc w) V] [IsScalarTower (𝓞 K) (Rloc w) V]
    (ϖ : 𝓞 K) (M N : Submodule (𝓞 K) V) (d : ℕ) (e : Fin d → ℕ),
    SmithLoc w ϖ M N e ↔ SmithAt w ϖ M N e
def SmithExistsDVR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Type) [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (d : ℕ) (M : Submodule R W) (_ : Basis (Fin d) R M) (N : Submodule R W), N ≤ M →
    Submodule.span K (M : Set W) ≤ Submodule.span K (N : Set W) →
    ∃ (b : Basis (Fin d) R M) (e : Fin d → ℕ),
      N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W))
def SmithExists : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (w : FinPl K) (ϖ : 𝓞 K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 →
    ∀ (M N : Submodule (𝓞 K) V), M.FG → Submodule.span K (M : Set V) = ⊤ → N ≤ M →
      Submodule.span K (N : Set V) = ⊤ →
      ∃ e : Fin (finrank K V) → ℕ, SmithAt w ϖ M N e
def SmithLen : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : FinPl K) (ϖ : 𝓞 K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 →
    ∀ (M N : Submodule (𝓞 K) V) (d : ℕ) (e : Fin d → ℕ), SmithAt w ϖ M N e →
      lenAt w M N = ((∑ i, e i : ℕ) : ℕ∞) ∧ d = rkK M ∧ rkK N = rkK M
def CutGlobal : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (τ : FinPl K →₀ ℤ) (M N : Submodule (𝓞 K) V) (V' : Submodule K V),
    idl τ M ⊓ V'.restrictScalars (𝓞 K) = idl τ (latV M V') ∧ cutG τ M N V' ≤ idl τ (latV M V')
def CutLocal : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : FinPl K) [Algebra (Rloc w) K] [IsScalarTower (𝓞 K) (Rloc w) K]
    [Module (Rloc w) V] [IsScalarTower (𝓞 K) (Rloc w) V] [IsScalarTower (Rloc w) K V]
    (ϖ : 𝓞 K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 → ∀ (τ : FinPl K →₀ ℤ), 0 ≤ τ w →
    ∀ (M N : Submodule (𝓞 K) V) (V' : Submodule K V),
      Submodule.span (Rloc w) ((latV M V' : Submodule (𝓞 K) V) : Set V) =
        latV (Submodule.span (Rloc w) (M : Set V)) V' ∧
      Submodule.span (Rloc w) ((idl τ (latV M V') : Submodule (𝓞 K) V) : Set V) =
        algebraMap (𝓞 K) (Rloc w) ϖ ^ (τ w).toNat • latV (Submodule.span (Rloc w) (M : Set V)) V' ∧
      Submodule.span (Rloc w) ((cutG τ M N V' : Submodule (𝓞 K) V) : Set V) =
        cutN (algebraMap (𝓞 K) (Rloc w) ϖ) (τ w).toNat (Submodule.span (Rloc w) (M : Set V))
          (Submodule.span (Rloc w) (N : Set V)) V'
def CutRank : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (τ : FinPl K →₀ ℤ) (M N : Submodule (𝓞 K) V) (V' : Submodule K V),
    Submodule.span K (M : Set V) = ⊤ → Submodule.span K (N : Set V) = ⊤ →
    Submodule.span K ((latV M V' : Submodule (𝓞 K) V) : Set V) = V' ∧
    Submodule.span K ((cutG τ M N V' : Submodule (𝓞 K) V) : Set V) = V'
def JointC : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (w : FinPl K) (ϖ : 𝓞 K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 →
    ∀ (τ : FinPl K →₀ ℤ), 0 ≤ τ w → ∀ (M N : Submodule (𝓞 K) V), Submodule.span K (M : Set V) = ⊤ →
    ∀ (d : ℕ) (e : Fin d → ℕ), SmithAt w ϖ M N e → ∀ V' : Submodule K V,
      cutG τ M N V' ≤ idl τ (latV M V') ∧
      lenAt w (idl τ (latV M V')) (cutG τ M N V') ≤ (posSum e (τ w) : ℕ∞)
def JointCEq : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : FinPl K) (ϖ : 𝓞 K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 →
    ∀ (τ : FinPl K →₀ ℤ), 0 ≤ τ w → ∀ (M N : Submodule (𝓞 K) V) (d : ℕ) (e : Fin d → ℕ),
      SmithAt w ϖ M N e →
      lenAt w (idl τ (latV M (⊤ : Submodule K V))) (cutG τ M N ⊤) = (posSum e (τ w) : ℕ∞)
def JointCLen : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (w : FinPl K) (ϖ : 𝓞 K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 →
    ∀ (τ : FinPl K →₀ ℤ), 0 ≤ τ w → ∀ (M N : Submodule (𝓞 K) V), Submodule.span K (M : Set V) = ⊤ →
    ∀ (d : ℕ) (e : Fin d → ℕ), SmithAt w ϖ M N e → ∀ V' : Submodule K V,
      lenAt w (latV M V') (cutG τ M N V') =
        lenAt w (idl τ (latV M V')) (cutG τ M N V') + ((finrank K V' * (τ w).toNat : ℕ) : ℕ∞) ∧
      lenAt w (latV M V') (cutG τ M N V') ≤
        ((finrank K V' * (τ w).toNat + posSum e (τ w) : ℕ) : ℕ∞)
def JointCSlope : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (ϖ : FinPl K → 𝓞 K), (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) →
    ∀ (σ τ : FinPl K →₀ ℤ), (∀ w, 0 ≤ τ w) → ∀ (M N : Submodule (𝓞 K) V), M.FG →
      Submodule.span K (M : Set V) = ⊤ → N ≤ M →
    ∀ (d : ℕ) (e : FinPl K → Fin d → ℕ), (∀ w, SmithAt w (ϖ w) M N (e w)) →
    ∀ V' : Submodule K V, V' ≠ ⊥ →
      (Function.support fun w : FinPl K => posSum (e w) (τ w)).Finite ∧
      muMaxDef b X (modLat σ (cutG τ M N V')) ≤ muMaxDef b X (latV M V') + sgSum σ τ ∧
      muDef b X (latV M V') + sgSum σ τ
          - ∑ᶠ w : FinPl K, 2 * ell w * ((posSum (e w) (τ w) : ℝ) / (finrank K V' : ℝ)) ≤
        muDef b X (modLat σ (cutG τ M N V'))
def JointCSlopeExists : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (σ τ : FinPl K →₀ ℤ), (∀ w, 0 ≤ τ w) → ∀ (M N : Submodule (𝓞 K) V), M.FG →
      Submodule.span K (M : Set V) = ⊤ → N ≤ M → Submodule.span K (N : Set V) = ⊤ →
    ∀ V' : Submodule K V, V' ≠ ⊥ →
    ∃ (ϖ : FinPl K → 𝓞 K) (e : FinPl K → Fin (finrank K V) → ℕ),
      (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) ∧ (∀ w, SmithAt w (ϖ w) M N (e w)) ∧
      (∀ w, lenAt w M N = ((∑ i, e w i : ℕ) : ℕ∞)) ∧
      (Function.support fun w : FinPl K => posSum (e w) (τ w)).Finite ∧
      muMaxDef b X (modLat σ (cutG τ M N V')) ≤ muMaxDef b X (latV M V') + sgSum σ τ ∧
      muDef b X (latV M V') + sgSum σ τ
          - ∑ᶠ w : FinPl K, 2 * ell w * ((posSum (e w) (τ w) : ℝ) / (finrank K V' : ℝ)) ≤
        muDef b X (modLat σ (cutG τ M N V'))
def JointCSlopeLocal : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    [∀ w : FinPl K, Algebra (Rloc w) K] [∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) K]
    [∀ w : FinPl K, Module (Rloc w) V] [∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V]
    [∀ w : FinPl K, IsScalarTower (Rloc w) K V]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (ϖ : FinPl K → 𝓞 K), (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) →
    ∀ (σ τ : FinPl K →₀ ℤ), (∀ w, 0 ≤ τ w) → ∀ (M N Ns N' : Submodule (𝓞 K) V), M.FG →
      Submodule.span K (M : Set V) = ⊤ →
    ∀ (d : ℕ) (e : FinPl K → Fin d → ℕ), (∀ w, SmithLoc w (ϖ w) M N (e w)) →
    ∀ V' : Submodule K V, V' ≠ ⊥ →
      (∀ w, Submodule.span (Rloc w) (Ns : Set V) =
        cutN (algebraMap (𝓞 K) (Rloc w) (ϖ w)) (τ w).toNat (Submodule.span (Rloc w) (M : Set V))
          (Submodule.span (Rloc w) (N : Set V)) V') →
      (∀ w, locScal w 1 N' = locScal w (algebraMap (𝓞 K) K (ϖ w) ^ (-σ w)) Ns) →
      (Function.support fun w : FinPl K => posSum (e w) (τ w)).Finite ∧
      muMaxDef b X N' ≤ muMaxDef b X (latV M V') + sgSum σ τ ∧
      muDef b X (latV M V') + sgSum σ τ
          - ∑ᶠ w : FinPl K, 2 * ell w * ((posSum (e w) (τ w) : ℝ) / (finrank K V' : ℝ)) ≤
        muDef b X N'
def JointCIndex : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (w : FinPl K) (ϖ : 𝓞 K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 →
    ∀ (τ : FinPl K →₀ ℤ), 0 ≤ τ w → ∀ (M N : Submodule (𝓞 K) V), Submodule.span K (M : Set V) = ⊤ →
    ∀ (d : ℕ) (e : Fin d → ℕ), SmithAt w ϖ M N e → ∀ (V' : Submodule K V) (eR io len : ℝ), 0 < eR →
      len = (((lenAt w (idl τ (latV M V')) (cutG τ M N V')).toNat : ℝ)
        + (finrank K V' : ℝ) * (τ w : ℝ)) / eR →
      len ≤ (finrank K V' : ℝ) * ((τ w : ℝ) / eR) + (posSum e (τ w) : ℝ) / eR ∧
      ((posSum e (τ w) : ℝ) ≤ (finrank K V : ℝ) * eR * io →
        len ≤ (finrank K V' : ℝ) * ((τ w : ℝ) / eR) + (finrank K V : ℝ) * io ∧
        len ≤ (finrank K V : ℝ) * ((τ w : ℝ) / eR + io))
def JointCPrim : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (ϖ : FinPl K → 𝓞 K), (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) →
    ∀ (σ τ : FinPl K →₀ ℤ), (∀ w, 0 ≤ τ w) → ∀ (M N : Submodule (𝓞 K) V), M.FG →
      Submodule.span K (M : Set V) = ⊤ → N ≤ M →
    ∀ (d : ℕ) (e : FinPl K → Fin d → ℕ), (∀ w, SmithAt w (ϖ w) M N (e w)) →
    ∀ V' : Submodule K V, V' ≠ ⊥ →
    ∀ (S : Finset (FinPl K)) (eR l sg' tau len io : FinPl K → ℝ),
      (∀ w, w ∉ S → σ w = 0 ∧ τ w = 0 ∧ posSum (e w) (τ w) = 0) → (∀ w ∈ S, 0 < eR w) →
      (∀ w ∈ S, l w = ell w * eR w) → (∀ w ∈ S, sg' w = (σ w : ℝ) / eR w) →
      (∀ w ∈ S, tau w = (τ w : ℝ) / eR w) →
      (∀ w ∈ S, len w = (((lenAt w (idl τ (latV M V')) (cutG τ M N V')).toNat : ℝ)
        + (finrank K V' : ℝ) * (τ w : ℝ)) / eR w) →
      (∀ w ∈ S, (posSum (e w) (τ w) : ℝ) ≤ (finrank K V : ℝ) * eR w * io w) →
      (∀ w ∈ S, len w ≤ (finrank K V : ℝ) * (tau w + io w)) ∧
      muMaxDef b X (modLat σ (cutG τ M N V')) ≤ muMaxDef b X (latV M V') + UnitWeightPartition.Sg S l sg' tau ∧
      muDef b X (modLat σ (cutG τ M N V')) = muDef b X (latV M V') + UnitWeightPartition.Sg S l sg' tau
        - UnitWeightPartition.BeSum S l (finrank K V' : ℝ) len tau ∧
      UnitWeightPartition.BeSum S l (finrank K V' : ℝ) len tau ≤
        (finrank K V : ℝ) / (finrank K V' : ℝ) * UnitWeightPartition.IO S l io
def JointCFam : Prop :=
  ∀ (I : Type) (m : ℕ) (F : LChain2.Fam I m) (u : I) (j : F.V u →ₗ[F.K] F.Vf u),
    Function.Injective j → ∀ P : Submodule (𝓞 F.K) (F.Vf u),
    (F.M u).map (j.restrictScalars (𝓞 F.K)) = latV (F.Mf u) (LinearMap.range j) →
    (F.N0 u).map (j.restrictScalars (𝓞 F.K)) = cutG F.τ (F.Mf u) P (LinearMap.range j) →
    Submodule.span F.K (F.Mf u : Set (F.Vf u)) = ⊤ →
    F.N0 u ≤ F.ItM u ∧
    (Submodule.span F.K (P : Set (F.Vf u)) = ⊤ → rkK (F.N0 u) = rkK (F.M u)) ∧
    ∀ (w : FinPl F.K) (ϖ : 𝓞 F.K), ϖ ∈ w.1 → ϖ ∉ w.1 ^ 2 → 0 ≤ F.τ w →
    ∀ (d : ℕ) (e : Fin d → ℕ), SmithAt w ϖ (F.Mf u) P e →
      F.lenN u w ≤ posSum e (F.τ w) ∧
      ((posSum e (F.τ w) : ℝ) ≤ F.dM u * LChain2.ramE w * F.iop (LChain2.prBelow w) →
        F.lenR u w ≤ F.du u * F.tauR w + F.dM u * F.iop (LChain2.prBelow w) ∧
        F.lenR u w ≤ F.dM u * (F.tauR w + F.iop (LChain2.prBelow w)))
section Real
variable {ι κ : Type*} [DecidableEq ι]
def HypLowC (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ 0 < dM ∧ 0 ≤ de ∧ de < 1 ∧ du = (1 - de) * dM ∧ WT ⊆ W ∧
  (∀ w ∈ WT, tau w = 0) ∧ (∀ w ∈ W, 0 ≤ io w) ∧
  (∀ w ∈ W \ WT, len w ≤ du * tau w + dM * io w) ∧
  ∑ w ∈ WT, 2 * l w * len w / du ≤ PT ∧
  ∑ w ∈ W, 2 * l w * (UnitWeightPartition.sgw J gain F E w - sg' w) ≤ Rd ∧
  muN = muMu + UnitWeightPartition.Sg W l sg' tau - UnitWeightPartition.BeSum W l du len tau
def ClaimLowC (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  HypLowC W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd →
  muMu + UnitWeightPartition.Ga W J l gain tau + UnitWeightPartition.Fo W J l F - UnitWeightPartition.Ee W J l E - Rd - PT
      - UnitWeightPartition.IO W l io / (1 - de) ≤ muN
def ClaimLowCExt (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) (f T muM IOp LT RX : ℝ) : Prop :=
  HypLowC W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd →
  muMu = muM - f * Real.log (T - 1) / (T - 2) → de ≤ 1 / 2 →
  f * Real.log (T - 1) / (T - 2) ≤ 1 → UnitWeightPartition.IO W l io = 2 * IOp → PT ≤ LT → Rd ≤ RX →
  muM + UnitWeightPartition.Ga W J l gain tau + UnitWeightPartition.Fo W J l F - UnitWeightPartition.Ee W J l E - (4 * IOp + LT + RX + 1) ≤ muN
end Real
end Formalism.LFunctionChainParameters.LJC


