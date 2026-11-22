-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
-- name    : Formalism_SizeWindowBrackets_LcvBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:02.298817+00:00
-- url     : https://prove2.me/theorems/106a2bb0-d5e4-49ba-acfd-f51843d93982
-- title:
--   Lcv Base Change
-- statement:
--   Definitions and structural lemmas for Lcv Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/LcvBaseChange.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementMod
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
namespace Formalism.LFunctionChainParameters.LLcv
open Formalism.HN
section Defs
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
def lcvInf (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) {j : ℕ} (e : Fin j → V) : ℝ :=
  (1 / (nPl K : ℝ)) * ∑ v, Real.log (gramPl b X v e).det.re
def lcvFin {j : ℕ} (e : Fin j → V) (M : Submodule (𝓞 K) V) : ℝ :=
  2 * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
    (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
      (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ))
def lcv (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) {j : ℕ} (e : Fin j → V)
    (M : Submodule (𝓞 K) V) : ℝ :=
  lcvInf b X e + lcvFin e M
end Defs
def LcvMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V) (M : Submodule (𝓞 K) V), LinearIndependent K e → M.FG → M ≠ ⊥ →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e) →
      rkK M = j ∧ 0 < j ∧
      (∀ v, 0 < (gramPl b X v e).det.re ∧ (gramPl b X v e).det.im = 0) ∧
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M)).Finite ∧
      muDef b X M = -lcv b X e M / (rkK M : ℝ)
def LcvBasisFree : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j j' : ℕ) (e : Fin j → V) (e' : Fin j' → V) (M : Submodule (𝓞 K) V),
      LinearIndependent K e → LinearIndependent K e' → M.FG → M ≠ ⊥ →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e) →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e') →
      lcv b X e M = lcv b X e' M
def LcvBaseChange : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K) (M : Submodule (𝓞 K) V),
      LinearIndependent K e → IsUnit g.det → M.FG → M ≠ ⊥ →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e) →
      lcvInf b X (fun a => ∑ c, g c a • e c) = lcvInf b X e +
        2 / (Module.finrank ℚ K : ℝ) * Real.log |((Algebra.norm ℚ g.det : ℚ) : ℝ)| ∧
      lcvFin (fun a => ∑ c, g c a • e c) M = lcvFin e M -
        2 / (Module.finrank ℚ K : ℝ) * Real.log |((Algebra.norm ℚ g.det : ℚ) : ℝ)|
def LcvExists : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V),
    ∃ (j : ℕ) (e : Fin j → V), LinearIndependent K e ∧ (∀ a, e a ∈ M) ∧
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e)
def LcvFree : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V), LinearIndependent K e → 0 < j →
      lcvFin e (Submodule.span (𝓞 K) (Set.range e)) = 0 ∧
      muDef b X (Submodule.span (𝓞 K) (Set.range e)) = -lcvInf b X e / (j : ℝ)
def LcvIdeal : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (_b : Basis ι K V) (j : ℕ) (e : Fin j → V)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), LinearIndependent K e → 0 < j → I ≠ 0 →
      lcvFin e (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K)
        (Submodule.span (𝓞 K) (Set.range e))) =
        2 * (j : ℝ) * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)
def IndexLocLen : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 →
      (∀ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI := p.2.isPrime;
        Module.length (𝓞 K) ((Formalism.HermitianLatticesTheory.localization₂ p.1 A) ⧸
          (Formalism.HermitianLatticesTheory.localization₂ p.1 B).comap (Formalism.HermitianLatticesTheory.localization₂ p.1 A).subtype)) ≠ ⊤) ∧
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.locLen p.1 A B)).Finite ∧
      Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, Real.log (Ideal.absNorm p.1 : ℝ) *
          (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.locLen p.1 A B : ℝ))
end Formalism.LFunctionChainParameters.LLcv


