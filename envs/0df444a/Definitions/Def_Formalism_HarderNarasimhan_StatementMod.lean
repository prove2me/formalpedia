-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_StatementMod
-- name    : Formalism_HarderNarasimhan_StatementMod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:20.665325+00:00
-- url     : https://prove2.me/theorems/501074f2-6746-490b-8238-302bd8ae8ba7
-- title:
--   Statement Mod
-- statement:
--   Definitions and structural lemmas for Statement Mod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/StatementMod.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
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
namespace Formalism.HN
def IdealScale : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I ≠ 0 →
    ∀ M : Submodule (𝓞 K) V, M.FG → M ≠ ⊥ →
      (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M).FG ∧
      muDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muMaxDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muMaxDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muMinDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muMinDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)
def IndexMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ M N : Submodule (𝓞 K) V, M.FG → N ≤ M → N ≠ ⊥ → rkK N = rkK M →
      muDef b X N = muDef b X M -
        2 * Real.log (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) /
          ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) ∧
      muMaxDef b X N ≤ muMaxDef b X M
def CutLattice : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I ≠ 0 →
    ∀ M N' : Submodule (𝓞 K) V, M.FG → M ≠ ⊥ → N' ≤ Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M →
      N' ≠ ⊥ → rkK N' = rkK M →
      muMaxDef b X N' ≤ muMaxDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muDef b X N' = muDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) -
        2 * Real.log (N'.toAddSubgroup.relIndex
          (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M).toAddSubgroup : ℝ) /
          ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ))
def LcvFormula : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V) (M : Submodule (𝓞 K) V), LinearIndependent K e → M.FG → M ≠ ⊥ →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e) →
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M)).Finite ∧
      muDef b X M = -((1 / (nPl K : ℝ)) * ∑ v, Real.log (gramPl b X v e).det.re +
        2 * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
          (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
            (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ))) /
        (rkK M : ℝ)
end Formalism.HN


