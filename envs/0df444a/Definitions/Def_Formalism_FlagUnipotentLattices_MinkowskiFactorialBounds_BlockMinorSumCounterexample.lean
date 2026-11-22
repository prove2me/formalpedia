-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:50.937657+00:00
-- url     : https://prove2.me/theorems/adb600ee-00e3-4e1e-a899-15f3ada675fa
-- title:
--   Block Minor Sum Counterexample
-- statement:
--   Definitions and structural lemmas for Block Minor Sum Counterexample, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.P
section G0
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
end G0
section G1
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
end G1
section G2
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
end G2
section G3
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
noncomputable def infinitePlaceEmbedding (E : Type) [Field E] (x : E) : InfinitePlace E → ℂ := fun w => w.embedding x
noncomputable def idealRadius (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℝ :=
  (FractionalIdeal.absNorm aa : ℝ) ^ (1 / (2 * (Fintype.card (InfinitePlace E) : ℝ)))
end G3
section G4
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
def scalarPoint {E : Type} [Field E] (x : E) : Σ c : Composition (0 + 1), (Fin c.length → E) :=
  ⟨Composition.ones 1, fun _ => x⟩
end G4
section G5
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
end G5
section G6
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
noncomputable def boundPolynomial (r A' : ℕ) : MvPolynomial (Fin (r + 1) ⊕ Fin (r + 1)) NNReal :=
  (∏ l : Fin (r + 1), (1 + MvPolynomial.X (Sum.inl l) * MvPolynomial.X (Sum.inr l)) ^ 2) *
    (1 + MvPolynomial.X (Sum.inl (Fin.last r)) * MvPolynomial.X (Sum.inr (Fin.last r))) ^ A'
end G6
section G7
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal
end G7
section G8
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
noncomputable def lOneNorm {P : Type} (a : P →₀ ℂ) : ℝ := a.sum fun _ c => ‖c‖
end G8
section Compose
open Formalism.HermitianLatticeCounting.ExpansionTerms
end Compose
end Formalism.HermitianLatticeCounting.P


