-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:09.578649+00:00
-- url     : https://prove2.me/theorems/e1f553d6-1738-493b-8721-1f058a00c93b
-- title:
--   List Map Sum Apply
-- statement:
--   Definitions and structural lemmas for List Map Sum Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_HilbertSchmidtVectorization_adjH_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def TermClause (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ T ∈ Θ, ∃ (P : Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (c : ℕ)
      (es : List (Fin nf × List (Mat k r))), U.IsPolyDeg κ P ∧
      (∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) ∧
      ∀ g ∈ C6.domL D L, T.coef g = (P g * C6.monoM D a b c g) • C6.Epart fib es g
section mk
variable [FiniteDimensional ℂ Wp]
open Classical in

def mkTerm (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (e : CT k r nf × List (Mat k r)) : DTerm k r Wp Wq where
  coef := cv D fib e.1
  coefAdj := fun x => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH (cv D fib e.1 x)
  word := if ∀ X ∈ e.2, inLie k r X then e.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := fun x A B => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH_spec _ A B
end mk
def compFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (L₁ L₂ : FS k r nf) : FS k r nf :=
  L₁.flatMap fun e₁ => (steps D e₁.2 L₂).map fun e => (mulCT e₁.1 e.1, e.2)
end Formalism.FourierDecayAlt.P.MinorPolynomials


