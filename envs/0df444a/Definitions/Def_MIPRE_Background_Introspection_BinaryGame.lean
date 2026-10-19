-- Prove2me | Definitions.Def_MIPRE_Background_Introspection_BinaryGame
-- name    : MIPRE_Background_Introspection_BinaryGame
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:22:52.55189+00:00
-- url     : https://prove2.me/theorems/ff5145d4-3751-46fd-a3fc-ab6b01432db8
-- title:
--   Definitions of BinaryGame: Perfect PCC completeness of the concrete full typed introspection game The sampler is the twenty-six-type Pauli CL…
-- statement:
--   The definitions of the module `MIPRE.Background.Introspection.BinaryGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Perfect PCC completeness of the concrete full typed introspection game. The sampler is the twenty-six-type Pauli CL presentation, with all auxiliary vertices, and the predicate is the actual parsed introspection predicate with the QLD decider. A perfect original PCC strategy gives a perfect PCC strategy on the common seed register tensor the original auxiliary space tensor one qubit. Original CL seeds are arbitrary binary CL functions on the full qubit register; no executable compiler or arbitrary seed-padding claim is made here.
--
--   **Definitions** (6): `MIPRE.Introspection.BinaryComplete.Question`; `MIPRE.Introspection.BinaryComplete.game`; `MIPRE.Introspection.BinaryComplete.op`; `MIPRE.Introspection.BinaryComplete.pauliCheck`; `MIPRE.Introspection.BinaryComplete.query`; `MIPRE.Introspection.BinaryComplete.strategy` (The actual common-carrier strategy for the complete typed game.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `op_isPVM`, `doubled_positive`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Introspection.BinaryGame` (`MIPRE/Background/Introspection/BinaryGame.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 119 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/BinaryGame.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/BinaryGame.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsedHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCompleteAux
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HonestSampling
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryMeasurements
import Definitions.Def_MIPRE_Background_Introspection_BinaryAnchors
import Definitions.Def_MIPRE_Background_Introspection_BinarySampled
import Theorems.Thm_MIPRE_tracialValue_eq_one_of_re_eq_zero
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_auxOp_isPVM
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_pauliOp_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM

/-! # Perfect PCC completeness of the concrete full typed introspection game

The sampler is the twenty-six-type Pauli CL presentation, with all auxiliary
vertices, and the predicate is the actual parsed introspection predicate with
the QLD decider. A perfect original PCC strategy gives a perfect PCC strategy
on the common seed register tensor the original auxiliary space tensor one
qubit. Original CL seeds are arbitrary binary CL functions on the full qubit register; no executable
compiler or arbitrary seed-padding claim is made here.
-/

noncomputable section
namespace MIPRE.Introspection.BinaryComplete
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)

abbrev Question (m t ℓ : ℕ) :=
  CL.Detyping.Question (QuestionType QLD.Ty ℓ) (Fin ((3*m+3)*t))

def pauliCheck (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (p q : QLD.Ty) (x y : Fin ((3*m+3)*t) → ZMod 2) :
    QLD.Answer F m d → QLD.Answer F m d → Bool :=
  QLD.accepts hm (QLD.PauliCL.binaryQuestion b p x) (QLD.PauliCL.binaryQuestion b q y)

def game (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F) :=
  TypedEstimates.parsedGame QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.binaryPresentation hm b) L (project (d := d) b) D (pauliCheck hm b)

def query (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (p : QuestionType QLD.Ty ℓ) (c : QLD.Content F m) : Question m t ℓ :=
  (p, (TypedPresentation.family (QLD.PauliCL.binaryPresentation hm b) p).eval
    (QLD.PauliCL.binaryVectorEquiv b (QLD.PauliCL.contentVector c)))

variable (R : SyncStrategy (Honest.sourceGame L D).doubled)

def op (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (q : Question m t ℓ) :
    Answer F A m t d → Matrix (Space L D R) (Space L D R) ℂ :=
  match q.1 with
  | .inl p => pauliOp b L D R hm (QLD.PauliCL.binaryQuestion b p q.2)
  | .inr p => auxOp L D R hL p

theorem op_isPVM (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (q : Question m t ℓ) :
    IsPVM (op (d := d) L D R hm b hL q) := by
  rcases q with ⟨q,x⟩
  cases q with
  | inl p => exact pauliOp_isPVM b L D R hm _
  | inr p => exact auxOp_isPVM L D R hL p

/-- The actual common-carrier strategy for the complete typed game. -/
def strategy (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) : SyncStrategy (game (d := d) L D hm b).doubled where
  d := Fintype.card (Space L D R)
  d_pos := by
    let : Nonempty (Fin R.d) := Fin.pos_iff_nonempty.mp R.d_pos
    exact Fintype.card_pos
  P :=
    { M := fun q a => registerOp (Fintype.equivFin (Space L D R)).symm (op L D R hm b hL q.2 a)
      selfAdjoint := fun q a => by
        rw [Matrix.star_eq_conjTranspose]
        exact (registerOp_isPVM _ (op_isPVM L D R hm b hL q.2)).isSelfAdjoint a
      projective := fun q a => (registerOp_isPVM _ (op_isPVM L D R hm b hL q.2)).idem a
      normalized := fun q => (registerOp_isPVM _ (op_isPVM L D R hm b hL q.2)).sum_eq_one }

theorem doubled_positive (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (p q : Bool × Question m t ℓ)
    (h : 0 < (game (d := d) L D hm b).doubled.μ p q) :
    (p.1 = false ∧ q.1 = true) ∧ 0 < (game (d := d) L D hm b).μ p.2 q.2 := by
  have ht : p.1 = false ∧ q.1 = true := by
    by_contra hn
    simp only [Game.doubled_μ, if_neg hn] at h
    exact (lt_irrefl 0 h).elim
  exact ⟨ht,by simpa only [Game.doubled_μ, if_pos ht] using h⟩

end MIPRE.Introspection.BinaryComplete
end


