-- Prove2me | Definitions.Def_MIPRE_Background_Introspection_PauliRestriction
-- name    : MIPRE_Background_Introspection_PauliRestriction
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:12:17.839312+00:00
-- url     : https://prove2.me/theorems/1017bab0-1abc-43ff-b0c9-9444a31df917
-- title:
--   Definitions of PauliRestriction: Actual Pauli strategies extracted by restricting introspection The strategy is built on exactly the original finite…
-- statement:
--   The definitions of the module `MIPRE.Background.Introspection.PauliRestriction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Actual Pauli strategies extracted by restricting introspection. The strategy is built on exactly the original finite registers and state. Outer malformed answers are completed at fixed answers; the binary CL strategy then pulls back to the actual QLD game along canonical encodings.
--
--   **Definitions** (6): `MIPRE.Introspection.PauliRestriction.alice`; `MIPRE.Introspection.PauliRestriction.binaryStrategy` (Restriction and answer completion preserve the actual original state.); `MIPRE.Introspection.PauliRestriction.bob`; `MIPRE.Introspection.PauliRestriction.fullGame`; `MIPRE.Introspection.PauliRestriction.pauliCheck`; `MIPRE.Introspection.PauliRestriction.strategy` (The actual QLD strategy obtained by canonical question pullback.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `alice_isPVM`, `bob_isPVM`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Introspection.PauliRestriction` (`MIPRE/Background/Introspection/PauliRestriction.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 77 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/PauliRestriction.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/PauliRestriction.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import Mathlib.FieldTheory.Finite.GaloisField
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
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Theorems.Thm_MIPRE_Introspection_completePauliPOVM_isPVM

/-! # Actual Pauli strategies extracted by restricting introspection

The strategy is built on exactly the original finite registers and state.
Outer malformed answers are completed at fixed answers; the binary CL
strategy then pulls back to the actual QLD game along canonical encodings.
-/

noncomputable section
namespace MIPRE.Introspection.PauliRestriction
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]

def pauliCheck (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (p q : QLD.Ty) (x y : Fin ((3*m+3)*t) → ZMod 2) :
    QLD.Answer F m d → QLD.Answer F m d → Bool :=
  QLD.accepts hm (QLD.PauliCL.binaryQuestion b p x) (QLD.PauliCL.binaryQuestion b q y)

def fullGame (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
    (D : (ι → F₀) → (ι → F₀) → A → A → Bool) :=
  TypedEstimates.parsedGame QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.binaryPresentation hm b) L project D (pauliCheck hm b)

variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))

def alice (a₀ : QLD.Answer F m d) (q : QLD.PauliCL.BinaryQuestion m t) :
    POVM (QLD.Answer F m d) (Fin S.dA) :=
  completePauliPOVM a₀ (S.PA.toPOVM (.inl q.1,q.2))

def bob (b₀ : QLD.Answer F m d) (q : QLD.PauliCL.BinaryQuestion m t) :
    POVM (QLD.Answer F m d) (Fin S.dB) :=
  completePauliPOVM b₀ (S.PB.toPOVM (.inl q.1,q.2))

theorem alice_isPVM (a₀ : QLD.Answer F m d) (q : QLD.PauliCL.BinaryQuestion m t) :
    IsPVM (fun a => ((alice hm b L project D S a₀ q).mats a).val) := by
  apply completePauliPOVM_isPVM
  exact ⟨S.PA.selfAdjoint _, S.PA.projective _, S.PA.normalized _⟩

theorem bob_isPVM (b₀ : QLD.Answer F m d) (q : QLD.PauliCL.BinaryQuestion m t) :
    IsPVM (fun a => ((bob hm b L project D S b₀ q).mats a).val) := by
  apply completePauliPOVM_isPVM
  exact ⟨S.PB.selfAdjoint _, S.PB.projective _, S.PB.normalized _⟩

/-- Restriction and answer completion preserve the actual original state. -/
def binaryStrategy (a₀ b₀ : QLD.Answer F m d) :
    TensorProductStrategy (QLD.PauliCL.binaryGame (d := d) hm b) where
  dA := S.dA
  dB := S.dB
  ψ := S.ψ
  ψ_unit := S.ψ_unit
  PA := ProjectiveMeasurement.ofIsPVM (alice hm b L project D S a₀)
    (alice_isPVM hm b L project D S a₀)
  PB := ProjectiveMeasurement.ofIsPVM (bob hm b L project D S b₀)
    (bob_isPVM hm b L project D S b₀)

/-- The actual QLD strategy obtained by canonical question pullback. -/
def strategy (a₀ b₀ : QLD.Answer F m d) : TensorProductStrategy (QLD.qldGame (d := d) hm) :=
  QLD.PauliCL.pullbackStrategy hm b (binaryStrategy hm b L project D S a₀ b₀)

end MIPRE.Introspection.PauliRestriction
end


