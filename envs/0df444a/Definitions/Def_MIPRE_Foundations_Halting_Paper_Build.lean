-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_Build
-- name    : MIPRE_Foundations_Halting_Paper_Build
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:15:44.865979+00:00
-- url     : https://prove2.me/theorems/d0b492c8-0c16-4b53-abe7-00685c5db4e4
-- title:
--   Building the decider $\mathcal{D}^{\mathrm{halt}}$ from $(M, \lambda)$ in polynomial time
-- statement:
--   The class verifier of the polynomial-time halting reduction must compute, from a machine $M$ and the parameter $\lambda = \Lambda_0 + 4|M|$, the description of the decider `dec M λ` of `Paper/Decider.lean`. That description is a fixed tree with the encodings of $M$ and $\lambda$ at two positions: `dec M λ = hardcode K (encode K)` for `K = kleeneProg U.univ F`, and the code of `F` holds `body`, $M$ and $\lambda$ as constants. Fix $G$, $U$, $UT$ and $S'$.
--
--   **The three shapes, on data.** `MIPRE.Halting.fcodeData bodyD MD lamD` is the description of `F.code` from the data of `body`, $M$ and $\lambda$; `kleeneData univD fD` the description of `kleeneProg univ F` from those of `univ` and `F.code`; `fixData kD` the description of `hardcode K (encode K)` from that of $K$.
--
--   **As polynomial-time functions.** `fcodeF bodyD : PolyTimeFun (Prog × ℕ) Data` computes `fcodeData bodyD p.1.toData (encode p.2)`; `kleeneF univD : PolyTimeFun Data Data` computes `kleeneData univD`; `fixF : PolyTimeFun Data Data` computes `fixData`; all three are assembled from `pair` and `const` and retyped with `PolyTimeFun.cast` (same encodings, different function). `decBuild G U UT S' : PolyTimeFun (Prog × ℕ) Prog` is their composite, cast to the decider:
--   $$\mathrm{decBuild}\;G\;U\;UT\;S'\;(M, \lambda) = \mathrm{dec}\;G\;U\;UT\;S'\;M\;\lambda .$$
--   `lamF Λ₀ : PolyTimeFun Prog ℕ` computes $M \mapsto \Lambda_0 + 4\,\mathrm{esize}\,M$ and `cutF K D : PolyTimeFun ℕ ℕ` computes $\lambda \mapsto 2^{K + D\cdot\mathrm{esize}\,\lambda}$, the answer cutoff the class decider applies before running the decider of $\mathcal{V}^{\mathrm{halt}}$.
--
--   The embedded lemmas are the three `toData` equations identifying `(F …).code.toData`, `(kleeneProg univ F).toData` and `(kleeneFix U F).toData` with the three shapes, the `@[simp]` application equations of `fcodeF`, `kleeneF`, `fixF`, `decBuild`, `lamF`, `cutF`, and `esize_bitStr_le` (a bit string of length $k$ encodes to at most $4k + 1$ nodes).
--
--   **Formalization Note**. The `toFun` of `decBuild` is literally `fun p => dec G U UT S' p.1 p.2`, so the class verifier can run the decider it computes without a separate correctness lemma. The cutoff is a power of two so that it can be computed from $|\lambda|$ in unary (`expBits`), and polynomial in $\lambda$ since $2^{|\lambda|} \le 32\lambda^4$ (module docstring). All `PolyTimeFun`s here are `noncomputable`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Build.lean; blueprint lem:lambda

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Build.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_LambdaBound
import Definitions.Def_MIPRE_Foundations_Halting_Absorb
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Size
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Cost
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Induction
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Stages

/-!
# Building the decider `𝒟^halt` from `(M, λ)`, in polynomial time

The class verifier of the polynomial-time halting reduction runs, on input `z`, the verifier
`𝒱^halt M λ` of `Paper/Decider.lean` for the machine `M = R z` at the parameter
`λ = Λ₀ + 4|M|`; so it must compute the description of `dec M λ` from `M` and `λ`. That
description is a fixed tree with `M`'s and `λ`'s encodings at two positions (`Paper/Size.lean`
computed its size): `dec M λ = hardcode K (encode K)` for `K = kleeneProg univ F`, and `F`'s
code holds `body`, `M` and `λ` as constants. `decBuild` assembles the tree with `pair` and
`const` over `Data` (`kleeneData`, `fcodeData`, `fixData` are the three shapes) and is a
`PolyTimeFun (Prog × ℕ) Prog`. Beside it, `lamF` computes the parameter `Λ₀ + 4|M|` and
`cutF K D` the answer cutoff `2 ^ (K + D · |λ|)` that the class decider applies before running
`𝒱^halt`'s decider — a power of two so that it can be computed from `|λ|` in unary
(`expBits`), and polynomial in `λ` since `2 ^ |λ| ≤ 32 λ ^ 4`.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.PolyTimeFun

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-! ## The three shapes -/

/-- The description of `F.code` from those of `body`, `M` and `λ`. -/
def fcodeData (bodyD MD lamD : Data) : Data :=
  .cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) bodyD) (.cons (.ofNat 2)
    (.cons (.cons (.ofNat 6) MD) (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) lamD)
      (.cons (.ofNat 0) (.ofNat 0)))))))) smnProg.toData)

theorem toData_F_code (S' M : Prog) (lam : ℕ) :
    (F G U UT S' M lam).code.toData =
      fcodeData (body G U UT S').toData M.toData (encode lam) := rfl

/-- The description of `kleeneProg univ F` from those of `univ` and `F.code`. -/
def kleeneData (univD fD : Data) : Data :=
  .cons (.ofNat 3) (.cons (.ofNat 0) (.cons (.cons (.ofNat 1) .nil) (.cons (.ofNat 4)
    (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 0) (.ofNat 0)) (.cons (.ofNat 0) (.ofNat 0))))
      (.cons (.ofNat 4) (.cons (.cons (.ofNat 4) (.cons (.cons (.ofNat 0) (.ofNat 0))
        smnProg.toData)) (.cons (.ofNat 4) (.cons (.cons (.ofNat 4) (.cons (.cons (.ofNat 0)
          (.ofNat 0)) fD)) (.cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 0)
            (.ofNat 0)) (.cons (.ofNat 0) (.ofNat 4)))) (.cons (.ofNat 4) (.cons (.cons (.ofNat 0)
              (.ofNat 0)) univD))))))))))))

theorem toData_kleeneProg (univ : Prog) (F : PolyTimeFun Prog Prog) :
    (kleeneProg univ F).toData = kleeneData univ.toData F.code.toData := rfl

/-- The description of `hardcode K (encode K)` from that of `K`. -/
def fixData (kD : Data) : Data :=
  .cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) kD) (.cons .nil .nil))) kD)

theorem toData_kleeneFix (F : PolyTimeFun Prog Prog) :
    (kleeneFix U F).toData = fixData (kleeneProg U.univ F).toData := rfl

/-! ## The shapes as polynomial-time functions -/

/-- `fcodeData bodyD` on `(M, λ)`, as nested pairs of `Data`. -/
noncomputable def fcodeF (bodyD : Data) : PolyTimeFun (Prog × ℕ) Data :=
  cast (pair (const (Data.ofNat 4)) (pair (pair (const (Data.ofNat 2))
    (pair (pair (const (Data.ofNat 6)) (const bodyD)) (pair (const (Data.ofNat 2))
      (pair (pair (const (Data.ofNat 6)) (progData.comp fst)) (pair (const (Data.ofNat 2))
        (pair (pair (const (Data.ofNat 6)) (natData.comp snd))
          (const (Data.cons (.ofNat 0) (.ofNat 0)))))))))
    (const smnProg.toData)))
    (fun p => fcodeData bodyD p.1.toData (encode p.2)) (fun _ => rfl)

@[simp] theorem fcodeF_apply (bodyD : Data) (p : Prog × ℕ) :
    fcodeF bodyD p = fcodeData bodyD p.1.toData (encode p.2) := rfl

/-- `kleeneData univD` on `fD`, as nested pairs of `Data`. -/
noncomputable def kleeneF (univD : Data) : PolyTimeFun Data Data :=
cast (pair (const (Data.ofNat 3)) (pair (const (Data.ofNat 0)) (pair (const (Data.cons (.ofNat
    1) .nil)) (pair (const (Data.ofNat 4)) (pair (const (Data.cons (.ofNat 2) (.cons (.cons
    (.ofNat 0) (.ofNat 0)) (.cons (.ofNat 0) (.ofNat 0))))) (pair (const (Data.ofNat 4)) (pair
    (const (Data.cons (.ofNat 4) (.cons (.cons (.ofNat 0) (.ofNat 0)) smnProg.toData))) (pair
    (const (Data.ofNat 4)) (pair (pair (const (Data.ofNat 4)) (pair (const (Data.cons (.ofNat 0)
    (.ofNat 0))) (id Data))) (pair (const (Data.ofNat 4)) (pair (const (Data.cons (.ofNat 2)
    (.cons (.cons (.ofNat 0) (.ofNat 0)) (.cons (.ofNat 0) (.ofNat 4))))) (const (Data.cons
    (.ofNat 4) (.cons (.cons (.ofNat 0) (.ofNat 0)) univD))))))))))))))
    (kleeneData univD) (fun _ => rfl)

@[simp] theorem kleeneF_apply (univD fD : Data) : kleeneF univD fD = kleeneData univD fD := rfl

/-- `fixData` on `kD`, as nested pairs of `Data`. -/
noncomputable def fixF : PolyTimeFun Data Data :=
  cast (pair (const (Data.ofNat 4)) (pair (pair (const (Data.ofNat 2))
    (pair (pair (const (Data.ofNat 6)) (id Data)) (const (Data.cons .nil .nil)))) (id Data)))
    fixData (fun _ => rfl)

@[simp] theorem fixF_apply (kD : Data) : fixF kD = fixData kD := rfl

/-- **The decider's description from `(M, λ)`**, in polynomial time. -/
noncomputable def decBuild (S' : Prog) : PolyTimeFun (Prog × ℕ) Prog :=
  cast (fixF.comp ((kleeneF U.univ.toData).comp (fcodeF (body G U UT S').toData)))
    (fun p => dec G U UT S' p.1 p.2) (fun p => by
      show (dec G U UT S' p.1 p.2).toData = _
      rw [dec, toData_kleeneFix, toData_kleeneProg, toData_F_code]
      rfl)

@[simp] theorem decBuild_apply (S' : Prog) (p : Prog × ℕ) :
    decBuild G U UT S' p = dec G U UT S' p.1 p.2 := rfl

/-! ## The parameter and the cutoff -/

/-- `M ↦ Λ₀ + 4|M|`: the size of `M` in unary, four copies, plus the constant, read in
binary. -/
noncomputable def lamF (Λ₀ : ℕ) : PolyTimeFun Prog ℕ :=
  addUnary.comp (pair (const Λ₀) ((unaryMul 4).comp (encodedSizeU Prog)))

@[simp] theorem lamF_apply (Λ₀ : ℕ) (M : Prog) : lamF Λ₀ M = Λ₀ + 4 * esize M := by
  show Λ₀ + (unaryMul 4 (unary (esize M))).length = _
  rw [unaryMul_apply]
  simp [unary]

/-- `λ ↦ 2 ^ (K + D · |λ|)`: the answer cutoff of the class decider. -/
noncomputable def cutF (K D : ℕ) : PolyTimeFun ℕ ℕ :=
  expBits.comp ((addConstU K).comp ((unaryMul D).comp (encodedSizeU ℕ)))

@[simp] theorem cutF_apply (K D lam : ℕ) : cutF K D lam = 2 ^ (K + D * esize lam) := by
  show 2 ^ (addConstU K (unaryMul D (unary (esize lam)))).length = _
  rw [unaryMul_apply, addConstU_apply]
  simp [unary]

/-- A bit string of length `k` encodes to at most `4k + 1` nodes. -/
theorem esize_bitStr_le (l : BitStr) : esize l ≤ 4 * l.length + 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [esize_bitStr_cons]
    have := Data.size_ofBool b
    simp only [List.length_cons]
    omega

end MIPRE.Halting


