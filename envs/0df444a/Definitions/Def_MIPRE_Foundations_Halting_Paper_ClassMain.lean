-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassMain
-- name    : MIPRE_Foundations_Halting_Paper_ClassMain
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:20:14.941057+00:00
-- url     : https://prove2.me/theorems/d79c298a-78c6-4e1f-96b1-922232fd6429
-- title:
--   The class verifier as a polynomial-time verifier: its polynomial, cutoff bound and question embedding
-- statement:
--   With the ambient data of the `ClassVerifier` bundle ($G$, $U$, $U_T$, $\Lambda_0$, $K$, $R$), this bundle packages `sampProg` and `decProg` into a `PolyVerifier` (blueprint `def:mipstar`) and defines what the computation of its game value on an input $z$ needs.
--
--   `cutB m` is the cutoff in the input length, $2^{K+\deg}(2\cdot\mathtt{lamB}\,m + 1)^{4\deg}$ with $\deg$ the degree of $G.\mathrm{bound}$, chosen to dominate `cutz z` at $m = |z|$. `classP` is the verifier's polynomial, the sum of the four polynomials `PolyBounded.poly` chooses for `sampB`, `dimB`, `decB`, `cutB`:
--
--   $$\mathtt{classP} = P_{\mathtt{sampB}} + P_{\mathtt{dimB}} + P_{\mathtt{decB}} + P_{\mathtt{cutB}}, \qquad \mathtt{classV} = \langle \mathtt{sampProg},\ \mathtt{decProg},\ \mathtt{classP} \rangle .$$
--
--   `classV` is that `PolyVerifier`: the two programs with their closedness proofs and `bound := classP`, so its answer-length bound on $z$ is $B(z) = \mathtt{classP}(|z|)$. `Vz z` is `Vpaper G U UT (R z) (lamz z)`, the level-$7$ verifier $\mathcal{V}^{\mathrm{halt}}(R(z),\lambda(z))$ played on $z$. `qEmb z` embeds the questions of `Vz z` at level $C$ ($\mathbb{F}_2$-vectors of the compressed sampler's dimension) into the strings of length at most $B(z)$, by `toBits`.
--
--   The embedded lemmas prove `PolyBounded` for each cost function (`lamB`, `dimB`, `T1B`, `R1B`, `UnB`, `T2B`, `R2B`, `T3B`, `R3B`, `sampB`, `TDB`, `zB`, `decB`, `cutB`, with `polyBounded_call` the common shape of the universal calls), `dimB m ≤ classP.eval m`, `dimz z ≤ classV.B z`, and that `qOf w z r` has length `dimz z`.
--
--   The source module proves this verifier efficient (`classV_efficient`) and computes its game value (`classV_value`), giving `re_subset_mipstar_of` and `mipstar_eq_re_of` (blueprint `thm:mipstar-eq-re`, for the paper's class) from a compressor and two universal machines.
--
--   **Formalization Note** `PolyBounded f` is `∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n` and `PolyBounded.poly` its chosen witness, so `classP` is noncomputable. `classV.B z` unfolds to `classP.eval z.length`. `Vz` is an `abbrev`. `qEmb z : (Vz z).Questions C ↪ Answers (classV.B z)`, with `Answers T` the subtype of bit strings of length at most `T`; its injectivity is `ofBits_toBits`. `classV_efficient`, `classV_questions`, `seedCount_eq`, `classV_value`, `re_subset_mipstar_of` and `mipstar_eq_re_of` are in the source module, not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/ClassMain.lean; blueprint thm:halting

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassMain.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_ClassMIPStarTab
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
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Build
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Main
import Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassVerifier

/-!
# `RE ⊆ MIP*_{1,1/2}(2,1)`, and `MIP*_{1,1/2}(2,1) = RE`

The class verifier of `Paper/ClassVerifier.lean` is a `PolyVerifier` for the polynomial
`classP` chosen above its four cost bounds (`sampB`, `dimB`, `decB`, `cutB`, each polynomially
bounded here), and:

* it is **efficient** on every input (`classV_efficient`): the sampler's cost and the decider's
  are within the polynomial, the questions have the compressed sampler's dimension at the fixed
  level, and the decider rejects overlong messages — the answers by its cutoff, the questions
  by the wrapper's length check;
* its **game** on `z` has the value of `𝒱^halt (R z) λ(z)` at the fixed level `C` with the
  answers cut at `cutz z` (`classV_value`): the uniform seed of length `B ≥ s(C)` pushes
  forward, through its first `s(C)` bits, to the compressed sampler's distribution
  (`length_filter_take`, `length_filter_bitStrsOfLen`), so the game is the restriction of the
  verifier's to the questions of length `s(C)` (`quantumValue_restrictQuestions`) with the
  answers extended by always-rejected ones (`quantumValue_extendAnswers`);
* that value is `1` on `L` and at most `1/2` off it (`thm:halting` at the fixed level,
  `halting_paper`): the cutoff is at least the compressor's answer bound, and below it the
  decider of `𝒱^halt` rejects overlong answers whenever `M` does not halt.

Hence `re_subset_mipstar_of` and `mipstar_eq_re_of` (blueprint `thm:mipstar-eq-re`,
for the paper's class), given a compressor and the two universal machines; the unconditional
forms are in `MIPRE/Background/Pipeline.lean` and `MIPRE/MainTheorem.lean`.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.PolyTimeFun CL Verifier

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)

/-! ## The bounds are polynomial -/

theorem polyBounded_lamB : PolyBounded (lamB Λ₀ R) :=
  (PolyBounded.const Λ₀).add
    ((PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 1)).const_mul 4)

theorem polyBounded_dimB : PolyBounded (dimB G Λ₀ R) :=
  PolyBounded.eval _ ((PolyBounded.const (C G)).add (polyBounded_lamB Λ₀ R))

theorem polyBounded_T1B : PolyBounded (T1B G Λ₀ R) :=
  PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 3)

/-- The shape of the three universal calls' bounds. -/
theorem polyBounded_call {T : ℕ → ℕ} (hT : PolyBounded T) :
    PolyBounded fun m => 2 * T m + (4 * dimB G Λ₀ R m + 1) +
      U.bound.eval (2 * T m + dimB G Λ₀ R m * (T m + 1) ^ G.deg) + 8 :=
  have hd := polyBounded_dimB G Λ₀ R
  (((hT.const_mul 2).add ((hd.const_mul 4).add_const 1)).add
    (PolyBounded.eval _ ((hT.const_mul 2).add (hd.mul ((hT.add_const 1).pow G.deg))))).add_const 8

theorem polyBounded_R1B : PolyBounded (R1B G U Λ₀ R) :=
  polyBounded_call G U Λ₀ R (polyBounded_T1B G Λ₀ R)

theorem polyBounded_unB_dimB : PolyBounded fun m => unB (dimB G Λ₀ R m) :=
  have hd := polyBounded_dimB G Λ₀ R
  (hd.add_const 2).mul ((((hd.add_const 1).mul ((hd.const_mul 4).add_const 14)).add
    (((hd.const_mul 4).add_const 1).const_mul 7)).add ((hd.const_mul 8).add_const 90))

theorem polyBounded_UnB : PolyBounded (UnB G U Λ₀ R) :=
  (((polyBounded_R1B G U Λ₀ R).add (((polyBounded_dimB G Λ₀ R).const_mul 4).add_const 1)).add
    (polyBounded_unB_dimB G Λ₀ R)).add_const 5

theorem polyBounded_T2B : PolyBounded (T2B G U Λ₀ R) :=
  PolyBounded.eval _ (polyBounded_UnB G U Λ₀ R)

theorem polyBounded_R2B : PolyBounded (R2B G U Λ₀ R) :=
  polyBounded_call G U Λ₀ R (polyBounded_T2B G U Λ₀ R)

theorem polyBounded_T3B : PolyBounded (T3B G U Λ₀ R) :=
  PolyBounded.eval _ (polyBounded_R2B G U Λ₀ R)

theorem polyBounded_R3B : PolyBounded (R3B G U Λ₀ R) :=
  polyBounded_call G U Λ₀ R (polyBounded_T3B G U Λ₀ R)

theorem polyBounded_sampB : PolyBounded (sampB G U Λ₀ R) :=
  ((((((((polyBounded_T1B G Λ₀ R).add (polyBounded_R1B G U Λ₀ R)).add
    (polyBounded_UnB G U Λ₀ R)).add (polyBounded_T2B G U Λ₀ R)).add
    (polyBounded_R2B G U Λ₀ R)).add (polyBounded_T3B G U Λ₀ R)).const_mul 2).add
    (polyBounded_R3B G U Λ₀ R)).add_const 18

theorem polyBounded_TDB : PolyBounded (TDB G U UT Λ₀ K R) :=
  PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 9)

theorem polyBounded_zB : PolyBounded (zB G Λ₀ R) :=
  (((PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 1)).add
    (PolyBounded.const (C G))).add (polyBounded_lamB Λ₀ R)).add
    ((PolyBounded.id.const_mul 4).add_const 7)

theorem polyBounded_decB : PolyBounded (decB G U UT Λ₀ K R) :=
  have hTD := polyBounded_TDB G U UT Λ₀ K R
  ((hTD.const_mul 3).add (PolyBounded.eval _ (hTD.add
    (((polyBounded_WZ G U UT (semL G U)).comp (polyBounded_zB G Λ₀ R)).add_const
      constCost)))).add_const 6

/-- The cutoff, in the input length. -/
noncomputable def cutB (m : ℕ) : ℕ :=
  2 ^ (K + G.bound.natDegree) * (2 * lamB Λ₀ R m + 1) ^ (4 * G.bound.natDegree)

theorem polyBounded_cutB : PolyBounded (cutB G Λ₀ K R) :=
  (PolyBounded.const _).mul ((((polyBounded_lamB Λ₀ R).const_mul 2).add_const 1).pow _)

/-! ## The class verifier -/

/-- **The polynomial of the class verifier**: above the sampler's cost, the dimension, the
decider's cost and the cutoff. -/
noncomputable def classP : Polynomial ℕ :=
  (polyBounded_sampB G U Λ₀ R).poly + (polyBounded_dimB G Λ₀ R).poly +
    (polyBounded_decB G U UT Λ₀ K R).poly + (polyBounded_cutB G Λ₀ K R).poly

theorem dimB_le (m : ℕ) : dimB G Λ₀ R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_dimB G Λ₀ R).le_poly_eval m; omega

/-- **The class verifier** of the language reduced to halting by `R`. -/
noncomputable def classV : PolyVerifier where
  sampler := sampProg G U Λ₀ R
  sampler_closed := sampProg_wellScoped G U Λ₀ R
  decider := decProg G U UT Λ₀ K R
  decider_closed := decProg_wellScoped G U UT Λ₀ K R
  bound := classP G U UT Λ₀ K R

theorem dimz_le_B (z : BitStr) : dimz G Λ₀ R z ≤ (classV G U UT Λ₀ K R).B z :=
  (dimz_le G Λ₀ R z z.length le_rfl).trans (dimB_le G U UT Λ₀ K R _)

/-- The verifier `𝒱^halt (R z) λ(z)` the class verifier plays on `z`. -/
noncomputable abbrev Vz (z : BitStr) : Verifier 7 := Vpaper G U UT (R z) (lamz Λ₀ R z)

theorem qOf_length (w : Player) (z r : BitStr) : (qOf G Λ₀ R w z r).length = dimz G Λ₀ R z :=
  length_toBits _

/-! ## The value of the game -/

/-- The embedding of the compressed sampler's questions into the strings of length at most
`B z`. -/
noncomputable def qEmb (z : BitStr) :
    (Vz G U UT Λ₀ R z).Questions (C G) ↪ Answers ((classV G U UT Λ₀ K R).B z) where
  toFun v := ⟨toBits v, by rw [length_toBits]; exact dimz_le_B G U UT Λ₀ K R z⟩
  inj' v w h := by
    have := congrArg Subtype.val h
    simp only at this
    rw [← ofBits_toBits v, ← ofBits_toBits w, this]

/-! ## `RE ⊆ MIP*`, and `MIP* = RE` -/

end MIPRE.Halting


