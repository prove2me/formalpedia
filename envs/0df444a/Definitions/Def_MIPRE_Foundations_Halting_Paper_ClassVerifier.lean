-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassVerifier
-- name    : MIPRE_Foundations_Halting_Paper_ClassVerifier
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:18:46.99973+00:00
-- url     : https://prove2.me/theorems/ac747939-f7c6-4287-8983-f4c16299ab7f
-- title:
--   The class verifier of the polynomial-time halting reduction: its sampler and decider programs
-- statement:
--   Fix a gap compression $G$, universal machines $U$ and (clocked) $U_T$, constants $\Lambda_0, K$ and a polynomial-time reduction $R$ of a language $L$ to halting on the empty input. The bundle defines the two programs of the polynomial-time verifier that puts $L$ in $\mathrm{MIP}^*_{1,1/2}(2,1)$: on input $z$ it plays the game of $\mathcal{V}^{\mathrm{halt}}(R(z), \lambda(z))$ at the fixed level $C = \max(C_0(G), 2)$.
--
--   Parameters: `lamz z` is $\lambda(z) = \Lambda_0 + 4|R(z)|$ (`lem:lambda`); `Sz z` is the compressed sampler $G.\mathrm{sampler}(\lambda(z))$ and `dimz z` its dimension at level $C$; `qOf w z r`, player $w$'s question on the seed $r$, is the marginal of `Sz z` at the first `dimz z` bits of $r$; `cutz z` is the cutoff $2^{K + \deg\cdot|\lambda(z)|}$, $\deg$ the degree of $G.\mathrm{bound}$.
--
--   Sampler: `spF` maps $(z,r)$ to `ComputeSampler`$(\lambda(z))$; `queryF w`, `qdim` are the marginal and dimension queries at level $C$, as data; the stages `A1`, `A2`, `A3` return the next (program, query) pair and the carried state; `sampProg` chains them with three universal calls and a binary-to-unary conversion:
--
--   $$\mathtt{sampProg} = \mathtt{A1};\ \mathtt{runUK}\,U;\ \mathtt{unaryStage};\ \mathtt{A2};\ \mathtt{runUK}\,U;\ \mathtt{A3};\ \mathtt{runUK}\,U.$$
--
--   Decider: on $q = (z,x,y,a,b)$, `MzF`, `lamzF`, `cutzF`, `aF`, `bF` read $R(z)$, $\lambda(z)$, `cutz z`, $a$, $b$; `wF` computes `wdec z`, the wrapped decider of $\mathcal{V}^{\mathrm{halt}}$; `inputF` encodes $(C,x,y,a,b)$; `rejF` is the constant-false program; `D1` returns `(wF q, inputF q)` if $|a|$ and $|b|$ are at most `cutz z`, else `rejF`; `decProg` runs `D1`, then $U$.
--
--   Cost bounds in the total input length $m$: `lamB`, `dimB`; the stage costs `T1B`, `T2B`, `T3B`; the universal-call costs `R1B`, `R2B`, `R3B`; the conversion costs `unB`, `UnB`; their total `sampB`; for the decider `TDB`, `zB`, `decB`. Embedded lemmas: `sampProg` and `decProg` are closed (`WellScoped 1`), `queryF G w z` is the encoded marginal query, and `lamz z ≤ lamB m`, `dimz z ≤ dimB m` for $|z| \le m$.
--
--   **Formalization Note** All declarations take `G : GapCompression`, `U : UniversalMachine`, `UT : ClockedUniversalMachine`, `Λ₀ K : ℕ`, `R : PolyTimeFun BitStr Prog`. The pieces are `PolyTimeFun`s of the cost model; `sampProg`, `decProg` are `Prog`s built with `seq`. The run theorems `sampProg_runs`, `decProg_accepts`, `decProg_runs` are in the source module, not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/ClassVerifier.lean; blueprint lem:lambda; blueprint thm:halting

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassVerifier.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The class verifier of the polynomial-time halting reduction

The two programs of the `PolyVerifier` (`def:mipstar`) that puts an r.e. language `L` in the
paper's class `MIP*_{1,1/2}(2,1)`, for a polynomial-time reduction `R` of `L` to halting on the
empty input (`Cost.exists_polyTime_reduction`): on input `z` they play the game of
`𝒱^halt (R z) λ(z)` at the fixed level `C` (`Paper/Main.lean`), with
`λ(z) = Λ₀ + 4|R z|` the parameter of `lem:lambda`.

* **The sampler** `sampProg`, on `(z, r)`: computes `M = R z`, `λ(z)` and the compressed
  sampler's program `S = ComputeSampler(λ(z))` (`A1`); asks `S` its dimension `s = s(C)` through
  the universal machine (`runUK`); converts `s` to unary (`unaryStage`); takes the first `s`
  bits `r'` of the seed and asks `S` Alice's marginal `L^A(r')` (`A2`, `runUK`); then Bob's
  (`A3`, `runUK`). Its output is the question pair of `𝒱^halt` at the point `r'`
  (`sampProg_runs`), so that the uniform seed of length `B ≥ s` pushes forward to the
  compressed sampler's distribution.
* **The decider** `decProg`, on `(z, x, y, a, b)`: computes `M`, `λ(z)` and the description of
  `𝒱^halt`'s decider (`wrapCore` around `dec M λ(z)`, `decBuild`), rejects if `a` or `b` is
  longer than the cutoff `2 ^ (K + deg · |λ(z)|)` (`cutF`, at least the compressor's answer
  bound `poly(C, λ(z))` by `exists_cut_ge`), and otherwise runs the description on
  `(C, x, y, a, b)` through the universal machine (`runU`). It accepts exactly when both
  answers are within the cutoff and `𝒱^halt`'s decider accepts (`decProg_accepts`).

The costs are bounded by explicit expressions in the total input length (`sampB`, `decB`),
polynomially bounded (`polyBounded_sampB`, `polyBounded_decB`); `Paper/ClassMain.lean` chooses
the verifier's polynomial above them and proves the game's value.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.PolyTimeFun CL

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)

/-! ## The parameter, the sampler and the pieces -/

/-- The parameter of the input `z`: `Λ₀ + 4|R z|`. -/
def lamz (z : BitStr) : ℕ := Λ₀ + 4 * esize (R z)

/-- The compressed sampler of the input `z`. -/
noncomputable abbrev Sz (z : BitStr) : Sampler 7 := G.sampler (lamz Λ₀ R z)

/-- The dimension of its questions at the fixed level. -/
noncomputable def dimz (z : BitStr) : ℕ := (Sz G Λ₀ R z).dim (C G)

/-- Player `w`'s question on the seed `r`, on the input `z`: the marginal of the compressed
sampler at the first `dimz z` bits of `r`. -/
noncomputable def qOf (w : Player) (z r : BitStr) : BitStr :=
  toBits (((Sz G Λ₀ R z).cl (C G) w).eval
    (ofBits (dimz G Λ₀ R z) (r.take (dimz G Λ₀ R z))))

/-- `(z, r) ↦ ComputeSampler(λ(z))`. -/
noncomputable def spF : PolyTimeFun (BitStr × BitStr) Prog :=
  G.samplerProg.comp ((lamF Λ₀).comp (R.comp fst))

/-- The marginal query of player `w` at the fixed level, as data. -/
noncomputable def queryF (w : Player) : PolyTimeFun BitStr Data :=
  cast (pair (const (C G)) (pair (const (1 : ℕ)) (pair (const w) (pair (const (7 : ℕ))
    (pair (id BitStr) (const ([] : BitStr)))))))
    (fun z => encode (C G, Sampler.Query.marginal w 7 z)) (fun _ => rfl)

@[simp] theorem queryF_apply (w : Player) (z : BitStr) :
    queryF G w z = encode (C G, Sampler.Query.marginal w 7 z) := rfl

/-- The dimension query at the fixed level, as data. -/
def qdim : Data := encode (C G, Sampler.Query.dimension)

/-- Stage 1: from `(z, r)`, the pair `(S, dimension)` to run and the state `(S, r)`. -/
noncomputable def A1 : PolyTimeFun (BitStr × BitStr) ((Prog × Data) × (Prog × BitStr)) :=
  pair (pair (spF G Λ₀ R) (const (qdim G))) (pair (spF G Λ₀ R) snd)

/-- Stage 2: from `((S, r), s)` with `s` in unary, the pair `(S, marginal A (r.take s))` to
run and the state `(S, r.take s)`. -/
noncomputable def A2 :
    PolyTimeFun ((Prog × BitStr) × Unary) ((Prog × Data) × (Prog × BitStr)) :=
  pair (pair (fst.comp fst) ((queryF G .alice).comp (take.comp (pair (snd.comp fst) snd))))
    (pair (fst.comp fst) (take.comp (pair (snd.comp fst) snd)))

/-- Stage 3: from `((S, r'), x)`, the pair `(S, marginal B r')` to run and the state `x`. -/
noncomputable def A3 : PolyTimeFun ((Prog × BitStr) × BitStr) ((Prog × Data) × BitStr) :=
  pair (pair (fst.comp fst) ((queryF G .bob).comp (snd.comp fst))) snd

/-- **The sampler of the class verifier.** -/
noncomputable def sampProg : Prog :=
  seq (A1 G Λ₀ R).code (seq (runUK U.univ) (seq unaryStage (seq (A2 G).code
    (seq (runUK U.univ) (seq (A3 G).code (runUK U.univ))))))

theorem sampProg_wellScoped : (sampProg G U Λ₀ R).WellScoped 1 :=
  seq_wellScoped (A1 G Λ₀ R).closed (seq_wellScoped (runUK_wellScoped U.closed)
    (seq_wellScoped unaryStage_wellScoped (seq_wellScoped (A2 G).closed
      (seq_wellScoped (runUK_wellScoped U.closed) (seq_wellScoped (A3 G).closed
        (runUK_wellScoped U.closed))))))

/-! ## Running the sampler -/

/-- The cost of the binary-to-unary conversion, monotone in the number. -/
def unB (D : ℕ) : ℕ := (D + 2) * ((D + 1) * (4 * D + 14) + 7 * (4 * D + 1) + 8 * D + 90)

/-- The parameter, in the total input length `m`. -/
noncomputable def lamB (m : ℕ) : ℕ := Λ₀ + 4 * R.timeBound.eval (4 * m + 1)
/-- The compressor's bound `poly(C, λ)`, in `m`: bounds the dimension and the times. -/
noncomputable def dimB (m : ℕ) : ℕ := G.bound.eval (C G + lamB Λ₀ R m)
/-- Stage 1's cost. -/
noncomputable def T1B (m : ℕ) : ℕ := (A1 G Λ₀ R).timeBound.eval (4 * m + 3)
/-- The first universal call's cost. -/
noncomputable def R1B (m : ℕ) : ℕ :=
  2 * T1B G Λ₀ R m + (4 * dimB G Λ₀ R m + 1) +
    U.bound.eval (2 * T1B G Λ₀ R m + dimB G Λ₀ R m * (T1B G Λ₀ R m + 1) ^ G.deg) + 8
/-- The conversion's cost. -/
noncomputable def UnB (m : ℕ) : ℕ :=
  R1B G U Λ₀ R m + (4 * dimB G Λ₀ R m + 1) + unB (dimB G Λ₀ R m) + 5
/-- Stage 2's cost. -/
noncomputable def T2B (m : ℕ) : ℕ := (A2 G).timeBound.eval (UnB G U Λ₀ R m)
/-- The second universal call's cost. -/
noncomputable def R2B (m : ℕ) : ℕ :=
  2 * T2B G U Λ₀ R m + (4 * dimB G Λ₀ R m + 1) +
    U.bound.eval (2 * T2B G U Λ₀ R m + dimB G Λ₀ R m * (T2B G U Λ₀ R m + 1) ^ G.deg) + 8
/-- Stage 3's cost. -/
noncomputable def T3B (m : ℕ) : ℕ := (A3 G).timeBound.eval (R2B G U Λ₀ R m)
/-- The third universal call's cost. -/
noncomputable def R3B (m : ℕ) : ℕ :=
  2 * T3B G U Λ₀ R m + (4 * dimB G Λ₀ R m + 1) +
    U.bound.eval (2 * T3B G U Λ₀ R m + dimB G Λ₀ R m * (T3B G U Λ₀ R m + 1) ^ G.deg) + 8
/-- **The sampler's cost**, in the total input length. -/
noncomputable def sampB (m : ℕ) : ℕ :=
  2 * (T1B G Λ₀ R m + R1B G U Λ₀ R m + UnB G U Λ₀ R m + T2B G U Λ₀ R m +
    R2B G U Λ₀ R m + T3B G U Λ₀ R m) + R3B G U Λ₀ R m + 18

theorem lamz_le (z : BitStr) (m : ℕ) (hm : z.length ≤ m) :
    lamz Λ₀ R z ≤ lamB Λ₀ R m := by
  unfold lamz lamB
  have h1 := R.esize_apply_le z
  have h2 := esize_bitStr_le z
  have h3 := polynomial_eval_mono R.timeBound (show esize z ≤ 4 * m + 1 by omega)
  omega

theorem dimz_le (z : BitStr) (m : ℕ) (hm : z.length ≤ m) :
    dimz G Λ₀ R z ≤ dimB G Λ₀ R m :=
  (G.sampler_dim _ _).trans (polynomial_eval_mono _ (by have := lamz_le Λ₀ R z m hm; omega))

/-! ## The decider -/

/-- `q ↦ R z` on the decider's input `q = (z, x, y, a, b)`. -/
noncomputable def MzF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) Prog :=
  R.comp fst

/-- `q ↦ λ(z)`. -/
noncomputable def lamzF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) ℕ :=
  (lamF Λ₀).comp (MzF R)

/-- The cutoff on the input `z`: `2 ^ (K + deg · |λ(z)|)`. -/
def cutz (z : BitStr) : ℕ := 2 ^ (K + G.bound.natDegree * esize (lamz Λ₀ R z))

/-- `q ↦ cutz z`. -/
noncomputable def cutzF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) ℕ :=
  (cutF K G.bound.natDegree).comp (lamzF Λ₀ R)

/-- `q ↦ a`. -/
noncomputable def aF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) BitStr :=
  fst.comp (snd.comp (snd.comp snd))

/-- `q ↦ b`. -/
noncomputable def bF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) BitStr :=
  snd.comp (snd.comp (snd.comp snd))

/-- `q ↦ wrapCore univ (ComputeSampler λ(z)) (dec (R z) λ(z))`, the decider of `𝒱^halt`. -/
noncomputable def wF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) Prog :=
  (wrapPoly G U).comp (pair (lamzF Λ₀ R)
    ((decBuild G U UT (semL G U)).comp (pair (MzF R) (lamzF Λ₀ R))))

/-- The decider of `𝒱^halt (R z) λ(z)`, wrapped. -/
noncomputable def wdec (z : BitStr) : Prog := (Vpaper G U UT (R z) (lamz Λ₀ R z)).decider.prog

/-- `q ↦ encode (C, x, y, a, b)`, the decider's input at the fixed level. -/
noncomputable def inputF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) Data :=
  cast (pair (const (C G)) (pair (fst.comp snd) (pair (fst.comp (snd.comp snd)) (pair aF bF))))
    (fun q => encode (C G, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) (fun _ => rfl)

/-- The rejecting branch: the constant-`false` program on the empty input. -/
noncomputable def rejF :
    PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) (Prog × Data) :=
  const (falseProg, Data.nil)

/-- **The preparation of the class decider**: the program to run and its input — the
constant-`false` program if `a` or `b` exceeds the cutoff, else `𝒱^halt`'s decider on
`(C, x, y, a, b)`. -/
noncomputable def D1 :
    PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) (Prog × Data) :=
  ite (leNat.comp (pair (lenBin.comp aF) (cutzF G Λ₀ K R)))
    (ite (leNat.comp (pair (lenBin.comp bF) (cutzF G Λ₀ K R)))
      (pair (wF G U UT Λ₀ R) (inputF G)) rejF)
    rejF

/-- **The decider of the class verifier**: the preparation, then the universal machine. -/
noncomputable def decProg : Prog := seq (D1 G U UT Λ₀ K R).code U.univ

theorem decProg_wellScoped : (decProg G U UT Λ₀ K R).WellScoped 1 :=
  seq_wellScoped (D1 G U UT Λ₀ K R).closed U.closed

/-- The preparation's cost, in the total input length. -/
noncomputable def TDB (m : ℕ) : ℕ := (D1 G U UT Λ₀ K R).timeBound.eval (4 * m + 9)
/-- A common bound on the atoms of the wrapped decider's cost, in `m`. -/
noncomputable def zB (m : ℕ) : ℕ :=
  R.timeBound.eval (4 * m + 1) + C G + lamB Λ₀ R m + (4 * m + 7)
/-- **The class decider's cost**, in the total input length. -/
noncomputable def decB (m : ℕ) : ℕ :=
  3 * TDB G U UT Λ₀ K R m +
    U.bound.eval (TDB G U UT Λ₀ K R m + (WZ G U UT (semL G U) (zB G Λ₀ R m) + constCost)) + 6

end MIPRE.Halting


