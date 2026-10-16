-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_Main
-- name    : MIPRE_Foundations_Halting_Paper_Main
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:17:22.17504+00:00
-- url     : https://prove2.me/theorems/9789cd8a-936d-4700-804f-92a4ef63afa7
-- title:
--   The paper-route halting verifier with its search program fixed: `Vpaper` and the threshold
-- statement:
--   Blueprint `thm:halting` in the paper's form (`recursive.tex`), for the polynomial-time halting reduction: for every machine $M$ and every $\lambda \ge \Lambda_0 + 4|M|$, the verifier $\mathcal{V}^{\mathrm{halt}}\,M\,\lambda$ of `Paper/Decider.lean` at the fixed level $C = \max(C_0, 2)$ has a value-$1$ PCC strategy if $M$ halts on the empty input and value at most $1/2$ otherwise. This bundle fixes the two free parameters of that construction once and for all; the theorem itself is in the module and not part of the bundle. Fix $G : \mathrm{GapCompression}$, $U : \mathrm{UniversalMachine}$ and $UT : \mathrm{ClockedUniversalMachine}$.
--
--   `MIPRE.Halting.semL G U : Prog` is the search program: the semidecider of "$1/2 < \mathrm{val}^*$ at level $C$ of the verifier the string describes", chosen from `exists_semL G U (C G)` (`Paper/TabulateL.lean`), so that it is a closed program with `Halts (semL G U) (encode x) ↔ 1/2 < quantumValue (tabL G U x (C G)).game` for every string $x$. `MIPRE.Halting.Vpaper G U UT M lam : Verifier 7` is $\mathcal{V}^{\mathrm{halt}}$ with this search program,
--   $$\mathrm{Vpaper}\;G\;U\;UT\;M\;\lambda = \mathrm{Vhalt}\;G\;U\;UT\;(\mathrm{semL}\;G\;U)\;M\;\lambda ,$$
--   and `MIPRE.Halting.lamThreshold G U UT : ℕ` is `Lam0 G U UT (semL G U)`, the threshold $\Lambda_0$ of `lem:lambda` (`Paper/Cost.lean`) for this search program. The bundle has no embedded lemmas.
--
--   This is the criterion route's `thm:halting` with the level fixed and the parameter explicit, which is what makes the reduction polynomial-time: the game is $\mathcal{V}^{\mathrm{halt}}\,M\,\lambda$ at index $C$, its sampler is the compressed sampler at $\lambda = \Lambda_0 + 4|M|$ (polynomial-time in $|M|$ through `samplerProg`), and its decider runs within the polynomial bound of `Paper/Cost.lean`; the class verifier of the paper's $\mathrm{MIP}^*$ is this game read off a uniform program.
--
--   **Formalization Note**. All three definitions are `noncomputable`: `semL` is the `choose` of the existential theorem `exists_semL`, and `lamThreshold` unfolds to `Lam0`, itself the `choose` of `exists_lamBound`, so nothing about their values is known beyond the specifications those theorems give; `Vpaper` unfolds to `Verifier.ofSamplerDecider U (G.sampler lam) (dec G U UT (semL G U) M lam)`. The answer alphabet in the final statement is cut at the compressor's bound $\mathrm{poly}(C, \lambda)$, a polynomial in $\lambda$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Main.lean; blueprint thm:halting; paper recursive.tex

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Main.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
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

/-!
# The halting verifier along the paper's route: `thm:halting` at a fixed level

Blueprint `thm:halting` in the paper's form (`recursive.tex`), for the polynomial-time halting
reduction of `planning/polytime-halting.md`: for every machine `M` and every `λ ≥ Λ₀ + 4|M|`,
the verifier `𝒱^halt M λ` of `Paper/Decider.lean`, at the **fixed** level `C = max C₀ 2`, has
a value-`1` PCC strategy if `M` halts on the empty input and value at most `1/2` otherwise —
with the answer alphabet cut at the compressor's bound `poly(C, λ)`, a polynomial in `λ`.

This is the criterion route's `thm:halting` (`Halting/Reduction.lean`, `Criterion.lean`) with the
level fixed and the parameter explicit, which is what makes the reduction polynomial-time: the
game is `𝒱^halt M λ` at index `C`, its sampler is the compressed sampler at `λ = Λ₀ + 4|M|`
(polynomial-time in `|M|` through `samplerProg`), and its decider runs within the polynomial
bound of `Paper/Cost.lean`. The class verifier of the paper's `MIP*` (PR 3 of the plan) is this
game read off a uniform program.

The search program `S'` of the decider's second branch is `semL`, the semidecider of
"`val*` at level `C` of the verifier this string describes exceeds `1/2`" (`exists_semL`),
fixed once and for all; `Λ₀` is the threshold `Lam0` of `lem:lambda` (`Paper/Cost.lean`).
-/

namespace MIPRE.Halting

open Cost Cost.Prog

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-- **The search program**: the semidecider of `1/2 < val*` at level `C` of the described
verifier, from `exists_semL`. -/
noncomputable def semL : Prog := (exists_semL G U (C G)).choose

/-- The verifier `𝒱^halt M λ` with the search program `semL`. -/
noncomputable def Vpaper (M : Prog) (lam : ℕ) : Verifier 7 := Vhalt G U UT (semL G U) M lam

/-- The threshold of `lem:lambda` for the search program `semL`. -/
noncomputable def lamThreshold : ℕ := Lam0 G U UT (semL G U)

end MIPRE.Halting


