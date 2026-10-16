-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider
-- name    : MIPRE_Foundations_Halting_Paper_Decider
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:06:24.38141+00:00
-- url     : https://prove2.me/theorems/99e94fbc-da2d-4c07-899f-752fa6199693
-- title:
--   The halting verifier $\mathcal{V}^{\mathrm{halt}}$ along the paper's route: its decider as a Kleene fixed point
-- statement:
--   Blueprint `lem:halt-construction` in the paper's form (`recursive.tex`, `fig:halt_f`). Fix $G : \mathrm{GapCompression}$, $U : \mathrm{UniversalMachine}$, a clocked universal machine $UT$ and a search program $S'$; $M$ is a machine (a program) and $\lambda$ a parameter.
--
--   **Polynomial-time pieces.** `MIPRE.Halting.descPoly : PolyTimeFun (ℕ × Prog) BitStr` is $(\lambda, d) \mapsto$ `descOf λ d`; `wrapBuild U : PolyTimeFun (Prog × Prog) Prog` is $(s, d) \mapsto$ `wrapCore U.univ s (encode d)`; `wrapPoly G U : PolyTimeFun (ℕ × Prog) Prog` is $(\lambda, d) \mapsto$ `wrapCore U.univ (G.samplerProg λ) (encode d)`; `reencode` is the identity on `ℕ × Data` as a `PolyTimeFun`; `trueProg`, `falseProg` are `const (encode true)`, `const (encode false)`; `searchP S' lam d = hardcode (Prog.onLeft S') (encode (descOf lam d))` is $S'$ hardcoded to the description; `comprDec G U lam d = G.compress ((G.samplerProg lam, wrapCore U.univ (G.samplerProg lam) (encode d)), lam)`.
--
--   **The three branches.** `prep G U UT S'`, a `PolyTimeFun`, maps the description $(M, (\lambda, d'))$ and the input $(n, \mathit{rest})$ to the program to run and its input: if $M$ halts on the empty input within budget $\mathrm{size}\,n$, `(trueProg, nil)`; else if `searchP S' λ d'` halts within $\mathrm{size}\,n$, `(falseProg, nil)`; else `(comprDec G U λ d', encode (n, rest))`. `body G U UT S' = let_ (prep …).code (callVar 0 U.univ)` runs `prep`, then $U$ on its output.
--
--   **The fixed point.** `F G U UT S' M lam : PolyTimeFun Prog Prog` is $d' \mapsto$ `hardcode body (encode (M, (λ, d')))`; `dec G U UT S' M lam = kleeneFix U (F …)` is the decider $\mathcal{D}^{\mathrm{halt}}$; and
--   $$\mathrm{Vhalt}\;G\;U\;UT\;S'\;M\;\lambda = \mathrm{ofSamplerDecider}\;U\;(G.\mathrm{sampler}\;\lambda)\;(\mathrm{dec}\;G\;U\;UT\;S'\;M\;\lambda) : \mathrm{Verifier}\;7 .$$
--
--   The embedded lemmas are `descPoly_apply`, `prep_apply` (the three-way `if` above), `body_wellScoped`, `F_apply`, `Vhalt_sampler` and `Vhalt_decider_prog`.
--
--   **Formalization Note**. Branch 2 is the search branch the module attributes to Lin (the value form of compression has no base case for soundness); branches 1 and 3 are the paper's $\mathcal{F}$. The budgets are $\mathrm{size}\,n$ rather than $n$, which along the levels $n, 2^n, \dots$ costs nothing. `prep_apply` is stated with the `noncomputable` `evalWithin`, which the clocked machine $UT$ computes; all `PolyTimeFun`s here are `noncomputable`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Decider.lean; blueprint lem:halt-construction; paper recursive.tex, fig:halt_f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Decider.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL

/-!
# The halting verifier along the paper's route: the decider

Blueprint `lem:halt-construction` in the paper's form (`recursive.tex`, `fig:halt_f`), for the
polynomial-time halting reduction of `planning/polytime-halting.md`. For a machine `M` and a
parameter `λ`, the verifier is

  `Vhalt M λ = Verifier.ofSamplerDecider U (G.sampler λ) (dec M λ)`,

the compressed sampler at `λ` together with the decider `dec M λ`, wrapped in the question-length
check of `def:normal-verifier`. The decider is an efficient Kleene fixed point (`Cost.kleeneFix`)
of the map `d' ↦ hardcode body (encode (M, (λ, d')))`, so that on `(n, x, y, a, b)` it runs
`body` on the pair of its own description `(M, (λ, dec M λ))` and the input, where `body`:

1. runs `M` on the empty input for the budget `Nat.size n` (the clocked universal machine); if
   it halts, **accepts**;
2. otherwise runs the semidecider `S'` of the search branch — "`val*` at level `C₀` of the
   verifier this string describes exceeds `1/2`" (`exists_semL`) — on the description
   `descOf λ (dec M λ)`, for the budget `Nat.size n`; if it halts, **rejects**;
3. otherwise computes the compressed decider `Compress ((S^compr_λ, wrap (dec M λ)), λ)` of its
   own verifier and runs it on the input through the universal machine.

Branch 2 is Lin's search branch, which the criterion route (`Compression.lean`, `decFunV`) has
too: the value form of compression has no base case for soundness, and the search supplies it.
Branches 1 and 3 are the paper's `F`. The reading of `M`'s and the search's budgets as `Nat.size
n` rather than `n` is the criterion's, and costs nothing: the levels of the recursion are
`n, 2 ^ n, …`, along which `Nat.size` grows without bound.

`body` is the program of a polynomial-time function `prep` returning the pair "program to run,
its input" — branch 1 returns the constant-`true` program, branch 2 the constant-`false` one,
branch 3 the compressed decider on the input — followed by one call of the universal machine.
That is what makes the acceptance characterization (`accepts_iff`, blueprint
`lem:dhalt-values`) a matter of running `prep` and reading its output, and what keeps the
accounting (`Paper/Cost.lean`) to `prep`'s time bound plus the universal machine's overhead on
the compressed decider.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.Prog.ProgD Polynomial

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-! ## Three polynomial-time pieces -/

/-- The description string `descOf λ d` of a pair, as a polynomial-time function: `serProg`. -/
noncomputable def descPoly : PolyTimeFun (ℕ × Prog) BitStr where
  toFun p := descOf p.1 p.2
  code := serProg
  closed := serProg_wellScoped
  timeBound := (C 3 * X + C 2) * (C 16 * X + C 42) + (X + C 2) * (C 5 * X + C 30)
  computes p := by
    obtain ⟨lam, d⟩ := p
    obtain ⟨t, ht, h⟩ := serProg_runs (encode (lam, d))
    refine ⟨t, ?_, h⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    exact ht

@[simp] theorem descPoly_apply (lam : ℕ) (d : Prog) : descPoly (lam, d) = descOf lam d := rfl

/-- The wrapper's description, as a polynomial-time function of the sampler program and the
inner decider: `wrapBuildProg`. -/
noncomputable def wrapBuild : PolyTimeFun (Prog × Prog) Prog where
  toFun p := wrapCore U.univ p.1 (encode p.2)
  code := wrapBuildProg (encode U.univ)
  closed := wrapBuildProg_wellScoped _
  timeBound := X + C (2 * esize U.univ + wrapNodes + 3)
  computes p := by
    obtain ⟨s, d⟩ := p
    obtain ⟨t, ht, h⟩ := wrapBuildProg_runs (encode U.univ) (encode s) (encode d)
    refine ⟨t, ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod]
      have e1 : (encode s : Data).size = esize s := rfl
      have e2 : (encode d : Data).size = esize d := rfl
      have e3 : (encode U.univ : Data).size = esize U.univ := rfl
      omega
    · rw [dWrapCore_eq] at h
      exact h

/-- `(λ, d) ↦ wrapCore U.univ (G.samplerProg λ) (encode d)`, the program of the wrapped decider
of the verifier `(S^compr_λ, d)`. -/
noncomputable def wrapPoly : PolyTimeFun (ℕ × Prog) Prog :=
  (wrapBuild U).comp ((G.samplerProg.comp PolyTimeFun.fst).pair PolyTimeFun.snd)

/-- The pair `(n, rest)` as the datum `encode (n, rest)`: the identity program. -/
noncomputable def reencode : PolyTimeFun (ℕ × Data) Data where
  toFun p := encode p
  code := .var 0
  closed := Nat.zero_lt_one
  timeBound := X + 1
  computes p := ⟨esize p + 1, by simp, Eval.var _ _⟩

/-- The program halting with output `true` on every input. -/
def trueProg : Prog := .const (encode true)

/-- The program halting with output `false` on every input. -/
def falseProg : Prog := .const (encode false)

/-- The search program of the pair `(λ, d)`: the semidecider `S'` hard-coded to the description
`descOf λ d`, to be run on the empty input. -/
def searchP (S' : Prog) (lam : ℕ) (d : Prog) : Prog :=
  hardcode (Prog.onLeft S') (encode (descOf lam d))

/-! ## The preparation, and the decider -/

/-- **The three branches**, as a polynomial-time function of the description `(M, (λ, d'))` and
the input `(n, rest)`: the program to run and its input. -/
noncomputable def prep (S' : Prog) :
    PolyTimeFun ((Prog × (ℕ × Prog)) × (ℕ × Data)) (Prog × Data) :=
  PolyTimeFun.ite
    ((PolyTimeFun.haltsWithin UT).comp
      (PolyTimeFun.pair (PolyTimeFun.fst.comp PolyTimeFun.fst)
        (PolyTimeFun.fst.comp PolyTimeFun.snd)))
    (PolyTimeFun.const (trueProg, Data.nil))
    (PolyTimeFun.ite
      ((PolyTimeFun.haltsWithin UT).comp
        (PolyTimeFun.pair
          ((haltingReduction S').comp (descPoly.comp
            (PolyTimeFun.pair ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst)
              ((PolyTimeFun.snd.comp PolyTimeFun.snd).comp PolyTimeFun.fst))))
          (PolyTimeFun.fst.comp PolyTimeFun.snd)))
      (PolyTimeFun.const (falseProg, Data.nil))
      (PolyTimeFun.pair
        (G.compress.comp (PolyTimeFun.pair
          (PolyTimeFun.pair
            (G.samplerProg.comp ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst))
            ((wrapPoly G U).comp
              (PolyTimeFun.pair ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst)
                ((PolyTimeFun.snd.comp PolyTimeFun.snd).comp PolyTimeFun.fst))))
          ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst)))
        (reencode.comp PolyTimeFun.snd)))

/-- The compressed decider of the verifier `(S^compr_λ, wrap d)`. -/
noncomputable def comprDec (lam : ℕ) (d : Prog) : Prog :=
  G.compress ((G.samplerProg lam, wrapCore U.univ (G.samplerProg lam) (encode d)), lam)

theorem prep_apply (S' M : Prog) (lam : ℕ) (d : Prog) (n : ℕ) (rest : Data) :
    prep G U UT S' ((M, (lam, d)), (n, rest)) =
      if (evalWithin M .nil (Nat.size n)).isSome then (trueProg, Data.nil)
      else if (evalWithin (searchP S' lam d) .nil (Nat.size n)).isSome then (falseProg, Data.nil)
      else (comprDec G U lam d, encode (n, rest)) := rfl

/-- **The body of the decider**: run `prep`, then the universal machine on its output. -/
noncomputable def body (S' : Prog) : Prog := .let_ (prep G U UT S').code (callVar 0 U.univ)

theorem body_wellScoped (S' : Prog) : (body G U UT S').WellScoped 1 :=
  ⟨(prep G U UT S').closed, callVar_wellScoped (by decide) U.closed⟩

/-- The map whose fixed point is the decider: `d' ↦ hardcode body (encode (M, (λ, d')))`. -/
noncomputable def F (S' M : Prog) (lam : ℕ) : PolyTimeFun Prog Prog :=
  (PolyTimeFun.smn (Prog × (ℕ × Prog))).comp
    (PolyTimeFun.pair (PolyTimeFun.const (body G U UT S'))
      (PolyTimeFun.pair (PolyTimeFun.const M)
        (PolyTimeFun.pair (PolyTimeFun.const lam) (PolyTimeFun.id Prog))))

theorem F_apply (S' M : Prog) (lam : ℕ) (d : Prog) :
    F G U UT S' M lam d = hardcode (body G U UT S') (encode (M, (lam, d))) := rfl

/-- **The decider `𝒟^halt`** of the machine `M` at the parameter `λ`: the efficient Kleene fixed
point of `F`. -/
noncomputable def dec (S' M : Prog) (lam : ℕ) : Prog := kleeneFix U (F G U UT S' M lam)

/-- **The verifier `𝒱^halt`** of the machine `M` at the parameter `λ`. -/
noncomputable def Vhalt (S' M : Prog) (lam : ℕ) : Verifier 7 :=
  Verifier.ofSamplerDecider U (G.sampler lam) (dec G U UT S' M lam)

@[simp] theorem Vhalt_sampler (S' M : Prog) (lam : ℕ) :
    (Vhalt G U UT S' M lam).sampler = G.sampler lam := rfl

theorem Vhalt_decider_prog (S' M : Prog) (lam : ℕ) :
    (Vhalt G U UT S' M lam).decider.prog =
      wrapCore U.univ (G.sampler lam).prog (encode (dec G U UT S' M lam)) := rfl

/-! ## Running the decider -/

end MIPRE.Halting


