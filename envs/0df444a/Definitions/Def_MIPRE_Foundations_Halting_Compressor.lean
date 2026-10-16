-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Compressor
-- name    : MIPRE_Foundations_Halting_Compressor
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:57:51.745697+00:00
-- url     : https://prove2.me/theorems/eb2dc758-368f-4523-971b-4aaa12b0b0d7
-- title:
--   The compressor's decider as a program: reading, parsing, wrapping, freezing and compressing
-- statement:
--   Obligation O4 of blueprint `rem:compression-abstract`, the program half. Fix $G$ and $U$. On a succinct description $(c, n)$ of $x$ the compressor outputs a string denoting the compressed form of the verifier of $x$ frozen at $2n+1$.
--
--   Reading: `MIPRE.Cost.Prog.readTail`, `readBody univ`, `readProg univ` form the loop reading $x$ from $c$ by bit queries; answers `nil` and `cons nil nil` are the bits $0$, $1$, anything else the out-of-range marker that stops the loop; the accumulator is then reversed; `readState cD x i` is the state after $i$ bits, `readEnv` (private) an environment, `readIter U s n L` one iteration's cost.
--
--   **Descriptions as data** (`dK`, `dC`, `dL`, `dE`: the data of `const`, `cons`, `let_`, `elim`). `ProgD.dFreeze kD p` describes `freezeProg k p`; `ProgD.wrapNodes` is the wrapper description's fixed node count; `pK`, `pC`, `pL`, `pE i` build `dK`, `dC`, `dL`, `dE i`; `pCheck i j c` builds one length check around $c$; `wrapBuildProg univD` builds `dWrapCore univD sampD decD` from $\mathtt{cons}\ \mathit{sampD}\ \mathit{decD}$; `freezeBuildProg` builds `dFreeze kD p` from $\mathtt{cons}\ kD\ p$; `call2 i j q` runs the closed $q$ on the pair of variables $i$, $j$.
--
--   `MIPRE.Halting.prepProg G U`, on `encode (c, n, λ)`, reads $x$ from $c$, parses it, computes the encoded sampler program and the wrapped decider, freezes both at $2n+1$ and runs `G.compress.code` on the pair and $\lambda$; `haltProg G U`, on $\mathtt{cons}\ P\ d$, runs `prepProg` on $P$, then $U$ on the result and $d$. The output string is
--   $$\mathrm{comprStr}\;c\;n\;\lambda = \mathrm{descOf}\;\lambda\;\big(\mathrm{hardcode}\;\mathrm{haltProg}\;(\mathrm{encode}\,(c, n, \lambda))\big).$$
--   `frozen G U x n` is `(Vof G U x).freeze (2n+1)`, `compressedD` its compressed decider's encoding, `sampD`, `wD`, `kD` abbreviations for stage values, and `sampBound`, `wBound`, `kBound`, `fBound`, `prepBound G U s n L l` size and cost bounds (in $s$, $n$, a length bound $L$, the parameter's size $l$).
--
--   The embedded lemmas give the sizes of the data constructors and of `dWrapCore`, evaluation and scoping of the builders, `wrapBuildProg`'s run within a linear cost, and `descLam (comprStr G U c n lam) = lam`.
--
--   **Formalization Note**. The string to compress is read from $c$ rather than hardcoded as in the paper's $\mathcal{F}$; the paper's Step 2 (running $\mathcal{M}$) does not appear. `haltProg_accepts_iff` and the stage cost lemmas are theorems of the module, not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Compressor.lean; blueprint lem:halt-construction; paper recursive.tex, fig:halt_f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Compressor.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction

/-!
# The compressor's decider: the program

Obligation O4 of blueprint `rem:compression-abstract`, the program half. The compressor of the
halting reduction takes a succinct description `(c, n)` of a string `x` and returns a string
denoting the compressed verifier of *the verifier of `x` frozen at index `2n + 1`*: its
parameter is `λ(n)`, and its decider — the datum a string carries — is the program `haltProg`
below with `(c, n, λ(n))` hardcoded. This module is that program and its acceptance
agreement, `CompressorSpec.accepts_compr`; the accounting is separate.

The decider is the paper's machine `𝓕` (`recursive.tex`, `fig:halt_f`) with the recursion
removed: the paper's `𝓕` hardcodes its own description and compresses the verifier it is the
decider of, while here the string to compress is *read* from the description `c` by bit
queries — the reading is what the compressibility criterion's succinct descriptions make
possible — and the verifier compressed is the string's own, frozen. The paper's Step 2, running
`𝓜` for `n` steps, is the criterion's business and does not appear.

The program `prepProg G U` does everything but the last step, and always halts on a succinct
description:

1. `readProg U.univ`: read `x` from `c` by bit queries `0, 1, 2, …` through the universal
   machine, stopping at the out-of-range marker of `bitQueryAnswer`;
2. `parseProg`, then the two projections and `normBinProg`: the parameter `encode (descLam x)`
   and the decider datum `descDecD x`;
3. `G.samplerProg.code`: the encoded sampler program `sampData G x`;
4. `wrapBuildProg U.univ`: the encoded wrapped decider `decProgData G U x`, which is
   `encode (Vof G U x).decider.prog`;
5. `freezeBuildProg` twice at index `2n + 1`: the encoded programs of the frozen verifier;
6. `G.compress.code` on `((frozen sampler, frozen decider), λ(n))`: the encoded compressed
   decider.

Then `haltProg G U` runs it through the universal machine on the decider's own input, and
returns what the universal machine does. Forward runs of each stage compose to a forward run
of `haltProg`; the inversion (`haltProg_runs_inv`) is three `cases` and determinism, the
preparation being a single closed program with an unconditional run, and gives the acceptance
agreement `haltProg_accepts_iff`.

Every stage carries an explicit cost, in the sizes of what it is handed, so that the accounting
can be done from these lemmas alone.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

open Data

/-! ## Reading a string from its succinct description

`readProg univ` on `encode c`: loop over `i = 0, 1, 2, …`, running `univ` on
`cons (encode c) (encode i)`, until the answer is the out-of-range marker `ofNat 2`; the bits
answered are accumulated in reverse and reversed at the end. On a succinct description of `x`
the answers are `bitQueryAnswer x i`, so the result is `encode x`.

The loop state is `cons cD (cons iD acc)`: the description, the index in binary, and the bits
read so far, most recent first. -/

/-- The body of the reading loop. After taking the state apart (`cD` at `2`, `iD` at `0`,
`acc` at `1`), it runs `univ` on `cons cD iD`. The answer `nil` is the bit `false`,
`cons nil nil` the bit `true`, and anything else — the marker `ofNat 2 = cons nil (cons nil nil)`
— stops the loop with the accumulator. On a bit, the index is incremented with `incProg` and the
bit pushed onto the accumulator. -/
def readTail : Prog :=
  .elim 0
    -- answer `nil`: the bit `false`
    (.let_ (callVar 2 incProg)
      (.cons (.cons .nil .nil) (.cons (.var 5) (.cons (.var 0) (.cons .nil (.var 4))))))
    (.elim 1
      -- answer `cons a nil`: the bit `true`
      (.let_ (callVar 4 incProg)
        (.cons (.cons .nil .nil)
          (.cons (.var 7) (.cons (.var 0) (.cons (.cons .nil .nil) (.var 6))))))
      -- anything else: the marker, stop with the accumulator
      (.cons .nil (.var 7)))

def readBody (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 1 .nil
    (.let_ (.cons (.var 2) (.var 0))
      (.let_ (callVar 0 univ) readTail)))

/-- `readProg univ` on `encode c`: the loop from the state `cons (encode c) (cons nil nil)`
— index `0`, nothing read — followed by the reversal of the accumulator. -/
def readProg (univ : Prog) : Prog :=
  .let_ (.cons (.var 0) (.cons .nil .nil)) (.let_ (.loop (readBody univ)) revProg)

section Read

variable {univ : Prog} (cD : Data)

/-- The state of the reading loop after `i` bits of `x` have been read. -/
def readState (x : BitStr) (i : ℕ) : Data :=
  .cons cD (.cons (encode i) (encode (x.take i).reverse))

/-- The environment after the body has taken the state apart and queried the description. -/
def readEnv (iD acc ans : Data) : Env :=
  [ans, .cons cD iD, iD, acc, cD, .cons iD acc, .cons cD (.cons iD acc)]

end Read

/-- The cost of one iteration of the reading loop on a succinct description at parameter `n`
of a string of length at most `L`, with the description of size `s`: the universal machine's
overhead on a bit query, plus the bookkeeping. -/
noncomputable def readIter (U : UniversalMachine) (s n L : ℕ) : ℕ :=
  U.bound.eval (s + (4 * Nat.size L + 1) + (n + 1) * (Nat.size L + 1) ^ 2) +
    3 * s + 4 * (4 * Nat.size L + 1) + (4 * L + 1) +
    2 * ((Nat.size L + 2) * (8 * (4 * Nat.size L + 1) + 8 * Nat.size L + 60)) + 30

/-! ## Building descriptions of programs

The compressor's decider has to assemble the *descriptions* of the wrapped decider and of the
two frozen programs: `Prog.ProgD.dWrapCore` and `dFreeze` below, at the level of data, with the
sampler program and the string's decider as holes. The programs that build them are the same
trees with `cons`/`const` in place of the constructors — `pK`, `pC`, `pL`, `pE` mirror
`ProgD.dK`, `dC`, `dL`, `dE` — and their cost is the size of what they build plus one per hole
read. -/

namespace ProgD

/-- The description of the frozen program `freezeProg k p`, at the level of data. -/
def dFreeze (kD p : Data) : Data := dL (dE 0 dNil (dC (dK kD) (dV 1))) p

/-! The sizes of the constructors' descriptions. -/

theorem size_dV (i : ℕ) : (dV i).size = 2 * i + 3 := by simp [dV]; omega
theorem size_dNil : dNil.size = 5 := by simp [dNil]
theorem size_dK (d : Data) : (dK d).size = d.size + 14 := by simp [dK]; omega
theorem size_dC (a b : Data) : (dC a b).size = a.size + b.size + 7 := by simp [dC]; omega
theorem size_dL (a b : Data) : (dL a b).size = a.size + b.size + 11 := by simp [dL]; omega
theorem size_dE (i : ℕ) (a b : Data) : (dE i a b).size = a.size + b.size + 2 * i + 11 := by
  simp [dE]; omega

/-- The size of the wrapper's description: the two holes, the universal machine twice, and a
fixed number of nodes. -/
def wrapNodes : ℕ :=
  2 * (encode Prog.lenProg : Data).size + 2 * (encode Prog.eqBitsProg : Data).size +
    (encode Prog.toUnaryProg : Data).size + (encode CL.Sampler.Query.dimension : Data).size + 475

theorem size_dWrapCore (univD sampD decD : Data) :
    (dWrapCore univD sampD decD).size = sampD.size + decD.size + 2 * univD.size + wrapNodes := by
  unfold dWrapCore dWrapHead dWrapCheck dWrapTail
  simp only [size_dE, size_dL, size_dC, size_dK, size_dV, size_dNil]
  unfold wrapNodes
  omega

end ProgD

open ProgD

/-- `cons (const 6) e`: builds `dK`. -/
def pK (e : Prog) : Prog := .cons (.const (.ofNat 6)) e
/-- Builds `dC`. -/
def pC (h t : Prog) : Prog := .cons (.const (.ofNat 2)) (.cons h t)
/-- Builds `dL`. -/
def pL (e b : Prog) : Prog := .cons (.const (.ofNat 4)) (.cons e b)
/-- Builds `dE i`. -/
def pE (i : ℕ) (n c : Prog) : Prog :=
  .cons (.const (.ofNat 3)) (.cons (.const (.ofNat i)) (.cons n c))

section Build

variable {env : Env}

theorem pK_eval {e : Prog} {v : Data} {s : ℕ} (h : Eval env e v s) :
    Eval env (pK e) (dK v) (s + 14) :=
  (Eval.cons (Eval.const _ _) h).cast_cost (by simp [Data.size_ofNat]; omega)

theorem pC_eval {h t : Prog} {a b : Data} {s u : ℕ} (h₁ : Eval env h a s) (h₂ : Eval env t b u) :
    Eval env (pC h t) (dC a b) (s + u + 7) :=
  (Eval.cons (Eval.const _ _) (Eval.cons h₁ h₂)).cast_cost (by simp [Data.size_ofNat]; omega)

theorem pL_eval {e b : Prog} {a c : Data} {s u : ℕ} (h₁ : Eval env e a s) (h₂ : Eval env b c u) :
    Eval env (pL e b) (dL a c) (s + u + 11) :=
  (Eval.cons (Eval.const _ _) (Eval.cons h₁ h₂)).cast_cost (by simp [Data.size_ofNat]; omega)

theorem pE_eval (i : ℕ) {n c : Prog} {a b : Data} {s u : ℕ} (h₁ : Eval env n a s)
    (h₂ : Eval env c b u) : Eval env (pE i n c) (dE i a b) (s + u + 2 * i + 11) :=
  (Eval.cons (Eval.const _ _) (Eval.cons (Eval.const _ _) (Eval.cons h₁ h₂))).cast_cost
    (by simp [Data.size_ofNat]; omega)

end Build

theorem pK_wellScoped {n : ℕ} {e : Prog} (h : e.WellScoped n) : (pK e).WellScoped n := ⟨trivial, h⟩
theorem pC_wellScoped {n : ℕ} {h t : Prog} (h₁ : h.WellScoped n) (h₂ : t.WellScoped n) :
    (pC h t).WellScoped n := ⟨trivial, h₁, h₂⟩
theorem pL_wellScoped {n : ℕ} {e b : Prog} (h₁ : e.WellScoped n) (h₂ : b.WellScoped n) :
    (pL e b).WellScoped n := ⟨trivial, h₁, h₂⟩
theorem pE_wellScoped {n i : ℕ} {e b : Prog} (h₁ : e.WellScoped n) (h₂ : b.WellScoped n) :
    (pE i e b).WellScoped n := ⟨trivial, trivial, h₁, h₂⟩

/-- One length check of the wrapper, as a builder with the continuation as a hole. -/
def pCheck (i j : ℕ) (c : Prog) : Prog :=
  pL (.const (dL (dV i) (encode Prog.lenProg)))
    (pL (.const (dC (dV 0) (dV (j + 1))))
      (pL (.const (dL (dV 0) (encode Prog.eqBitsProg))) (pE 0 (.const dNil) c)))

theorem pCheck_eval {env : Env} (i j : ℕ) {c : Prog} {v : Data} {s : ℕ} (h : Eval env c v s) :
    Eval env (pCheck i j c) (dWrapCheck i j v)
      (s + (dL (dV i) (encode Prog.lenProg)).size + (dC (dV 0) (dV (j + 1))).size +
        (dL (dV 0) (encode Prog.eqBitsProg)).size + dNil.size + 44) :=
  (pL_eval (Eval.const _ (dL (dV i) (encode Prog.lenProg)))
    (pL_eval (Eval.const _ (dC (dV 0) (dV (j + 1))))
      (pL_eval (Eval.const _ (dL (dV 0) (encode Prog.eqBitsProg)))
        (pE_eval 0 (Eval.const _ dNil) h)))).cast_cost (by omega)

theorem pCheck_wellScoped {n i j : ℕ} {c : Prog} (h : c.WellScoped n) :
    (pCheck i j c).WellScoped n :=
  pL_wellScoped trivial (pL_wellScoped trivial (pL_wellScoped trivial
    (pE_wellScoped trivial h)))

/-- **The wrapper's description, built.** On `cons sampD decD`, the description
`dWrapCore univD sampD decD` of the wrapped decider. -/
def wrapBuildProg (univD : Data) : Prog :=
  .elim 0 .nil
    (pE 0 (.const dNil)
      (pL (pC (pK (.var 0)) (.const (dC (dV 0) (dK (encode CL.Sampler.Query.dimension)))))
        (pL (.const (dL (dV 0) univD))
          (pL (.const (dL (dV 0) (encode Prog.toUnaryProg)))
            (pE 4 (.const dNil) (pE 1 (.const dNil)
              (pCheck 2 4 (pCheck 5 9
                (pL (pC (pK (.var 1)) (.const (dV 19))) (.const (dL (dV 0) univD)))))))))))

theorem wrapBuildProg_wellScoped (univD : Data) : (wrapBuildProg univD).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, pE_wellScoped trivial (pL_wellScoped
    (pC_wellScoped (pK_wellScoped (by simp [WellScoped])) trivial)
    (pL_wellScoped trivial (pL_wellScoped trivial (pE_wellScoped trivial (pE_wellScoped trivial
      (pCheck_wellScoped (pCheck_wellScoped (pL_wellScoped
        (pC_wellScoped (pK_wellScoped (by simp [WellScoped])) trivial) trivial))))))))⟩

/-- The builder builds the wrapper's description, at a cost linear in the sizes involved. -/
theorem wrapBuildProg_runs (univD sampD decD : Data) :
    ∃ t ≤ sampD.size + decD.size + 2 * univD.size + wrapNodes + 3,
      (wrapBuildProg univD).Runs (.cons sampD decD) (dWrapCore univD sampD decD) t := by
  have run := Eval.elim_cons (env := [Data.cons sampD decD]) (i := 0) (n := .nil)
    (a := sampD) (b := decD) (by simp)
    (pE_eval 0 (Eval.const _ dNil)
      (pL_eval (pC_eval (pK_eval (Eval.var_of_get (i := 0) (v := sampD) (by simp)))
          (Eval.const _ (dC (dV 0) (dK (encode CL.Sampler.Query.dimension)))))
        (pL_eval (Eval.const _ (dL (dV 0) univD))
          (pL_eval (Eval.const _ (dL (dV 0) (encode Prog.toUnaryProg)))
            (pE_eval 4 (Eval.const _ dNil) (pE_eval 1 (Eval.const _ dNil)
              (pCheck_eval 2 4 (pCheck_eval 5 9
                (pL_eval (pC_eval (pK_eval (Eval.var_of_get (i := 1) (v := decD) (by simp)))
                  (Eval.const _ (dV 19))) (Eval.const _ (dL (dV 0) univD)))))))))))
  refine ⟨_, ?_, run⟩
  simp only [size_dL, size_dC, size_dK, size_dV, size_dNil]
  unfold wrapNodes
  omega

/-- **The frozen program's description, built.** On `cons kD p`, the description
`dFreeze kD p`. -/
def freezeBuildProg : Prog :=
  .elim 0 .nil (pL (pE 0 (.const dNil) (pC (pK (.var 0)) (.const (dV 1)))) (.var 1))

/-! ## Small pieces -/

/-- A pair of two variables, then a closed program on it. -/
def call2 (i j : ℕ) (q : Prog) : Prog := .let_ (.cons (.var i) (.var j)) q

end Cost.Prog

namespace Halting

open Cost Cost.Prog Cost.Prog.ProgD

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The preparation: from `(c, n, λ)` to the compressed decider's description -/

/-- Everything the compressor's decider does before running the compressed decider: on
`encode (c, n, λ)`, the description of `Compress` applied to the verifier of the string `c`
describes, frozen at `2n + 1`, and to `λ`. The stages are those of the module docstring; the
comments give the environment after each. -/
def prepProg : Prog :=
  .elim 0 .nil (.elim 1 .nil                      -- [nD, lamD, cD, cons nD lamD, input]
    (.let_ (callVar 2 (readProg U.univ))          -- [xD, nD, lamD, cD, …]
      (.let_ (callVar 0 parseProg)                -- [pD, xD, nD, lamD, cD, …]
        (.let_ (callVar 0 sndProg)                -- [decD, pD, xD, nD, lamD, cD, …]
          (.let_ (callVar 1 fstProg)              -- [lamDx, decD, pD, xD, nD, lamD, cD, …]
            (.let_ (callVar 0 normBinProg)        -- [nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
              (.let_ (callVar 0 G.samplerProg.code)
                                                  -- [sampD, nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
                (.let_ (call2 0 3 (wrapBuildProg (encode U.univ)))
                                                  -- [wD, sampD, nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
                  (.let_ (.cons (.cons .nil .nil) (.var 7))
                                                  -- [kD, wD, sampD, nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
                    (.let_ (call2 0 2 freezeBuildProg)
                                                  -- [fsD, kD, wD, sampD, …]
                      (.let_ (call2 1 2 freezeBuildProg)
                                                  -- [fdD, fsD, kD, wD, sampD, nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
                        (.let_ (.cons (.cons (.var 1) (.var 0)) (.var 11))
                          (callVar 0 G.compress.code)))))))))))))

/-- The frozen verifier of the string `x`, at index `2n + 1`. -/
abbrev frozen (x : BitStr) (n : ℕ) : Verifier 7 := (Vof G U x).freeze (2 * n + 1)

/-- The description of the compressed decider the preparation produces. -/
def compressedD (x : BitStr) (n lam : ℕ) : Data :=
  encode (G.compress (((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog), lam))

/-- The values of the stages, named. `sampD` is `sampData G x`, `wD` is `decProgData G U x`
and `kD n` is `encode (2n + 1)` (`Cost.encode_two_mul_add_one`); they are `abbrev`s so that
the environment bookkeeping below sees through them. -/
abbrev sampD (x : BitStr) : Data := encode (G.samplerProg (descLam x))
abbrev wD (x : BitStr) : Data := dWrapCore (encode U.univ) (sampD G x) (Data.parse x).right
abbrev kD (n : ℕ) : Data := .cons (.cons .nil .nil) (encode n)

/-! The sizes of the stages' values, bounded in the length `L` of the described string and the
level `n`: the sampler program (`sampBound`, by its own time bound at a parameter of size at
most `L + 1`), the wrapped decider (`wBound`), the frozen index (`kBound`) and the two frozen
programs together (`fBound`). -/

/-- The size of the sampler program at a parameter of size at most `L + 1`. -/
noncomputable def sampBound (L : ℕ) : ℕ := G.samplerProg.timeBound.eval (L + 1)
/-- The size of the wrapped decider's description. -/
noncomputable def wBound (L : ℕ) : ℕ := sampBound G L + (L + 1) + 2 * esize U.univ + wrapNodes
/-- The size of `encode (2n + 1)`. -/
def kBound (n : ℕ) : ℕ := 4 * Nat.size n + 5
/-- The sizes of the two frozen programs, summed. -/
noncomputable def fBound (L n : ℕ) : ℕ :=
  sampBound G L + kBound n + 53 + (wBound G U L + kBound n + 53)

/-- The cost of the preparation, in the description's size `s`, the level `n`, a bound `L` on
the described string's length, and the size `l` of the parameter. -/
noncomputable def prepBound (s n L l : ℕ) : ℕ :=
  (L + 1) * (readIter U s n L + 1) + (L + 2) * (4 * L + 14) + s + 7 +      -- reading
    (L + 2) * (4 * L + 1 + 2 * L + 25) + (4 * L + 1) +                     -- parsing
    (L + 3) * (L + 26) + 3 * (L + 1) + 10 +                                -- normalization
    sampBound G L + wBound G U L + fBound G U L n +
      G.compress.timeBound.eval (fBound G U L n + l + 2) +                  -- the three programs
    2 * s + 4 * (4 * L + 1) + 12 * (L + 1) + 2 * sampBound G L + 3 * wBound G U L +
      6 * kBound n + 2 * fBound G U L n + 2 * l + 200

/-! ## The decider -/

/-- **The compressor's decider**, before hardcoding. On `cons P d` with `P = encode (c, n, λ)`
and `d` the decider's own input `encode (m, x', y', a, b)`: prepare the description of the
compressed decider, and run it on `d` through the universal machine; the result is the
universal machine's. -/
def haltProg : Prog :=
  .elim 0 .nil                                   -- [P, d, input]
    (.let_ (callVar 0 (prepProg G U))            -- [cmpD, P, d, input]
      (.let_ (.cons (.var 0) (.var 2))           -- [cons cmpD d, cmpD, P, d, input]
        (callVar 0 U.univ)))

/-! ## The compressor's output, as a string -/

/-- **The string the compressor outputs** on `(c, n)` at parameter `λ`: it denotes `λ` and the
decider `haltProg` with `(c, n, λ)` hardcoded. -/
def comprStr (c : Prog) (n lam : ℕ) : BitStr :=
  descOf lam (hardcode (haltProg G U) (encode (c, n, lam)))

@[simp] theorem descLam_comprStr (c : Prog) (n lam : ℕ) : descLam (comprStr G U c n lam) = lam :=
  descLam_descOf _ _

end Halting

end MIPRE


