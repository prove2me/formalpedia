-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_CompressorProgram
-- name    : MIPRE_Foundations_Halting_CompressorProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:03:10.059134+00:00
-- url     : https://prove2.me/theorems/d6dc33cc-96cd-4a22-9b61-809ce67f39ed
-- title:
--   The compressor as a polynomial-time function of the ambient model
-- statement:
--   The last piece of obligation O4: the map $(c, n) \mapsto \mathrm{comprStr}\,c\,n\,\lambda(n)$ as a polynomial-time function, from which `exists_compressorSpec` (a theorem of the module, not in this bundle) obtains a `CompressorSpec`, hence `Obligations`, hence the halting reduction with no hypothesis but gap-preserving compression. Fix $G : \mathrm{GapCompression}$ and $U : \mathrm{UniversalMachine}$.
--
--   `MIPRE.Cost.Prog.lamProg` computes the parameter in binary: on `encode n` it returns `encode (2 ^ (2 * Nat.size n))`, by two walks over the bits of $n$ with `lenBody`, each prepending a $\mathtt{nil}$ per bit to the accumulator, starting from the numeral $1$. `MIPRE.Halting.comprProg G U` is the compressor: on `encode (c, n)` it computes $\lambda(n)$ with `lamProg`, assembles the triple $(c, n, \lambda(n))$, hardcodes it into `haltProg G U` with `smnProg`, pairs $\lambda(n)$ with the resulting decider and serializes the pair with `serProg`. `MIPRE.Halting.comprPoly G U : PolyTimeFun (Prog × ℕ) BitStr` packages it: its function is `fun p => comprStr G U p.1 p.2 (lamOf p.2)`, its code `comprProg G U`, and its time bound the polynomial
--   $$20000\,\big(X + \mathrm{esize}(\mathrm{haltProg}\;G\;U) + 62\big)^2 .$$
--
--   The embedded lemmas are `bits_two_pow` (the bits of $2^e$ are $e$ zeros then a one), `encode_two_pow_list` (`encode (2 ^ e)` is $e$ copies of $\mathtt{nil}$ in front of the numeral $1$), the well-scopedness of `lamProg` and `comprProg`, `lamProg_runs` (within $50(\mathrm{esize}\,n + 5)^2$), `smn_outDec` (the description `smnProg` builds is `encode (outDec G U c n lam)`), `comprProg_runs` (`comprProg G U` on `encode (c, n)` returns `encode (comprStr G U c n (lamOf n))` within $20000(\mathrm{esize}(c, n) + \mathrm{esize}(\mathrm{haltProg}\,G\,U) + 62)^2$) and `comprPoly_apply` (`comprPoly G U (c, n) = comprStr G U c n (lamOf n)`).
--
--   **Formalization Note**. Every stage is linear or quadratic in its input, so the whole is quadratic in $|c| + |n|$; the constant $20000$ is a generous bound. `comprPoly` is `noncomputable` (its `timeBound` is a `Polynomial ℕ`); its `computes` field is the content of `comprProg_runs`, and it is what instantiates the `PolyTimeFun` fields `Obligations.compr` and `CompressorSpec.compr`. The parameter is `lamOf` of `CompressorCost.lean`, the output string `comprStr` of `Compressor.lean`; `comprProg` is a literal program over `callVar`, `smnProg`, `serProg` and the constant `encode (haltProg G U)`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/CompressorProgram.lean; blueprint lem:lambda

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/CompressorProgram.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Halting_CompressorCost

/-!
# The compressor as a program, and the halting reduction from compression alone

The last piece of obligation O4: the map `(c, n) ↦ comprStr c n (λ(n))` as a polynomial-time
function of the ambient model (`comprPoly`), which `exists_compressorSpec` turns into a
`CompressorSpec`, hence into `Obligations`, hence — through `halting_reduction` — into the
halting reduction with **no hypothesis but gap-preserving compression**: `halting_reduction_of`
in `val*`, and `halting_reduces_to_gameValue_of` in the headline's `gameValue`.

The program writes `λ(n) = 2 ^ (2 · size n)` in binary by walking the bits of `n` twice with
`lenBody`, prepending a `0` per bit to the numeral `1` (`lamProg`); assembles `(c, n, λ(n))`;
hardcodes it into `haltProg` with `smnProg`; pairs the parameter with the result; and serializes
the pair with `serProg`. Every stage is linear or quadratic in its input, so the whole is
quadratic in `|c| + |n|`.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

open Data

/-! ## The parameter in binary -/

/-- The bits of `2 ^ e`: `e` zeros then a one. -/
theorem bits_two_pow (e : ℕ) : (2 ^ e).bits = List.replicate e false ++ [true] := by
  have hval : ∀ e, (List.replicate e false ++ [true]).foldr Nat.bit 0 = 2 ^ e := by
    intro e
    induction e with
    | zero => rfl
    | succ e ih =>
      rw [List.replicate_succ, List.cons_append, List.foldr_cons, ih, Nat.bit_false, pow_succ]
      ring
  have hcanon : List.replicate e false ++ [true] = [] ∨
      (List.replicate e false ++ [true]).getLast? = some true := Or.inr (by simp)
  rw [← hval e, bits_foldr_of_canon _ hcanon]

/-- `encode (2 ^ e)`, as a list of `e` `nil`s in front of the numeral `1`. -/
theorem encode_two_pow_list (e : ℕ) :
    (encode (2 ^ e) : Data) = Data.list (List.replicate e .nil ++ [.cons .nil .nil]) := by
  show (encode (2 ^ e).bits : Data) = _
  rw [bits_two_pow, encode_bitStr_eq_list, List.map_append, List.map_replicate]
  rfl

/-- `lamProg` on `encode n` computes `encode (2 ^ (2 · size n))`: two walks over the bits of
`n`, each prepending a `nil` per bit to the accumulator, from the numeral `1`. -/
def lamProg : Prog :=
  .let_ (.cons (.var 0) (.const (.cons (.cons .nil .nil) .nil)))
    (.let_ (.loop lenBody)
      (.let_ (.cons (.var 2) (.var 0)) (.loop lenBody)))

theorem lamProg_wellScoped : lamProg.WellScoped 1 := by
  simp [lamProg, WellScoped, lenBody]

theorem lamProg_runs (n : ℕ) :
    ∃ t ≤ 50 * (esize n + 5) ^ 2,
      lamProg.Runs (encode n) (encode (2 ^ (2 * Nat.size n))) t := by
  set l : List Data := n.bits.map Data.ofBool with hl
  have hen : (encode n : Data) = Data.list l := by
    show (encode n.bits : Data) = _; rw [encode_bitStr_eq_list]
  have hlen : l.length = Nat.size n := by rw [hl, List.length_map, Nat.size_eq_bits_len]
  have hsz : (Data.list l).size = esize n := by rw [← hen]; rfl
  have hsn : Nat.size n ≤ esize n := size_le_esize_nat n
  have hacc : ∀ k, (Data.list (List.replicate k .nil ++ [.cons .nil .nil])).size = 2 * k + 5 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append, Data.size_list_cons, ih]
      simp only [Data.size_nil]; omega
  -- the first walk
  obtain ⟨t₁, ht₁, h₁⟩ := lenLoop_runs l [.cons .nil .nil] [Data.list l] (esize n + 5 + 2 * esize n)
    (by simp only [Data.list_cons, Data.list_nil, Data.size_cons, Data.size_nil, hsz]; omega)
  -- the second walk, from the first's result
  obtain ⟨t₂, ht₂, h₂⟩ := lenLoop_runs l (List.replicate l.length .nil ++ [.cons .nil .nil])
    [Data.list (List.replicate l.length .nil ++ [.cons .nil .nil]), Data.cons (Data.list l)
      (.cons (.cons .nil .nil) .nil), Data.list l] (esize n + (2 * esize n + 5) + 2 * esize n)
    (by rw [hacc, hsz, hlen]; omega)
  -- the result is `encode (2 ^ (2 · size n))`
  have hres : Data.list (List.replicate l.length .nil ++
      (List.replicate l.length .nil ++ [.cons .nil .nil])) = encode (2 ^ (2 * Nat.size n)) := by
    rw [encode_two_pow_list, ← List.append_assoc, ← List.replicate_add, hlen, Nat.two_mul]
  rw [hres] at h₂
  have hstate : Data.cons (Data.list l) (Data.list [.cons .nil .nil]) =
      Data.cons (Data.list l) (.cons (.cons .nil .nil) .nil) := rfl
  rw [hstate] at h₁
  rw [hen]
  refine ⟨_, ?_, Eval.let_ (Eval.cons (Eval.var_of_get (env := [Data.list l]) (i := 0)
      (v := Data.list l) (by simp)) (Eval.const _ _))
    (Eval.let_ h₁
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := Data.list l) (by simp))
          (Eval.var_of_get (i := 0)
            (v := Data.list (List.replicate l.length .nil ++ [.cons .nil .nil])) (by simp)))
        h₂))⟩
  -- the arithmetic
  rw [hlen] at ht₁ ht₂
  have h1 : (Nat.size n + 1) * (esize n + 5 + 2 * esize n + 13) ≤ (esize n + 1) * (3 * esize n + 18) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (Nat.size n + 1) * (esize n + (2 * esize n + 5) + 2 * esize n + 13) ≤
      (esize n + 1) * (5 * esize n + 18) := Nat.mul_le_mul (by omega) (by omega)
  simp only [Data.size_cons, Data.size_nil, hsz, hacc, hlen]
  nlinarith

end Cost.Prog

namespace Halting

open Cost Cost.Prog

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The compressor's program -/

/-- The compressor: on `encode (c, n)`, the parameter in binary, the triple `(c, n, λ(n))`,
its hardcoding into `haltProg` (`smnProg`), the pair `(λ(n), decider)`, and its serialization. -/
def comprProg : Prog :=
  .elim 0 .nil                                            -- [cD, nD, input]
    (.let_ (callVar 1 lamProg)                            -- [lamD, cD, nD, input]
      (.let_ (.cons (.var 1) (.cons (.var 2) (.var 0)))    -- [P, lamD, cD, nD, input]
        (.let_ (.let_ (.cons (.const (encode (haltProg G U))) (.var 0)) smnProg)
                                                          -- [H, P, lamD, cD, nD, input]
          (.let_ (.cons (.var 2) (.var 0)) serProg))))    -- serProg on `cons lamD H`

theorem comprProg_wellScoped : (comprProg G U).WellScoped 1 := by
  refine ⟨Nat.zero_lt_one, trivial, callVar_wellScoped (by decide) lamProg_wellScoped, ?_⟩
  refine ⟨by simp [WellScoped], ?_⟩
  refine ⟨⟨⟨trivial, by simp [WellScoped]⟩, smnProg_wellScoped.mono (by omega) _⟩, ?_⟩
  exact ⟨by simp [WellScoped], serProg_wellScoped.mono (by omega) _⟩

/-- The description of the hardcoded decider, as `smnProg` builds it. -/
theorem smn_outDec (c : Prog) (n lam : ℕ) :
    Data.cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) (encode (c, n, lam)))
      (.cons .nil .nil))) (encode (haltProg G U))) = encode (outDec G U c n lam) :=
  (toData_hardcode _ _).symm

/-- **The compressor computes its output.** -/
theorem comprProg_runs (c : Prog) (n : ℕ) :
    ∃ t ≤ 20000 * (esize (c, n) + esize (haltProg G U) + 62) ^ 2,
      (comprProg G U).Runs (encode (c, n)) (encode (comprStr G U c n (lamOf n))) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := lamProg_runs n
  have hlam : (encode (2 ^ (2 * Nat.size n)) : Data) = encode (lamOf n) := rfl
  rw [hlam] at h₁
  have h₂ := smnProg_runs (encode (haltProg G U)) (encode (c, n, lamOf n))
  rw [smn_outDec] at h₂
  obtain ⟨t₃, ht₃, h₃⟩ := serProg_runs (.cons (encode (lamOf n)) (encode (outDec G U c n (lamOf n))))
  have hP : (Data.cons (encode c) (.cons (encode n) (encode (lamOf n))) : Data) =
      encode (c, n, lamOf n) := rfl
  have hout : (encode (Data.cons (encode (lamOf n)) (encode (outDec G U c n (lamOf n)))).toBitsPost
      : Data) = encode (comprStr G U c n (lamOf n)) := rfl
  rw [hout] at h₃
  refine ⟨_, ?_, Eval.elim_cons (env := [encode (c, n)]) (i := 0) (a := encode c) (b := encode n)
      (by simp; rfl)
    (Eval.let_ (callVar_eval lamProg_wellScoped (i := 1) (v := encode n) (by simp) h₁)
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := encode c) (by simp))
          (Eval.cons (Eval.var_of_get (i := 2) (v := encode n) (by simp))
            (Eval.var_of_get (i := 0) (v := encode (lamOf n)) (by simp))))
        (Eval.let_ (Eval.let_ (Eval.cons (Eval.const _ (encode (haltProg G U)))
              (Eval.var_of_get (i := 0) (v := encode (c, n, lamOf n))
                (by rw [Env.get_cons_zero]; rfl)))
            (Eval.append_of_wellScoped h₂ smnProg_wellScoped _))
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := encode (lamOf n)) (by simp))
              (Eval.var_of_get (i := 0) (v := encode (outDec G U c n (lamOf n))) (by simp)))
            (Eval.append_of_wellScoped h₃ serProg_wellScoped _)))))⟩
  -- the arithmetic: everything is linear in `E = |c| + |n| + |haltProg|` but the serialization,
  -- which is quadratic
  obtain ⟨E, hEdef⟩ : ∃ E, E = esize c + esize n + esize (haltProg G U) := ⟨_, rfl⟩
  have hE : esize (c, n) = esize c + esize n + 1 := rfl
  have hec : (encode c : Data).size = esize c := rfl
  have hen : (encode n : Data).size = esize n := rfl
  have hel : (encode (lamOf n) : Data).size = esize (lamOf n) := rfl
  have heh : (encode (haltProg G U) : Data).size = esize (haltProg G U) := rfl
  have hl : esize (lamOf n) ≤ 8 * Nat.size n + 5 := esize_lamOf_le n
  have hsn : Nat.size n ≤ esize n := size_le_esize_nat n
  have hP' : (encode (c, n, lamOf n) : Data).size = esize c + (esize n + esize (lamOf n) + 1) + 1 := rfl
  have hO : (encode (outDec G U c n (lamOf n)) : Data).size =
      esize (haltProg G U) + esize c + esize n + esize (lamOf n) + 37 := esize_outDec G U c n (lamOf n)
  have hD : (Data.cons (encode (lamOf n)) (encode (outDec G U c n (lamOf n)))).size ≤ 18 * E + 48 := by
    rw [Data.size_cons, hel, hO]; omega
  have ht₃' : t₃ ≤ (3 * (18 * E + 48) + 2) * (16 * (18 * E + 48) + 42) +
      ((18 * E + 48) + 2) * (5 * (18 * E + 48) + 30) :=
    ht₃.trans (Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul (by omega) (by omega)))
  have ht₃'' : t₃ ≤ 17172 * E ^ 2 + 95148 * E + 131760 := ht₃'.trans (le_of_eq (by ring))
  have ht₁' : t₁ ≤ 50 * (E + 5) ^ 2 := ht₁.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have ht₁'' : t₁ ≤ 50 * E ^ 2 + 500 * E + 1250 := ht₁'.trans (le_of_eq (by ring))
  have hsq : (esize (c, n) + esize (haltProg G U) + 62) ^ 2 = (E + 63) ^ 2 := by rw [hE]; congr 1; omega
  rw [hsq]
  have hfin : 17222 * E ^ 2 + 96000 * E + 140000 ≤ 20000 * (E + 63) ^ 2 := by nlinarith
  omega

/-- **The compressor, as a polynomial-time function.** -/
noncomputable def comprPoly : PolyTimeFun (Prog × ℕ) BitStr where
  toFun p := comprStr G U p.1 p.2 (lamOf p.2)
  code := comprProg G U
  closed := comprProg_wellScoped G U
  timeBound := Polynomial.C 20000 * (Polynomial.X + Polynomial.C (esize (haltProg G U) + 62)) ^ 2
  computes := by
    rintro ⟨c, n⟩
    obtain ⟨t, ht, h⟩ := comprProg_runs G U c n
    refine ⟨t, ?_, h⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X]
    exact ht.trans (le_of_eq (by ring))

@[simp] theorem comprPoly_apply (c : Prog) (n : ℕ) :
    comprPoly G U (c, n) = comprStr G U c n (lamOf n) := rfl

/-! ## Obligation O4, discharged -/

-- The tabulation is opaque here as in `halting_reduction`, and for the same reason.
attribute [local irreducible] MIPRE.Halting.tab

end Halting

end MIPRE


