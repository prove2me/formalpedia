-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Wrapper
-- name    : MIPRE_Foundations_Halting_Wrapper
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:37:16.55734+00:00
-- url     : https://prove2.me/theorems/7240173e-c73c-43be-9ee7-72d1d041a814
-- title:
--   Reading a string as a normal form verifier: the wrapper decider and its copy at the level of data
-- statement:
--   Let `U : UniversalMachine` (closed program `U.univ`), `S : CL.Sampler ℓ` with dimension $s(n) =$ `S.dim n`, and `decD : Data` the datum a string carries as its decider; `callVar i p` calls `p` on variable `i`.
--
--   The wrapper (`MIPRE.Cost.Prog`). `wrapCheck i j c` compares the length of the bit string at index `i` with the unary numeral at index `j` (then `c` if equal, else `nil`). `wrapTail univ decD` runs `decD` on the whole input through `univ`. `wrapHead univ sampProg c` computes the sampler's dimension in unary and continues with `c`; `wrapPre univ sampProg c` adds the splitting of the two questions, with environments `wrapCheckEnv`, `wrapPreEnv`. `wrapCore univ sampProg decD := wrapPre univ sampProg (wrapCheck 2 4 (wrapCheck 5 9 (wrapTail univ decD)))`.
--
--   `MIPRE.Decider.wrap U S decD : Decider` has program `wrapCore U.univ S.prog decD`; `MIPRE.Verifier.ofSamplerDeciderD U S decD : Verifier ℓ` has sampler `S` and decider `wrap U S decD`; `MIPRE.Verifier.ofSamplerDecider U S dec := ofSamplerDeciderD U S (encode dec)`. By `wrap_accepts`,
--
--   $$(\mathrm{wrap}\ U\ S\ d).\mathrm{Accepts}\ n\ x\ y\ a\ b \iff |x| = s(n) \wedge |y| = s(n) \wedge \exists t,\ U.\mathrm{univ}.\mathrm{Runs}\ \big(\mathtt{cons}\ d\ (\mathrm{encode}\,(n,x,y,a,b))\big)\ (\mathrm{encode}\ \mathtt{true})\ t .$$
--
--   Data-level copy (`MIPRE.Cost.Prog.ProgD`): `dV i`, `dNil`, `dC h t`, `dE i n c`, `dL e b`, `dK d` encode `var`, `nil`, `cons`, `elim`, `let_`, `const` (tags $0,1,2,3,4,6$); `dWrapCheck`, `dWrapTail`, `dWrapHead`, `dWrapCore` rebuild the wrapper: `dWrapCore (encode univ) (encode sampProg) decD = encode (wrapCore univ sampProg decD)` (`dWrapCore_eq`).
--
--   Lemmas: `_wellScoped` for each piece; the forward runs (`wrapCheck_runs_of_eq`, `wrapCheck_runs_of_ne`, `wrapPre_runs`, `wrapCore_runs_of_eq`, `wrapCore_runs_of_ne_left`, `wrapCore_runs_of_ne_right`) and inversions (`wrapCheck_inv`, `wrapPre_inv`, `wrapCore_halts_inv`); `wrap_prog`, `wrap_accepts`, `wrap_accepts_length`, the two `_sampler` equations, five private helper runs, and `Primrec` lemmas for the `ProgD` definitions.
--
--   **Formalization Note**. The decider is a datum run by the universal machine, not a program, so every pair denotes a verifier; on the encoding of a program the two readings agree (`wrap_accepts_prog`, elsewhere). Only the question-length check is enforced: synchronicity and the answer-length bound are class conditions, and a non-halting decider fails $n$-boundedness. `ProgD` has no docstrings.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Wrapper.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Wrapper.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
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
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic

/-!
# Reading a string as a normal form verifier: the wrapper decider

Blueprint `rem:compression-abstract`, item 1: a string of the compressibility criterion is a
pair `(λ, 𝒟)` of a parameter and a decider program, read as the verifier
`(S^compr_λ, wrap 𝒟)`. The wrapper is what makes the pair a *normal form* verifier: the one
structural requirement of `def:normal-verifier` is `Verifier.accepts_length`, that the decider
accept only questions of the sampler's dimension — the paper's step 1, "compute the dimension
`s(n)` of the sampler and check `|x| = |y| = s(n)`; if not, reject".

Nothing else has to be enforced. Synchronicity at an index and the answer-length bound are
conditions on *membership in the classes* (`Verifier.InClassA`, `InClassB`), not on
well-formedness, so the wrapper leaves them to the class definition; and the paper's timeout
counter is likewise not needed here, since a decider that fails to halt simply fails to be
`n`-bounded, and its string then lies in neither class.

* `Prog.wrapCore univ sampProg dec`: on input `(N, x, y, a, b)`, run `sampProg` on
  `(N, dimension)` through the universal machine `univ`, convert the dimension to unary, compare
  it with the lengths of `x` and of `y`, and run `dec` on the whole input through `univ` if both
  match, rejecting otherwise.
* The three forward runs (`wrapCore_runs_of_eq`, `wrapCore_runs_of_ne_left`,
  `wrapCore_runs_of_ne_right`) and the inversion `wrapCore_halts_of`, which is what turns them
  into the characterization of acceptance.
* `Decider.wrap`, `Decider.wrap_accepts`, and `Verifier.ofSamplerDeciderD`, the normal form
  verifier a pair denotes. The decider component is a *datum* run by the universal machine,
  not a program: a string carries data, a datum that is not the encoding of any program still
  has to name a verifier, and reading it as a program would need a decoder with a fallback
  (once `Cost.progNorm`, in a module since removed) that the compressor's decider of
  obligation O4 would then have to reimplement in the ambient model — its tree-grammar check
  as a worklist program — only to reproduce a fallback nobody wanted. On the encoding of a program the two
  readings agree (`wrap_accepts_prog`, by `UniversalMachine.time_le` and `halts_of`), and
  `Verifier.ofSamplerDecider` is that special case, which the two distinguished strings use.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

open Data

/-! ## The program -/

/-- One length check, reusable for both questions: read the length of the bit string at index
`i`, compare it with the unary numeral at index `j`, and continue with `c` if they agree,
rejecting otherwise. -/
def wrapCheck (i j : ℕ) (c : Prog) : Prog :=
  .let_ (callVar i lenProg)
    (.let_ (.cons (.var 0) (.var (j + 1)))
      (.let_ (callVar 0 eqBitsProg)
        (.elim 0 .nil c)))

/-- The environment `wrapCheck` hands to its continuation. -/
def wrapCheckEnv (l : BitStr) (m : ℕ) (env : Env) : Env :=
  .nil :: .nil :: encode true :: .cons (Data.ofNat l.length) (Data.ofNat m) ::
    Data.ofNat l.length :: env

/-- The last step: run the string's decider — the datum `decD`, which the string carries and
which need not be the encoding of any program — on the whole input, through `univ`. At this
point the input sits at index `19`. -/
def wrapTail (univ : Prog) (decD : Data) : Prog :=
  .let_ (.cons (.const decD) (.var 19)) (callVar 0 univ)

/-- The head: compute the sampler's dimension at the input index, in unary. -/
def wrapHead (univ sampProg c : Prog) : Prog :=
  .elim 0 .nil
    (.let_ (.cons (.const (encode sampProg))
        (.cons (.var 0) (.const (encode CL.Sampler.Query.dimension))))
      (.let_ (callVar 0 univ)
        (.let_ (callVar 0 toUnaryProg) c)))

/-- The prefix: the head, then the two questions taken apart. -/
def wrapPre (univ sampProg c : Prog) : Prog :=
  wrapHead univ sampProg (.elim 4 .nil (.elim 1 .nil c))

/-- The wrapper's program. Input: `encode (N, x, y, a, b)`. -/
def wrapCore (univ sampProg : Prog) (decD : Data) : Prog :=
  wrapPre univ sampProg (wrapCheck 2 4 (wrapCheck 5 9 (wrapTail univ decD)))

theorem wrapCheck_wellScoped {i j n : ℕ} (hi : i < n) (hj : j < n) {c : Prog}
    (hc : c.WellScoped (n + 5)) : (wrapCheck i j c).WellScoped n :=
  ⟨callVar_wellScoped hi lenProg_wellScoped,
    ⟨⟨by simp [WellScoped], by simpa [WellScoped] using hj⟩,
      ⟨callVar_wellScoped (by omega) eqBitsProg_wellScoped,
        ⟨by simp, trivial, by simpa [show n + 1 + 1 + 1 + 2 = n + 5 by omega] using hc⟩⟩⟩⟩

theorem wrapTail_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (decD : Data) :
    (wrapTail univ decD).WellScoped 20 :=
  ⟨⟨trivial, by simp [WellScoped]⟩, callVar_wellScoped (by simp) hU⟩

theorem wrapHead_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (sampProg : Prog) {c : Prog}
    (hc : c.WellScoped 6) : (wrapHead univ sampProg c).WellScoped 1 := by
  refine ⟨by simp, trivial, ?_⟩
  refine ⟨⟨trivial, ⟨by simp [WellScoped], trivial⟩⟩, ?_⟩
  refine ⟨callVar_wellScoped (by simp) hU, ?_⟩
  exact ⟨callVar_wellScoped (by simp) toUnaryProg_wellScoped, hc⟩

theorem wrapPre_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (sampProg : Prog) {c : Prog}
    (hc : c.WellScoped 10) : (wrapPre univ sampProg c).WellScoped 1 :=
  wrapHead_wellScoped hU sampProg ⟨by simp, trivial, ⟨by simp, trivial, hc⟩⟩

theorem wrapCore_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (sampProg : Prog)
    (decD : Data) : (wrapCore univ sampProg decD).WellScoped 1 :=
  wrapPre_wellScoped hU sampProg
    (wrapCheck_wellScoped (by omega) (by omega)
      (wrapCheck_wellScoped (by omega) (by omega) (wrapTail_wellScoped hU decD)))

/-! ## The length check -/

section Check

variable {i j : ℕ} {c : Prog} {env : Env} {l : BitStr} {m : ℕ}

theorem len_run (z : BitStr) :
    ∃ t, lenProg.Runs (encode z) (Data.ofNat z.length) t := by
  obtain ⟨t, -, h⟩ := lenProg_runs (z.map Data.ofBool)
  refine ⟨t, ?_⟩
  rw [encode_bitStr_eq_list]
  simpa using h

theorem eq_run (p q : ℕ) :
    ∃ t, eqBitsProg.Runs (.cons (Data.ofNat p) (Data.ofNat q)) (encode (decide (p = q))) t := by
  obtain ⟨t, -, h⟩ := eqBitsProg_runs (Data.ofNat p) (Data.ofNat q) []
    ((Data.ofNat p).size + (Data.ofNat q).size) le_rfl
  rw [eqBits_ofNat] at h
  exact ⟨t, h⟩

theorem wrapCheck_runs_of_ne (hi : env.get i = encode l) (hj : env.get j = Data.ofNat m)
    (hne : l.length ≠ m) : ∃ t, Eval env (wrapCheck i j c) .nil t := by
  obtain ⟨t₁, h₁⟩ := len_run l
  obtain ⟨t₂, h₂⟩ := eq_run l.length m
  exact ⟨_, Eval.let_ (callVar_eval lenProg_wellScoped hi h₁)
    (Eval.let_ (Eval.cons
        (Eval.var_of_get (env := Data.ofNat l.length :: env) (i := 0)
          (v := Data.ofNat l.length) (by simp))
        (Eval.var_of_get (env := Data.ofNat l.length :: env) (i := j + 1)
          (v := Data.ofNat m) (by simpa using hj)))
      (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0)
          (v := .cons (Data.ofNat l.length) (Data.ofNat m)) (by simp) h₂)
        (Eval.elim_nil (i := 0)
          (show Env.get (encode (decide (l.length = m)) ::
              Data.cons (Data.ofNat l.length) (Data.ofNat m) ::
              Data.ofNat l.length :: env) 0 = Data.nil by
            simp [hne, encode_bool, Data.ofBool])
          (Eval.nil _))))⟩

theorem wrapCheck_runs_of_eq (hi : env.get i = encode l) (hj : env.get j = Data.ofNat m)
    (heq : l.length = m) {r : Data} {t : ℕ} (hc : Eval (wrapCheckEnv l m env) c r t) :
    ∃ t', Eval env (wrapCheck i j c) r t' := by
  obtain ⟨t₁, h₁⟩ := len_run l
  obtain ⟨t₂, h₂⟩ := eq_run l.length m
  have hc' : Eval (Data.nil :: Data.nil :: encode (decide (l.length = m)) ::
      Data.cons (Data.ofNat l.length) (Data.ofNat m) :: Data.ofNat l.length :: env) c r t := by
    simpa [wrapCheckEnv, heq] using hc
  exact ⟨_, Eval.let_ (callVar_eval lenProg_wellScoped hi h₁)
    (Eval.let_ (Eval.cons
        (Eval.var_of_get (env := Data.ofNat l.length :: env) (i := 0)
          (v := Data.ofNat l.length) (by simp))
        (Eval.var_of_get (env := Data.ofNat l.length :: env) (i := j + 1)
          (v := Data.ofNat m) (by simpa using hj)))
      (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0)
          (v := .cons (Data.ofNat l.length) (Data.ofNat m)) (by simp) h₂)
        (Eval.elim_cons (i := 0) (a := .nil) (b := .nil)
          (by simp [heq, encode_bool, Data.ofBool]) hc')))⟩

/-- **Inversion.** A run of the check either fails the comparison and returns `nil`, or passes
it and is a run of the continuation. -/
theorem wrapCheck_inv (hi : env.get i = encode l) (hj : env.get j = Data.ofNat m)
    {r : Data} {t : ℕ} (h : Eval env (wrapCheck i j c) r t) :
    (l.length ≠ m ∧ r = .nil) ∨ (l.length = m ∧ ∃ t', Eval (wrapCheckEnv l m env) c r t') := by
  obtain ⟨t₁, h₁⟩ := len_run l
  obtain ⟨t₂, h₂⟩ := eq_run l.length m
  change Eval env (.let_ (callVar i lenProg) _) r t at h
  cases h with
  | let_ hA hB =>
    obtain ⟨rfl, -⟩ := hA.deterministic (callVar_eval lenProg_wellScoped hi h₁)
    cases hB with
    | let_ hC hD =>
      obtain ⟨rfl, -⟩ := hC.deterministic
        (Eval.cons (Eval.var_of_get (i := 0) (v := Data.ofNat l.length) (by simp))
          (Eval.var_of_get (i := j + 1) (v := Data.ofNat m) (by simpa using hj)))
      cases hD with
      | let_ hE hF =>
        obtain ⟨rfl, -⟩ := hE.deterministic (callVar_eval eqBitsProg_wellScoped (i := 0)
          (v := .cons (Data.ofNat l.length) (Data.ofNat m)) (by simp) h₂)
        by_cases hlm : l.length = m
        · refine Or.inr ⟨hlm, ?_⟩
          cases hF with
          | elim_nil hn _ => simp [hlm, encode_bool, Data.ofBool] at hn
          | elim_cons hcx hrest =>
            simp only [Env.get_cons_zero, hlm, decide_true, encode_bool, Data.ofBool] at hcx
            obtain ⟨rfl, rfl⟩ := Data.cons.inj hcx
            exact ⟨_, by simpa [wrapCheckEnv, hlm] using hrest⟩
        · refine Or.inl ⟨hlm, ?_⟩
          cases hF with
          | elim_nil _ hnil => cases hnil; rfl
          | elim_cons hcx _ => simp [hlm, encode_bool, Data.ofBool] at hcx

end Check

/-! ## The whole run -/

section Runs

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (decD : Data)
  (n : ℕ) (x y a b : BitStr)

/-- The environment the prefix hands to the first length check. -/
def wrapPreEnv : Env :=
  [encode y, .cons (encode a) (encode b), encode x,
    .cons (encode y) (.cons (encode a) (encode b)), Data.ofNat (S.dim n), encode (S.dim n),
    .cons (encode S.prog) (Data.cons (encode n) (encode CL.Sampler.Query.dimension)), encode n,
    .cons (encode x) (.cons (encode y) (.cons (encode a) (encode b))), encode (n, x, y, a, b)]

theorem dim_run :
    ∃ t, U.univ.Runs (.cons (encode S.prog) (Data.cons (encode n) (encode CL.Sampler.Query.dimension)))
      (encode (S.dim n)) t := by
  obtain ⟨t, ht⟩ := S.runs_dimension n
  obtain ⟨t', -, h⟩ := U.time_le S.prog _ _ t ht
  exact ⟨t', h⟩

theorem toUnary_run (k : ℕ) : ∃ t, toUnaryProg.Runs (encode k) (Data.ofNat k) t := by
  obtain ⟨t, -, h⟩ := toUnaryProg_runs k
  exact ⟨t, h⟩

theorem input_cons :
    (encode (n, x, y, a, b) : Data) =
      .cons (encode n) (.cons (encode x) (.cons (encode y) (.cons (encode a) (encode b)))) := rfl

/-- The prefix runs, whatever the continuation does. -/
theorem wrapPre_runs {c : Prog} {r : Data} {t : ℕ}
    (hc : Eval (wrapPreEnv S n x y a b) c r t) :
    ∃ t', Eval [encode (n, x, y, a, b)] (wrapPre U.univ S.prog c) r t' := by
  obtain ⟨t₁, h₁⟩ := dim_run U S n
  obtain ⟨t₂, h₂⟩ := toUnary_run (S.dim n)
  exact ⟨_, Eval.elim_cons (env := [encode (n, x, y, a, b)]) (i := 0) (a := encode n)
    (b := .cons (encode x) (.cons (encode y) (.cons (encode a) (encode b))))
    (by rw [Env.get_cons_zero, input_cons])
    (Eval.let_ (Eval.cons (Eval.const _ _)
        (Eval.cons (Eval.var_of_get (i := 0) (v := encode n) (by simp)) (Eval.const _ _)))
      (Eval.let_ (callVar_eval U.closed (i := 0)
          (v := .cons (encode S.prog) (Data.cons (encode n) (encode CL.Sampler.Query.dimension))) (by simp) h₁)
        (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 0) (v := encode (S.dim n))
            (by simp) h₂)
          (Eval.elim_cons (i := 4) (a := encode x)
              (b := .cons (encode y) (.cons (encode a) (encode b))) (by simp)
            (Eval.elim_cons (i := 1) (a := encode y) (b := .cons (encode a) (encode b))
              (by simp) hc)))))⟩

/-- **Inversion of the prefix.** -/
theorem wrapPre_inv {c : Prog} {r : Data} {t : ℕ}
    (h : Eval [encode (n, x, y, a, b)] (wrapPre U.univ S.prog c) r t) :
    ∃ t', Eval (wrapPreEnv S n x y a b) c r t' := by
  obtain ⟨t₁, h₁⟩ := dim_run U S n
  obtain ⟨t₂, h₂⟩ := toUnary_run (S.dim n)
  change Eval [encode (n, x, y, a, b)] (.elim 0 .nil _) r t at h
  cases h with
  | elim_nil hn _ => rw [Env.get_cons_zero, input_cons] at hn; exact absurd hn (by simp)
  | @elim_cons _ _ _ _ A B _ _ hcx hA =>
    rw [Env.get_cons_zero, input_cons] at hcx
    obtain ⟨rfl, rfl⟩ := Data.cons.inj hcx.symm
    cases hA with
    | let_ hB hC =>
      obtain ⟨rfl, -⟩ := hB.deterministic (Eval.cons (Eval.const _ _)
        (Eval.cons (Eval.var_of_get (i := 0) (v := encode n) (by simp)) (Eval.const _ _)))
      cases hC with
      | let_ hD hE =>
        obtain ⟨rfl, -⟩ := hD.deterministic (callVar_eval U.closed (i := 0)
          (v := .cons (encode S.prog) (Data.cons (encode n) (encode CL.Sampler.Query.dimension))) (by simp) h₁)
        cases hE with
        | let_ hF hG =>
          obtain ⟨rfl, -⟩ := hF.deterministic (callVar_eval toUnaryProg_wellScoped (i := 0)
            (v := encode (S.dim n)) (by simp) h₂)
          cases hG with
          | elim_nil hn _ => simp at hn
          | @elim_cons _ _ _ _ A₂ B₂ _ _ hc₂ hH =>
            obtain ⟨rfl, rfl⟩ := Data.cons.inj (by simpa using hc₂.symm)
            cases hH with
            | elim_nil hn _ => simp at hn
            | @elim_cons _ _ _ _ A₃ B₃ _ _ hc₃ hI =>
              obtain ⟨rfl, rfl⟩ := Data.cons.inj (by simpa using hc₃.symm)
              exact ⟨_, hI⟩

/-! ### The three outcomes -/

theorem wrapCore_runs_of_ne_left (hx : x.length ≠ S.dim n) :
    ∃ t, (wrapCore U.univ S.prog decD).Runs (encode (n, x, y, a, b)) .nil t := by
  obtain ⟨t, h⟩ := wrapCheck_runs_of_ne (i := 2) (j := 4) (env := wrapPreEnv S n x y a b)
    (c := wrapCheck 5 9 (wrapTail U.univ decD)) rfl rfl hx
  exact wrapPre_runs U S n x y a b h

theorem wrapCore_runs_of_ne_right (hx : x.length = S.dim n) (hy : y.length ≠ S.dim n) :
    ∃ t, (wrapCore U.univ S.prog decD).Runs (encode (n, x, y, a, b)) .nil t := by
  obtain ⟨t, h⟩ := wrapCheck_runs_of_ne (i := 5) (j := 9)
    (env := wrapCheckEnv x (S.dim n) (wrapPreEnv S n x y a b))
    (c := wrapTail U.univ decD) rfl rfl hy
  obtain ⟨t', h'⟩ := wrapCheck_runs_of_eq (i := 2) (j := 4) (env := wrapPreEnv S n x y a b)
    rfl rfl hx h
  exact wrapPre_runs U S n x y a b h'

theorem wrapCore_runs_of_eq (hx : x.length = S.dim n) (hy : y.length = S.dim n)
    {r : Data} {t₇ : ℕ} (h₇ : U.univ.Runs (.cons decD (encode (n, x, y, a, b))) r t₇) :
    ∃ t, (wrapCore U.univ S.prog decD).Runs (encode (n, x, y, a, b)) r t := by
  have htail : Eval (wrapCheckEnv y (S.dim n) (wrapCheckEnv x (S.dim n)
      (wrapPreEnv S n x y a b))) (wrapTail U.univ decD) r _ :=
    Eval.let_ (Eval.cons (Eval.const _ _)
      (Eval.var_of_get (i := 19) (v := encode (n, x, y, a, b)) (by simp [wrapCheckEnv,
        wrapPreEnv]))) (callVar_eval U.closed (i := 0)
      (v := .cons decD (encode (n, x, y, a, b))) (by simp) h₇)
  obtain ⟨t, h⟩ := wrapCheck_runs_of_eq (i := 5) (j := 9)
    (env := wrapCheckEnv x (S.dim n) (wrapPreEnv S n x y a b)) rfl rfl hy htail
  obtain ⟨t', h'⟩ := wrapCheck_runs_of_eq (i := 2) (j := 4) (env := wrapPreEnv S n x y a b)
    rfl rfl hx h
  exact wrapPre_runs U S n x y a b h'

/-- **The wrapper halts only if the universal machine does on the string's decider.** -/
theorem wrapCore_halts_inv {r : Data} {t : ℕ}
    (h : (wrapCore U.univ S.prog decD).Runs (encode (n, x, y, a, b)) r t) :
    r = .nil ∨ ∃ t', U.univ.Runs (.cons decD (encode (n, x, y, a, b))) r t' := by
  obtain ⟨t₁, h₁⟩ := wrapPre_inv U S n x y a b h
  rcases wrapCheck_inv (i := 2) (j := 4) (env := wrapPreEnv S n x y a b) rfl rfl h₁ with
    ⟨-, hr⟩ | ⟨-, t₂, h₂⟩
  · exact Or.inl hr
  rcases wrapCheck_inv (i := 5) (j := 9)
      (env := wrapCheckEnv x (S.dim n) (wrapPreEnv S n x y a b)) rfl rfl h₂ with
    ⟨-, hr⟩ | ⟨-, t₃, h₃⟩
  · exact Or.inl hr
  refine Or.inr ?_
  change Eval _ (.let_ _ (callVar 0 U.univ)) r t₃ at h₃
  cases h₃ with
  | let_ hA hB =>
    obtain ⟨rfl, -⟩ := hA.deterministic (Eval.cons (Eval.const _ _)
      (Eval.var_of_get (i := 19) (v := encode (n, x, y, a, b))
        (by simp [wrapCheckEnv, wrapPreEnv])))
    obtain ⟨t₄, -, h₄⟩ := callVar_runs_rev U.closed hB
    simp only [Env.get_cons_zero] at h₄
    exact ⟨_, h₄⟩

end Runs

end Cost.Prog

/-! ## The wrapped decider and the verifier a pair denotes -/

namespace Decider

open Cost Cost.Prog

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (decD : Data)

/-- The decider a string denotes: the datum `decD` the string carries, run by the universal
machine, wrapped in the question-length check against the sampler `S`. The datum need not be
the encoding of a program; when it is, `encode dec`, the run is a run of `dec`
(`wrap_accepts_prog`). -/
def wrap : Decider :=
  ⟨wrapCore U.univ S.prog decD, wrapCore_wellScoped U.closed _ _⟩

@[simp] theorem wrap_prog : (wrap U S decD).prog = wrapCore U.univ S.prog decD := rfl

/-- **Acceptance of the wrapped decider**: the two questions have the sampler's dimension and
the universal machine, run on the string's decider and the input, returns `true`. -/
theorem wrap_accepts (n : ℕ) (x y a b : BitStr) :
    (wrap U S decD).Accepts n x y a b ↔
      (x.length = S.dim n ∧ y.length = S.dim n ∧
        ∃ t, U.univ.Runs (.cons decD (encode (n, x, y, a, b))) (encode true) t) := by
  constructor
  · rintro ⟨t, ht⟩
    have hne : (encode true : Data) ≠ .nil := by simp [encode_bool, Data.ofBool]
    have hx : x.length = S.dim n := by
      by_contra hx
      obtain ⟨t', h'⟩ := wrapCore_runs_of_ne_left U S decD n x y a b hx
      exact hne (Eval.deterministic ht h').1
    have hy : y.length = S.dim n := by
      by_contra hy
      obtain ⟨t', h'⟩ := wrapCore_runs_of_ne_right U S decD n x y a b hx hy
      exact hne (Eval.deterministic ht h').1
    rcases wrapCore_halts_inv U S decD n x y a b ht with hr | hd
    · exact absurd hr hne
    · exact ⟨hx, hy, hd⟩
  · rintro ⟨hx, hy, td, hd⟩
    exact wrapCore_runs_of_eq U S decD n x y a b hx hy hd

/-- The wrapped decider accepts only questions of the sampler's dimension: the one structural
requirement of `def:normal-verifier`. -/
theorem wrap_accepts_length (n : ℕ) (x y a b : BitStr)
    (h : (wrap U S decD).Accepts n x y a b) : x.length = S.dim n ∧ y.length = S.dim n :=
  ⟨((wrap_accepts U S decD n x y a b).1 h).1, ((wrap_accepts U S decD n x y a b).1 h).2.1⟩

end Decider

namespace Verifier

open Cost

/-- **The verifier a pair `(S, d)` denotes**: the sampler `S`, and the datum `d` — the string's
decider, run by the universal machine — wrapped in the question-length check. Every pair
denotes one, well formed or not. -/
def ofSamplerDeciderD {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (decD : Data) :
    Verifier ℓ where
  sampler := S
  decider := Decider.wrap U S decD
  accepts_length n x y a b h := Decider.wrap_accepts_length U S decD n x y a b h

/-- The verifier a pair `(S, 𝒟)` of a sampler and a decider *program* denotes:
`ofSamplerDeciderD` at the program's encoding. -/
def ofSamplerDecider {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (dec : Prog) :
    Verifier ℓ :=
  ofSamplerDeciderD U S (encode dec)

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (decD : Data) (dec : Prog)

@[simp] theorem ofSamplerDeciderD_sampler : (ofSamplerDeciderD U S decD).sampler = S := rfl

@[simp] theorem ofSamplerDecider_sampler : (ofSamplerDecider U S dec).sampler = S := rfl

end Verifier

namespace Cost.Prog

open Cost Data

/-! ## The wrapper at the level of data

`Decider.wrap` is what `Verifier.IsBounded` bounds, and it is therefore what a tabulation has
to run: the bound says nothing about the *inner* decider, the datum the string carries, since
`UniversalMachine.halts_of` produces a run with no bound on its cost. So the tabulation needs
`encode (wrapCore univ sampProg decD)` as a primitive recursive function of the encoded
sampler program and the datum — which it can be, because `wrapCore` mentions the sampler
program only under `Prog.const (encode ·)` and the datum only under `Prog.const`.

`ProgD` is that mirror: the constructors of `Prog` at the level of `Data`, and the wrapper
rebuilt from them. Every `_eq` lemma is `rfl`, `Prog.toData` being structural, and
`dWrapCore_eq` is `rfl` too — nothing here is a second definition to keep in step with the
first, it is the same definition seen through the encoding. The existing `wrapCheck`,
`wrapHead`, `wrapTail`, `wrapCore` and everything proved about them are untouched.
-/

namespace ProgD
open Cost.Prog

def dV (i : ℕ) : Data := .cons (.ofNat 0) (.ofNat i)
def dNil : Data := .cons (.ofNat 1) .nil
def dC (h t : Data) : Data := .cons (.ofNat 2) (.cons h t)
def dE (i : ℕ) (n c : Data) : Data := .cons (.ofNat 3) (.cons (.ofNat i) (.cons n c))
def dL (e b : Data) : Data := .cons (.ofNat 4) (.cons e b)
def dK (d : Data) : Data := .cons (.ofNat 6) d

theorem primrec_dC : Primrec₂ dC :=
  (Data.primrec_cons.comp (Primrec.const (Data.ofNat 2))
    (Data.primrec_cons.comp Primrec.fst Primrec.snd)).to₂

theorem primrec_dL : Primrec₂ dL :=
  (Data.primrec_cons.comp (Primrec.const (Data.ofNat 4))
    (Data.primrec_cons.comp Primrec.fst Primrec.snd)).to₂

theorem primrec_dK : Primrec dK := Data.primrec_cons.comp (Primrec.const (Data.ofNat 6)) Primrec.id

theorem primrec_dE (i : ℕ) : Primrec₂ (dE i) :=
  (Data.primrec_cons.comp (Primrec.const (Data.ofNat 3))
    (Data.primrec_cons.comp (Primrec.const (Data.ofNat i))
      (Data.primrec_cons.comp Primrec.fst Primrec.snd))).to₂

/-! The wrapper, at the level of data. -/

def dWrapCheck (i j : ℕ) (c : Data) : Data :=
  dL (dL (dV i) (encode Prog.lenProg))
    (dL (dC (dV 0) (dV (j + 1)))
      (dL (dL (dV 0) (encode Prog.eqBitsProg)) (dE 0 dNil c)))

def dWrapTail (univ decD : Data) : Data := dL (dC (dK decD) (dV 19)) (dL (dV 0) univ)

def dWrapHead (univ sampD c : Data) : Data :=
  dE 0 dNil
    (dL (dC (dK sampD) (dC (dV 0) (dK (encode CL.Sampler.Query.dimension))))
      (dL (dL (dV 0) univ) (dL (dL (dV 0) (encode Prog.toUnaryProg)) c)))

def dWrapCore (univ sampD decD : Data) : Data :=
  dWrapHead univ sampD (dE 4 dNil (dE 1 dNil
    (dWrapCheck 2 4 (dWrapCheck 5 9 (dWrapTail univ decD)))))

theorem dWrapCore_eq (univ sampProg : Prog) (decD : Data) :
    dWrapCore (encode univ) (encode sampProg) decD
      = encode (Prog.wrapCore univ sampProg decD) := rfl

theorem primrec_dWrapCheck (i j : ℕ) : Primrec (dWrapCheck i j) :=
  (primrec_dL.comp (Primrec.const _)
    (primrec_dL.comp (Primrec.const _)
      (primrec_dL.comp (Primrec.const _) ((primrec_dE 0).comp (Primrec.const dNil) Primrec.id))))

theorem primrec_dWrapTail (univ : Data) : Primrec (dWrapTail univ) :=
  primrec_dL.comp (primrec_dC.comp (primrec_dK.comp Primrec.id) (Primrec.const (dV 19)))
    (Primrec.const (dL (dV 0) univ))

theorem primrec_dWrapCore (univ : Data) : Primrec₂ (dWrapCore univ) := by
  have hhead : Primrec₂ fun sampD c : Data => dWrapHead univ sampD c :=
    ((primrec_dE 0).comp (Primrec.const dNil)
      (primrec_dL.comp
        (primrec_dC.comp (primrec_dK.comp Primrec.fst)
          (Primrec.const (dC (dV 0) (dK (encode CL.Sampler.Query.dimension)))))
        (primrec_dL.comp (Primrec.const (dL (dV 0) univ))
          (primrec_dL.comp (Primrec.const (dL (dV 0) (encode Prog.toUnaryProg)))
            Primrec.snd)))).to₂
  exact (hhead.comp Primrec.fst
    ((primrec_dE 4).comp (Primrec.const dNil)
      ((primrec_dE 1).comp (Primrec.const dNil)
        ((primrec_dWrapCheck 2 4).comp ((primrec_dWrapCheck 5 9).comp
          ((primrec_dWrapTail univ).comp Primrec.snd)))))).to₂

end ProgD

end Cost.Prog

end MIPRE


