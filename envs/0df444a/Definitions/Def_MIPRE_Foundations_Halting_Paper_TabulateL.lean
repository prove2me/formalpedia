-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
-- name    : MIPRE_Foundations_Halting_Paper_TabulateL
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:03:58.319851+00:00
-- url     : https://prove2.me/theorems/54aae276-09e1-4126-85f3-5799205c23d0
-- title:
--   Tabulating a string's verifier under its own compression parameter
-- statement:
--   `Halting.tab G U x n` (`Halting/Instantiation.lean`) tabulates the $n$-th game of the verifier a string denotes with the decider budget that $n$-boundedness supplies, $n^n(|d|+1)^n$. The paper's route runs its verifier at a fixed level $C_0$ with a parameter $\lambda = \mathrm{poly}(|M|)$, so that verifier is $\lambda$-bounded and not $C_0$-bounded; this bundle re-budgets the decider from the string's own parameter. Fix $G$ and $U$.
--
--   `MIPRE.Halting.accOfL pd n lam x y a b : Bool` is acceptance read off the encoded decider program $pd$ by one budgeted run: `Machine.runForD pd (encode (n, x, y, a, b))` with the budget `Decider.acceptBudget (n ^ lam) lam x y a b`, that is $n^\lambda (\mathrm{size}(\mathrm{encode}(x,y,a,b)) + 1)^\lambda$, returns `some (encode true)`. `tabOfL sd pd s T B k n lam : GameData` is the doubled tabulation with this acceptance: $\mathrm{nX} = 2^{s+1} - 1$, $\mathrm{nA} = |\mathrm{bitStrsLE}\,T| - 1$, the weight list over $\mathbb{F}_2^s$ from the tagged marginals `margOf sd B k n`, and the acceptance list `accListW` from `accOfL pd n lam`, the sampler side being that of `tabOf`. `tabL G U x n` instantiates it at the string's encoded programs, dimension and bounds, with $\lambda =$ `descLam x`:
--   $$\mathrm{tabL}\;G\;U\;x\;n = \mathrm{tabOfL}\;(\mathrm{sampData}\;G\;x)\;(\mathrm{decProgData}\;G\;U\;x)\;(\mathrm{dimOf}\;\dots)\;(\mathrm{ansBound}\;G\;x\;n)\;(\mathrm{ansBound}\;G\;x\;n)\;G.\mathrm{deg}\;n\;(\mathrm{descLam}\;x).$$
--   `eXofL G U x n : Fin (nX + 1) ≃ Bool × (Vof G U x).Questions n` and `eAofL G U x n : Fin (nA + 1) ≃ Verifier.Answers (ansBound G x n)` are the relabelings.
--
--   The embedded lemmas are the primitive recursiveness of `accOfL` and `tabOfL` in their parameters, the computability of the argument tuple and of `fun p => tabL G U p.1 p.2`, the cardinalities `tabL_nX`, `tabL_nA`, and `exists_semL n₀`: there is a closed program $S$ with `Halts S (encode x) ↔ 1/2 < quantumValue (tabL G U x n₀).game` for every string $x$, which the search branch of the paper-route decider tests.
--
--   **Formalization Note**. The only change from `tab` is the budget, $n^\lambda(|d|+1)^\lambda$ with $\lambda =$ `descLam x`, exactly what `Verifier.IsBounded λ` supplies at every $n \ge 2$; the correctness statement `tabL_value` is a theorem of the module not in this bundle. `tabL`, `eXofL`, `eAofL` are `noncomputable`. `exists_semL` is existential; `semL` of `Paper/Main.lean` is its `choose`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/TabulateL.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/TabulateL.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation

/-!
# The tabulation of a string's verifier under its own parameter

`Halting.tab G U x n` (`Halting/Instantiation.lean`) tabulates the `n`-th game of the verifier
a string denotes with the decider budget that `n`-boundedness supplies, `n ^ n · (|d| + 1) ^ n`,
and is correct on `n`-bounded strings. The halting reduction along the paper's route
(`planning/polytime-halting.md`) runs its verifier at the *fixed* level `C₀` with a parameter
`λ = poly(|M|)` that is far larger than `C₀`; that verifier is `λ`-bounded and not
`C₀`-bounded, and its size clause alone rules the old budget out. So the decider is
re-budgeted from the string's own parameter: `n ^ λ · (|d| + 1) ^ λ` at index `n` with
`λ = descLam x`, which is exactly what `Verifier.IsBounded λ` supplies at every `n ≥ 2`.

Everything else — the sampler runs under the compressed sampler's own bound, the doubled
question set, the weight list — is `Instantiation.lean`'s, and the correctness proof is its
`tab_match` with the one budget lemma swapped (`accOfL_iff`). The semidecider for
"`val*` at level `C₀` exceeds `1/2`" on this tabulation (`exists_semL`) is what the search
branch of the paper-route decider tests.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData)

namespace Halting

/-! ## Acceptance under the `λ`-budget -/

/-- Acceptance from the encoded decider program, under the budget `n ^ λ · (|d| + 1) ^ λ`. -/
def accOfL (pd : Data) (n lam : ℕ) (x y a b : BitStr) : Bool :=
  decide (Machine.runForD pd (encode (n, x, y, a, b))
    (Decider.acceptBudget (n ^ lam) lam x y a b) = some (encode true))

set_option maxHeartbeats 1000000 in
theorem primrec_accOfL {α : Type*} [Primcodable α] {pd : α → Data} {lvl lam : α → ℕ}
    (hpd : Primrec pd) (hlvl : Primrec lvl) (hlam : Primrec lam) :
    Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      accOfL (pd q.1) (lvl q.1) (lam q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have hpd' : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => pd q.1 :=
    hpd.comp Primrec.fst
  have hn : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => lvl q.1 :=
    hlvl.comp Primrec.fst
  have hl : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => lam q.1 :=
    hlam.comp Primrec.fst
  have hx : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hy : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hebs : Primrec fun l : BitStr => (encode l : Data) := primrec_encode_bitStr
  have htup : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => (encode q.2 : Data) :=
    Data.primrec_cons.comp (hebs.comp hx)
      (Data.primrec_cons.comp (hebs.comp hy)
        (Data.primrec_cons.comp (hebs.comp ha) (hebs.comp hb)))
  have hinput : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      (encode (lvl q.1, q.2) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp hn) htup
  have hbudget : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Decider.acceptBudget (lvl q.1 ^ lam q.1) (lam q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 :=
    Primrec.nat_mul.comp (primrec_nat_pow.comp hn hl)
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp htup)) hl)
  have hfin : PrimrecPred fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Machine.runForD (pd q.1) (encode (lvl q.1, q.2))
        (Decider.acceptBudget (lvl q.1 ^ lam q.1) (lam q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
        = some (encode true) :=
    Primrec.eq.comp (Machine.primrec_runForD.comp ((hpd'.pair hinput).pair hbudget))
      (Primrec.const (some (encode true) : Option Data))
  exact (Primrec.ite hfin (Primrec.const true) (Primrec.const false)).of_eq fun q => by
    simp only [accOfL]; split <;> simp_all

/-- The doubled tabulation with the decider under the `λ`-budget; the sampler side is
`tabOf`'s. -/
def tabOfL (sd pd : Data) (s T B k n lam : ℕ) : GameData where
  nX := 2 ^ (s + 1) - 1
  nA := (Data.bitStrsLE T).length - 1
  w := Verifier.weightList s
        (fun z => Verifier.bitsToIdx (false :: margOf sd B k n .alice z))
        (fun z => Verifier.bitsToIdx (true :: margOf sd B k n .bob z))
  acc := Verifier.accListW s T (fun u => Verifier.bitsToIdx (false :: u))
          (fun v => Verifier.bitsToIdx (true :: v)) (accOfL pd n lam)

theorem primrec_tabOfL {α : Type*} [Primcodable α] {sd pd : α → Data}
    {s T B lvl lam : α → ℕ}
    (k : ℕ) (hsd : Primrec sd) (hpd : Primrec pd) (hs : Primrec s) (hT : Primrec T)
    (hB : Primrec B) (hlvl : Primrec lvl) (hlam : Primrec lam) :
    Primrec fun a : α => tabOfL (sd a) (pd a) (s a) (T a) (B a) k (lvl a) (lam a) := by
  have hnX : Primrec fun a : α => 2 ^ (s a + 1) - 1 :=
    Primrec.nat_sub.comp
      (primrec_nat_pow.comp (Primrec.const 2) (Primrec.succ.comp hs)) (Primrec.const 1)
  have hnA : Primrec fun a : α => (Data.bitStrsLE (T a)).length - 1 :=
    Primrec.nat_sub.comp (Primrec.list_length.comp (Data.primrec_bitStrsLE.comp hT))
      (Primrec.const 1)
  have hacc := Verifier.primrec_accListW (s := s) (T := T)
    (fA := fun u => Verifier.bitsToIdx (false :: u))
    (fB := fun v => Verifier.bitsToIdx (true :: v))
    (acc? := fun a => accOfL (pd a) (lvl a) (lam a)) hs hT
    (Verifier.primrec_tagIdxOf false) (Verifier.primrec_tagIdxOf true)
    (primrec_accOfL hpd hlvl hlam)
  refine ((Primrec.of_equiv_symm (e := GameData.equivTuple)).comp
    (hnX.pair (hnA.pair ((primrec_weightList k hsd hs hB hlvl).pair hacc)))).of_eq ?_
  intro a
  rfl

variable (G : GapCompression) (U : UniversalMachine)

theorem primrec_tabOfL_tuple (k : ℕ) :
    Primrec fun q : (Data × Data) × (ℕ × ℕ) × ℕ × ℕ × ℕ =>
      tabOfL q.1.1 q.1.2 q.2.1.1 q.2.2.1 q.2.1.2 k q.2.2.2.1 q.2.2.2.2 :=
  primrec_tabOfL k (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

/-- **The tabulation of `(Vof G U x)`'s `n`-th game under the string's own parameter.** -/
noncomputable def tabL (x : BitStr) (n : ℕ) : GameData :=
  tabOfL (sampData G x) (decProgData G U x)
    (dimOf (sampData G x) (ansBound G x n) G.deg n) (ansBound G x n) (ansBound G x n) G.deg n
    (descLam x)

theorem computable_tabArgsL : Computable fun p : BitStr × ℕ =>
    ((sampData G p.1, decProgData G U p.1),
      ((dimOf (sampData G p.1) (ansBound G p.1 p.2) G.deg p.2, ansBound G p.1 p.2),
        (ansBound G p.1 p.2, (p.2, descLam p.1)))) :=
  ((computable_sampData_fst G).pair (computable_decProgData_fst G U)).pair
    (((computable_dimOf_fst G).pair (computable_ansBound G)).pair
      ((computable_ansBound G).pair (Computable.snd.pair (primrec_descLam.to_comp.comp
        Computable.fst))))

theorem tabL_computable : Computable fun p : BitStr × ℕ => tabL G U p.1 p.2 :=
  ((primrec_tabOfL_tuple G.deg).to_comp.comp (computable_tabArgsL G U)).of_eq fun _ => rfl

/-! ## The tabulation matches the verifier, doubled

Verbatim `Instantiation.lean`'s `tab_nX` … `tab_value`, at `tabL` and with `accOfL_iff` in
place of `accOf_iff`. -/

theorem tabL_nX (x : BitStr) (n : ℕ) :
    (tabL G U x n).nX + 1 = 2 ^ ((Vof G U x).sampler.dim n + 1) := by
  show 2 ^ (dimOf (sampData G x) (ansBound G x n) G.deg n + 1) - 1 + 1 = _
  rw [dimOf_eq G U x n]
  exact Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)

theorem tabL_nA (x : BitStr) (n : ℕ) :
    (tabL G U x n).nA + 1 = (Verifier.answerList (ansBound G x n)).length := by
  show (Data.bitStrsLE (ansBound G x n)).length - 1 + 1 = _
  rw [Verifier.answerList, List.length_map]
  exact Nat.succ_pred_eq_of_pos (Data.length_bitStrsLE_pos _)

/-- The question relabeling. -/
noncomputable def eXofL (x : BitStr) (n : ℕ) :
    Fin ((tabL G U x n).nX + 1) ≃ Bool × (Vof G U x).Questions n :=
  (finCongr (tabL_nX G U x n)).trans (Verifier.tagEquiv _).symm

/-- The answer relabeling. -/
noncomputable def eAofL (x : BitStr) (n : ℕ) :
    Fin ((tabL G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n) :=
  (finCongr (tabL_nA G U x n)).trans (Verifier.answerEquiv _)

/-! ## The semidecider of the search branch -/

/-- **The search branch's semidecider**: a closed program halting on `encode x` exactly when the
tabulation of `x`'s verifier at the level `n₀` has quantum value above `1/2`. On the strings this
tabulation is correct for (`tabL_value`), that is `val*(𝒱_{n₀}) > 1/2`. -/
theorem exists_semL (n₀ : ℕ) : ∃ S : Prog, S.WellScoped 1 ∧
    ∀ x : BitStr, Halts S (encode x) ↔ (1 : ℝ) / 2 < quantumValue (tabL G U x n₀).game := by
  obtain ⟨S, hS, hSx⟩ := exists_semidecider_lt_quantumValue
    (g := fun x => tabL G U x n₀)
    (((tabL_computable G U).comp (Computable.id.pair (Computable.const n₀))).of_eq
      fun _ => rfl) 1 2
  refine ⟨S, hS, fun x => (hSx x).trans ?_⟩
  simp only [Nat.cast_one, Nat.cast_ofNat]

end Halting

end MIPRE


