-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_Size
-- name    : MIPRE_Foundations_Halting_Paper_Size
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:08:50.877244+00:00
-- url     : https://prove2.me/theorems/0c690fc5-5f9d-4bd6-9d17-ca3cdb90be41
-- title:
--   Sizes of the descriptions along the paper's route: affine in $|M| + |\lambda|$
-- statement:
--   The accounting of `Paper/Cost.lean` runs on the sizes of the descriptions that the decider $\mathcal{D}^{\mathrm{halt}}$ of `Paper/Decider.lean` is built from; each is an exact affine function of $|M| + |\lambda|$, the sizes `esize M + esize lam` of the binary encodings, with a constant depending on $G$, $U$, $UT$ and the search program $S'$ alone. This bundle names the four constants.
--
--   `MIPRE.Halting.cF G U UT S' = esize (body G U UT S') + esize smnProg + 77` is the size of the code of `F` beyond $|M| + |\lambda|$; `cK = cF + esize U.univ + esize smnProg + 136` that of the two-argument program `kleeneProg U.univ F` of the fixed point; `cD = 2 cK + 35` that of the decider `dec M λ` beyond $2(|M| + |\lambda|)$; and `cO = 7 cK + 5 cD + 4 esize (body G U UT S') + 181` the overhead of the fixed point's time transfer beyond $21(|M| + |\lambda|)$.
--
--   The embedded lemmas are the equations these constants are named for: `esize_F_code`, `esize_kleeneProg_F`,
--   $$\mathrm{esize}\,(\mathrm{dec}\;G\;U\;UT\;S'\;M\;\lambda) = 2\,(\mathrm{esize}\,M + \mathrm{esize}\,\lambda) + \mathrm{cD}\;G\;U\;UT\;S',$$
--   `size_descData` (the description $(M, (\lambda, e))$ has size $|M| + |\lambda| + |e| + 2$), `esize_F_apply` (`F e` has size $|\mathrm{body}| + |M| + |\lambda| + |e| + 37$), `F_timeBound_eval` (the time bound of `F` at $x$ is $2(|\mathrm{body}| + |M| + |\lambda| + x) + 47$), `kleeneOverhead_eq` (`kleeneOverhead U F` is $21(|M| + |\lambda|) + \mathrm{cO}$) and the auxiliary `esize_nat_le_self` ($\mathrm{esize}\,n \le 4n + 1$).
--
--   The factor $2$ in `esize_dec`, the decider being a hardcoding of `kleeneProg` to its own description, is the $2|c|$ of the criterion route and the reason the parameter of blueprint `lem:lambda` is $\Lambda_0 + 4|M|$ rather than $\Lambda_0 + 2|M|$.
--
--   **Formalization Note**. The constants are what Lean computes from the constructors and are named rather than tracked, since only their existence matters downstream; all four are `noncomputable` definitions, taking `esize` of programs built from `PolyTimeFun` codes. The equations are exact equalities, not bounds, and `F`, `dec`, `kleeneProg`, `kleeneOverhead` and `smnProg` are those of `Paper/Decider.lean` and `Cost/Kleene.lean`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Size.lean; blueprint lem:lambda

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Size.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider
import Theorems.Thm_MIPRE_Cost_hardcode_size

/-!
# The halting verifier along the paper's route: sizes

The sizes of the descriptions the accounting of `Paper/Cost.lean` runs on, each an exact
affine function of `|M| + |λ|` — the binary encodings' sizes `esize M + esize lam` — with a
constant depending on `G`, `U`, `UT` and `S'` alone:

* the code of the map `F` (`esize_F_code`), which carries `body`, `M` and `λ` as constants;
* the two-argument program `kleeneProg` of the fixed point (`esize_kleeneProg_F`);
* the decider `dec M λ` itself, a hardcoding of `kleeneProg` to its own description
  (`esize_dec`), so **twice** the previous plus a constant — this is the `2|c|` of the
  criterion route and the reason the parameter `λ(M)` of `lem:lambda` is `Λ₀ + 4|M|`;
* `F` applied to the decider (`esize_F_dec`), the program the fixed point actually runs;
* the time bound of `F` (`F_timeBound_eval`) and the overhead of the fixed point's
  transfer (`kleeneOverhead_eq`).

The constants are what Lean computes from the constructors; they are named rather than
tracked, since only their existence matters downstream.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Polynomial

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-- `esize n ≤ 4n + 1`: the binary numeral of `n` has at most `size n ≤ n` digits. -/
theorem esize_nat_le_self (n : ℕ) : esize n ≤ 4 * n + 1 :=
  (esize_nat_le n).trans (by have := Nat.size_le.2 (Nat.lt_two_pow_self (n := n)); omega)

/-- The size of the code of `F` beyond `|M| + |λ|`. -/
noncomputable def cF (S' : Prog) : ℕ := esize (body G U UT S') + esize smnProg + 77

theorem esize_F_code (S' M : Prog) (lam : ℕ) :
    esize (F G U UT S' M lam).code = esize M + esize lam + cF G U UT S' := by
  simp only [F, PolyTimeFun.comp, PolyTimeFun.pair, PolyTimeFun.const, PolyTimeFun.id,
    PolyTimeFun.smn, esize_eq_size_toData, toData, Data.size_cons, Data.size_ofNat]
  have h1 : M.toData.size = esize M := rfl
  have h1' : (encode M : Data).size = esize M := rfl
  have h2 : (encode lam : Data).size = esize lam := rfl
  have h3 : (body G U UT S').toData.size = esize (body G U UT S') := rfl
  have h3' : (encode (body G U UT S') : Data).size = esize (body G U UT S') := rfl
  have h4 : smnProg.toData.size = esize smnProg := rfl
  unfold cF
  omega

/-- The size of `kleeneProg U.univ F` beyond `|M| + |λ|`. -/
noncomputable def cK (S' : Prog) : ℕ := cF G U UT S' + esize U.univ + esize smnProg + 136

theorem esize_kleeneProg_F (S' M : Prog) (lam : ℕ) :
    esize (kleeneProg U.univ (F G U UT S' M lam)) = esize M + esize lam + cK G U UT S' := by
  have h0 := esize_F_code G U UT S' M lam
  simp only [kleeneProg, callVar, esize_eq_size_toData, toData, Data.size_cons,
    Data.size_ofNat, Data.size_nil] at h0 ⊢
  have h1 : U.univ.toData.size = esize U.univ := rfl
  have h2 : smnProg.toData.size = esize smnProg := rfl
  have h3 : M.toData.size = esize M := rfl
  unfold cK
  omega

/-- The size of the decider `dec M λ` beyond `2 (|M| + |λ|)`. -/
noncomputable def cD (S' : Prog) : ℕ := 2 * cK G U UT S' + 35

theorem esize_dec (S' M : Prog) (lam : ℕ) :
    esize (dec G U UT S' M lam) = 2 * (esize M + esize lam) + cD G U UT S' := by
  rw [dec, kleeneFix, hardcode_size]
  have h1 : (encode (kleeneProg U.univ (F G U UT S' M lam)) : Data).size =
    esize (kleeneProg U.univ (F G U UT S' M lam)) := rfl
  rw [h1, esize_kleeneProg_F, cD]
  omega

/-- The description `(M, (λ, e))` has size `|M| + |λ| + |e| + 2`. -/
theorem size_descData (M : Prog) (lam : ℕ) (e : Prog) :
    (encode (M, (lam, e)) : Data).size = esize M + esize lam + esize e + 2 := by
  show esize M + (esize lam + esize e + 1) + 1 = _
  omega

/-- `F e = hardcode body (M, (λ, e))` has size `|body| + |M| + |λ| + |e| + 37`. -/
theorem esize_F_apply (S' M : Prog) (lam : ℕ) (e : Prog) :
    esize (F G U UT S' M lam e) = esize (body G U UT S') + esize M + esize lam + esize e + 37 := by
  rw [F_apply, hardcode_size, size_descData]
  omega

/-- The time bound of `F`: affine in the argument and in `|body| + |M| + |λ|`. -/
theorem F_timeBound_eval (S' M : Prog) (lam x : ℕ) :
    (F G U UT S' M lam).timeBound.eval x =
      2 * (esize (body G U UT S') + esize M + esize lam + x) + 47 := by
  simp only [F, PolyTimeFun.comp, PolyTimeFun.pair, PolyTimeFun.const, PolyTimeFun.id,
    PolyTimeFun.smn, eval_add, eval_comp, eval_X, eval_C, eval_one]
  omega

/-- The overhead of the fixed point's time transfer beyond `21 (|M| + |λ|)`. -/
noncomputable def cO (S' : Prog) : ℕ :=
  7 * cK G U UT S' + 5 * cD G U UT S' + 4 * esize (body G U UT S') + 181

theorem kleeneOverhead_eq (S' M : Prog) (lam : ℕ) :
    kleeneOverhead U (F G U UT S' M lam) = 21 * (esize M + esize lam) + cO G U UT S' := by
  have h1 := esize_kleeneProg_F G U UT S' M lam
  have h2 := esize_dec G U UT S' M lam
  have h3 := esize_F_apply G U UT S' M lam (dec G U UT S' M lam)
  have h4 := F_timeBound_eval G U UT S' M lam (esize (dec G U UT S' M lam))
  rw [kleeneOverhead]
  change 7 * esize (kleeneProg U.univ (F G U UT S' M lam)) + esize (dec G U UT S' M lam) +
    (F G U UT S' M lam).timeBound.eval (esize (dec G U UT S' M lam)) +
    2 * esize (F G U UT S' M lam (dec G U UT S' M lam)) + 60 = _
  rw [h1, h4, h3, h2, cO]
  omega

end MIPRE.Halting


