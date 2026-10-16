-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_Cost
-- name    : MIPRE_Foundations_Halting_Paper_Cost
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:11:26.536254+00:00
-- url     : https://prove2.me/theorems/ddd20a0e-ba36-46ff-848b-30e1bc6228e2
-- title:
--   The accounting of $\mathcal{V}^{\mathrm{halt}}$: master cost bounds and the threshold $\Lambda_0$ of `lem:lambda`
-- statement:
--   Blueprint `lem:lambda` in the paper's form: `Vhalt M λ` is $\lambda$-bounded once $\lambda \ge \Lambda_0 + 4|M|$, for a threshold $\Lambda_0$ depending on $G$, $U$, $UT$, $S'$ alone. This bundle defines the bounds and the threshold; $z$ is the largest of the index, $|M|$, $\lambda$ and the input size.
--
--   `constCost` and `progSize G U lam e` bound the constant programs' cost and the size of the program `prep` returns. `muZ z = 5z + 1` bounds $|n|$, $|M| + |\lambda|$, $|\lambda|$; `eZ`, `pZ`, `feZ` are the sizes of the decider, of the description $(M, (\lambda, \mathrm{dec}\,M\,\lambda))$ and of `F (dec M λ)`; `vZ z s` the size of the input $(n, d)$, $|d| = s$; `tpZ`, `sigmaZ`, `tcZ`, `tuZ`, `tbZ`, `tfZ` the time of `prep`, the size and time of the program it returns, the universal machine's time, the times of `body` and `F (dec M λ)`; `ovZ` the overhead of the fixed point's transfer; `decRunZ z s = U.bound.eval (vZ z s + tfZ z s + feZ z) + 3 vZ z s + ovZ z` the master bound on the decider's run; `decCostPoly`, `decCostDeg` the polynomial and degree chosen from `exists_dec_cost_poly`.
--
--   `sampSizeZ` (the compressed sampler's program size), `betaZ z = G.bound.eval (2z)`, `headWZ` (`wrapHeadZ` at $z$) and `WZ z` (`wrapCoreCost` with every atom replaced by its bound); `vsizeZ S' l`, the size of $\mathcal{V}^{\mathrm{halt}}$ beyond $2|M|$ in $l = |\lambda|$; `Lam0 G U UT S'`, the threshold chosen from `exists_lamBound`.
--
--   The embedded lemmas are `dec_cost` (`dec M λ` halts on $(n, d)$ within `decRunZ (n + |M| + λ) |d|`), `PolyBounded`/`PolyCost` facts for every bound, `exists_dec_cost_poly`, `dec_cost_spec`, `Vhalt_decider_cost`, `wrapCoreCost_le_WZ`, the three clause lemmas, `Vhalt_size_le`, two size lemmas, `prep_output`, and `exists_lamBound`:
--   $$\exists\,\Lambda_0,\ \forall M\ \lambda,\ \Lambda_0 + 4\,\mathrm{esize}\,M \le \lambda \to (\mathrm{Vhalt}\;M\;\lambda).\mathrm{IsBounded}\;\lambda \;\land\; \forall n \ge 2,\ G.\mathrm{bound}(n + \lambda) \le n^\lambda .$$
--
--   **Formalization Note**. The threshold is existential, as in `lem:lambda`: the paper's $\lambda(M) = \mathrm{poly}(|M|)$ is the affine $\Lambda_0 + 4|M|$, with $\Lambda_0$ whatever the absorption thresholds are; the $4|M|$ comes from the decider's description being $2(|M| + |\lambda|)$ plus a constant. `Lam0`, `decCostPoly`, `decCostDeg` are `Classical.choose` of existentials, hence `noncomputable`, as are the bounds evaluating polynomials.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Cost.lean; blueprint lem:lambda; paper recursive.tex

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Cost.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_kleeneFix_runs_of

/-!
# The halting verifier along the paper's route: the accounting

Blueprint `lem:lambda` in the paper's form (`recursive.tex`), for the polynomial-time halting
reduction of `planning/polytime-halting.md`: the verifier `Vhalt M λ` is `λ`-bounded
(`Verifier.IsBounded λ`) as soon as `λ ≥ Λ₀ + 4|M|`, for a threshold `Λ₀` depending on the
compressor, the universal machines and the search program alone — and at such `λ` the
compressor's bound `poly(n, λ)` is below `n ^ λ` at every level `n ≥ 2`, which is what the
induction of `Paper/Induction.lean` runs on.

The accounting has three layers.

* **The decider's run** (`dec_cost`): on `(n, d)`, `dec M λ` runs within `decRunZ z |d|` at
  `z = n + |M| + λ`, an explicit expression assembled along the fixed point's time transfer
  (`Cost.kleeneFix_runs_of`), the hardcoding of the description (`hardcode_time`), the run of
  `prep` (its `timeBound`), the universal machine on what `prep` returns (`U.time_le`) and
  the compressed decider's own time (`GapCompression.decider_time`). `decRunZ` is a `PolyCost`,
  so the run is within `Q(n + |M| + λ) · (|d| + 1) ^ k` for a polynomial `Q` and a degree `k`
  depending on `G`, `U`, `UT`, `S'` alone (`decCostPoly`, `decCostDeg`, `dec_cost_spec`).
  This fine form, polynomial in the level with `|M|` and `λ` as parameters, is what the class
  verifier of the paper's `MIP*` needs at the fixed level `C`; `IsBounded` only records
  `n ^ λ`.
* **The wrapped decider** (`Vhalt_decider_cost`): `Prog.wrapCoreCost` of `Halting/WrapperCost`
  with the inner cost above, bounded by the master expression `WZ z` at the largest `z` of the
  index, `|M|`, `λ` and the input size (`wrapCoreCost_le_WZ`).
* **The clauses** of `IsBounded λ`, each absorbed past a threshold by `PolyBounded.absorb`
  (the dimension, the sampler's and the decider's times, and the parameter inequality
  `poly(n, λ) ≤ n ^ λ`) or `PolyBounded.absorb_log` (the size, where the decider's description
  is `2 (|M| + |λ|)` plus a constant, so that `λ ≥ Λ₀ + 4|M|` leaves room for it).

The threshold is existential (`exists_lamBound`, `Lam0`), as in `lem:lambda`: the paper's
`λ(M) = poly(|M|)` is here the affine `Λ₀ + 4|M|`, and the constant `Λ₀` is whatever the
absorption thresholds are.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.Prog.ProgD Polynomial

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-! ## What `prep` returns -/

/-- The cost of the two constant programs: the sizes of `encode true` and `encode false`. -/
def constCost : ℕ := (encode true : Data).size + (encode false : Data).size

/-- The size of the program `prep` returns, at the parameter `λ` and the inner decider `e`:
the compressed decider's, from `compress`'s time bound at the size of its input. -/
noncomputable def progSize (lam : ℕ) (e : Prog) : ℕ :=
  G.compress.timeBound.eval (2 * G.samplerProg.timeBound.eval (esize lam) + esize e +
    2 * esize U.univ + wrapNodes + esize lam + 2) + esize trueProg + esize falseProg

/-- The description `wrapCore univ s (encode e)` has size `|s| + |e| + 2|univ| + wrapNodes`. -/
theorem esize_wrapCore (s e : Prog) :
    esize (wrapCore U.univ s (encode e)) = esize s + esize e + 2 * esize U.univ + wrapNodes := by
  show (encode (wrapCore U.univ s (encode e)) : Data).size = _
  rw [← dWrapCore_eq, size_dWrapCore]
  rfl

/-- **What `prep` returns, on the description `(M, (λ, e))` and the input `(n, d)`**: a program
of size at most `progSize λ e`, an input of size at most `|n| + |d| + 1`, and the program runs
on the input within the compressed decider's time plus a constant. -/
theorem prep_output (S' M : Prog) (lam : ℕ) (e : Prog) (n : ℕ) (d : Data) :
    esize (prep G U UT S' ((M, (lam, e)), (n, d))).1 ≤ progSize G U lam e ∧
    (prep G U UT S' ((M, (lam, e)), (n, d))).2.size ≤ esize n + d.size + 1 ∧
    ∃ r t, t ≤ G.bound.eval (n + lam) * (d.size + 1) ^ G.deg + constCost ∧
      (prep G U UT S' ((M, (lam, e)), (n, d))).1.Runs
        (prep G U UT S' ((M, (lam, e)), (n, d))).2 r t := by
  rw [prep_apply]
  split_ifs with h1 h2
  · refine ⟨?_, ?_, encode true, _, ?_, Eval.const _ _⟩
    · simp only [progSize]; omega
    · simp only [Data.size_nil]; omega
    · simp only [constCost]; omega
  · refine ⟨?_, ?_, encode false, _, ?_, Eval.const _ _⟩
    · simp only [progSize]; omega
    · simp only [Data.size_nil]; omega
    · simp only [constCost]; omega
  · refine ⟨?_, ?_, ?_⟩
    · show esize (comprDec G U lam e) ≤ _
      unfold comprDec progSize
      refine le_trans ((G.compress.esize_apply_le _).trans (polynomial_eval_mono _ ?_))
        (Nat.le_add_right _ _) |>.trans (Nat.le_add_right _ _)
      simp only [esize_prod]
      have h1 : esize (G.samplerProg lam) ≤ G.samplerProg.timeBound.eval (esize lam) :=
        G.samplerProg.esize_apply_le lam
      have h2 := esize_wrapCore U (G.samplerProg lam) e
      omega
    · show (Data.cons (encode n) d).size ≤ _
      simp only [Data.size_cons]
      exact le_rfl
    · obtain ⟨r, t, ht, h⟩ := G.decider_time
        (G.samplerProg lam, wrapCore U.univ (G.samplerProg lam) (encode e)) lam n d
      rw [G.output_decider] at h
      exact ⟨r, t, by omega, h⟩

/-! ## The decider's run

Every atom of the cost — `|n|`, `|M| + |λ|`, `|λ|`, `n`, `λ` — is at most `4z + 1` or `z` at
`z = n + |M| + λ`; `muZ` is the common bound on the encodings' sizes. -/

/-- The common bound `5z + 1` on `|n|`, `|M| + |λ|` and `|λ|`. -/
def muZ (z : ℕ) : ℕ := 5 * z + 1

/-- The size of the decider, in `z`. -/
noncomputable def eZ (S' : Prog) (z : ℕ) : ℕ := 2 * muZ z + cD G U UT S'

/-- The size of the description `(M, (λ, dec M λ))`, in `z`. -/
noncomputable def pZ (S' : Prog) (z : ℕ) : ℕ := 3 * muZ z + cD G U UT S' + 2

/-- The size of `F (dec M λ)`, in `z`. -/
noncomputable def feZ (S' : Prog) (z : ℕ) : ℕ := esize (body G U UT S') + pZ G U UT S' z + 35

/-- The size of the input `(n, d)`, in `z` and `|d|`. -/
def vZ (z s : ℕ) : ℕ := muZ z + s + 1

/-- The time of `prep`, in `z` and `|d|`. -/
noncomputable def tpZ (S' : Prog) (z s : ℕ) : ℕ :=
  (prep G U UT S').timeBound.eval (pZ G U UT S' z + vZ z s + 1)

/-- The size of the program `prep` returns, in `z`. -/
noncomputable def sigmaZ (S' : Prog) (z : ℕ) : ℕ :=
  G.compress.timeBound.eval (2 * G.samplerProg.timeBound.eval (muZ z) + eZ G U UT S' z +
    2 * esize U.univ + wrapNodes + muZ z + 2) + esize trueProg + esize falseProg

/-- The time of the program `prep` returns, in `z` and `|d|`. -/
noncomputable def tcZ (z s : ℕ) : ℕ := G.bound.eval (2 * z) * (s + 1) ^ G.deg + constCost

/-- The time of the universal machine on it, in `z` and `|d|`. -/
noncomputable def tuZ (S' : Prog) (z s : ℕ) : ℕ :=
  U.bound.eval (sigmaZ G U UT S' z + vZ z s + tcZ G z s)

/-- The time of `body`, in `z` and `|d|`. -/
noncomputable def tbZ (S' : Prog) (z s : ℕ) : ℕ :=
  tpZ G U UT S' z s + (sigmaZ G U UT S' z + vZ z s + 1 + 1 + tuZ G U UT S' z s + 1) + 1

/-- The time of `F (dec M λ)`, in `z` and `|d|`. -/
noncomputable def tfZ (S' : Prog) (z s : ℕ) : ℕ :=
  tbZ G U UT S' z s + pZ G U UT S' z + vZ z s + 3

/-- The overhead of the fixed point's transfer, in `z`. -/
noncomputable def ovZ (S' : Prog) (z : ℕ) : ℕ := 21 * muZ z + cO G U UT S'

/-- **The master bound on the decider's run**, in `z` and `|d|`. -/
noncomputable def decRunZ (S' : Prog) (z s : ℕ) : ℕ :=
  U.bound.eval (vZ z s + tfZ G U UT S' z s + feZ G U UT S' z) + 3 * vZ z s + ovZ G U UT S' z

/-- **The decider's run**: on `(n, d)`, `dec M λ` halts within `decRunZ (n + |M| + λ) |d|`. -/
theorem dec_cost (S' M : Prog) (lam n : ℕ) (d : Data) :
    ∃ r t, t ≤ decRunZ G U UT S' (n + esize M + lam) d.size ∧
      (dec G U UT S' M lam).Runs (.cons (encode n) d) r t := by
  set z := n + esize M + lam with hz
  set e := dec G U UT S' M lam with he
  -- the atoms
  have hμ : esize M + esize lam ≤ muZ z := by
    have := esize_nat_le_self lam; unfold muZ; omega
  have hn : esize n ≤ muZ z := by
    have := esize_nat_le_self n; unfold muZ; omega
  have hl : esize lam ≤ muZ z := by
    have := esize_nat_le_self lam; unfold muZ; omega
  have he_sz' : esize e ≤ 2 * muZ z + cD G U UT S' := by
    rw [he, esize_dec]; omega
  have he_sz : esize e ≤ eZ G U UT S' z := he_sz'
  have hP_sz : (encode (M, (lam, e)) : Data).size ≤ pZ G U UT S' z := by
    rw [size_descData]; unfold pZ; omega
  have hv_sz : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
  have hv_le : (Data.cons (encode n) d).size ≤ vZ z d.size := by
    rw [hv_sz]; unfold vZ; omega
  have hFe : esize (F G U UT S' M lam e) ≤ feZ G U UT S' z := by
    rw [esize_F_apply]; unfold feZ pZ; omega
  have hov : kleeneOverhead U (F G U UT S' M lam) ≤ ovZ G U UT S' z := by
    rw [kleeneOverhead_eq]; unfold ovZ; omega
  -- the run of `prep`
  set q := prep G U UT S' ((M, (lam, e)), (n, d)) with hq
  obtain ⟨tp, htp, hp⟩ := (prep G U UT S').computes ((M, (lam, e)), (n, d))
  have htp' : tp ≤ tpZ G U UT S' z d.size := by
    refine htp.trans (polynomial_eval_mono _ ?_)
    have h1 : esize ((M, (lam, e)), (n, d)) =
        (encode (M, (lam, e)) : Data).size + (esize n + d.size + 1) + 1 := rfl
    rw [h1]; unfold vZ; omega
  obtain ⟨hc_sz, hw_sz, r, tc, htc, hc⟩ := prep_output G U UT S' M lam e n d
  have hσ : esize q.1 ≤ sigmaZ G U UT S' z := by
    refine hc_sz.trans ?_
    unfold progSize sigmaZ
    have h1 := polynomial_eval_mono G.samplerProg.timeBound hl
    refine Nat.add_le_add_right (Nat.add_le_add_right (polynomial_eval_mono _ ?_) _) _
    omega
  have hw : q.2.size ≤ vZ z d.size := hw_sz.trans (by unfold vZ; omega)
  have htc' : tc ≤ tcZ G z d.size := by
    refine htc.trans ?_
    unfold tcZ
    have := polynomial_eval_mono G.bound (show n + lam ≤ 2 * z by omega)
    have := Nat.mul_le_mul_right ((d.size + 1) ^ G.deg) this
    omega
  -- the universal machine on it
  obtain ⟨tu, htu, hu⟩ := U.time_le q.1 q.2 r tc hc
  have htu' : tu ≤ tuZ G U UT S' z d.size := by
    refine htu.trans (polynomial_eval_mono _ ?_)
    omega
  -- the run of `body`
  have hq_sz : esize q = esize q.1 + q.2.size + 1 := rfl
  have hbody : (body G U UT S').Runs (.cons (encode (M, (lam, e))) (.cons (encode n) d)) r
      (tp + (esize q + 1 + tu + 1) + 1) := by
    have hu' : Eval [encode q] U.univ r tu := hu
    have h₂ := callVar_eval (env := [encode q, encode ((M, (lam, e)), (n, d))]) (i := 0)
      U.closed (v := encode q) (by simp) hu'
    exact Eval.let_ hp h₂
  have hF : (F G U UT S' M lam e).Runs (.cons (encode n) d) r
      (tp + (esize q + 1 + tu + 1) + 1 + (encode (M, (lam, e)) : Data).size +
        (Data.cons (encode n) d).size + 3) :=
    hardcode_time (body_wellScoped G U UT S') hbody
  -- the fixed point
  have hF' : (F G U UT S' M lam (kleeneFix U (F G U UT S' M lam))).Runs
      (.cons (encode n) d) r _ := hF
  obtain ⟨t', ht', hrun⟩ := kleeneFix_runs_of U (F G U UT S' M lam) hF'
  have ht'' : t' ≤ U.bound.eval ((Data.cons (encode n) d).size +
      (tp + (esize q + 1 + tu + 1) + 1 + (encode (M, (lam, e)) : Data).size +
        (Data.cons (encode n) d).size + 3) + esize (F G U UT S' M lam e)) +
      3 * (Data.cons (encode n) d).size + kleeneOverhead U (F G U UT S' M lam) := ht'
  refine ⟨r, t', ht''.trans ?_, hrun⟩
  have htf : tp + (esize q + 1 + tu + 1) + 1 + (encode (M, (lam, e)) : Data).size +
      (Data.cons (encode n) d).size + 3 ≤ tfZ G U UT S' z d.size := by
    unfold tfZ tbZ; omega
  have hev := polynomial_eval_mono U.bound (Nat.add_le_add (Nat.add_le_add hv_le htf) hFe)
  unfold decRunZ
  omega

/-! ## The polynomial form -/

/-- `(|d| + 1) ^ k` is a polynomial cost. -/
theorem polyCost_pow_size (k : ℕ) : PolyCost fun (_ : ℕ) (d : Data) => (d.size + 1) ^ k :=
  ⟨fun _ => 1, k, PolyBounded.const 1, fun _ d => by simp⟩

theorem polyBounded_muZ : PolyBounded muZ := (PolyBounded.id.const_mul 5).add_const 1

theorem polyBounded_eZ (S' : Prog) : PolyBounded (eZ G U UT S') :=
  (polyBounded_muZ.const_mul 2).add_const _

theorem polyBounded_pZ (S' : Prog) : PolyBounded (pZ G U UT S') :=
  ((polyBounded_muZ.const_mul 3).add_const _).add_const 2

theorem polyBounded_feZ (S' : Prog) : PolyBounded (feZ G U UT S') :=
  ((PolyBounded.const _).add (polyBounded_pZ G U UT S')).add_const 35

theorem polyBounded_sigmaZ (S' : Prog) : PolyBounded (sigmaZ G U UT S') :=
  ((PolyBounded.eval _ ((((((PolyBounded.eval _ polyBounded_muZ).const_mul 2).add
    (polyBounded_eZ G U UT S')).add_const _).add_const _).add polyBounded_muZ
    |>.add_const 2)).add_const _).add_const _

theorem polyBounded_ovZ (S' : Prog) : PolyBounded (ovZ G U UT S') :=
  (polyBounded_muZ.const_mul 21).add_const _

theorem polyCost_vZ : PolyCost fun z d => vZ z d.size :=
  ((PolyCost.ofIndex polyBounded_muZ).add PolyCost.size).add (PolyCost.const 1)

theorem polyCost_tpZ (S' : Prog) : PolyCost fun z d => tpZ G U UT S' z d.size :=
  PolyCost.poly _ (((PolyCost.ofIndex (polyBounded_pZ G U UT S')).add polyCost_vZ).add
    (PolyCost.const 1))

theorem polyCost_tcZ : PolyCost fun z d => tcZ G z d.size :=
  ((PolyCost.ofIndex (PolyBounded.eval _ (PolyBounded.id.const_mul 2))).mul
    (polyCost_pow_size G.deg)).add (PolyCost.const _)

theorem polyCost_tuZ (S' : Prog) : PolyCost fun z d => tuZ G U UT S' z d.size :=
  PolyCost.poly _ (((PolyCost.ofIndex (polyBounded_sigmaZ G U UT S')).add polyCost_vZ).add
    (polyCost_tcZ G))

theorem polyCost_tbZ (S' : Prog) : PolyCost fun z d => tbZ G U UT S' z d.size :=
  ((polyCost_tpZ G U UT S').add (((((PolyCost.ofIndex (polyBounded_sigmaZ G U UT S')).add
    polyCost_vZ).add (PolyCost.const 1)).add (PolyCost.const 1)).add
    (polyCost_tuZ G U UT S') |>.add (PolyCost.const 1))).add (PolyCost.const 1)

theorem polyCost_tfZ (S' : Prog) : PolyCost fun z d => tfZ G U UT S' z d.size :=
  (((polyCost_tbZ G U UT S').add (PolyCost.ofIndex (polyBounded_pZ G U UT S'))).add
    polyCost_vZ).add (PolyCost.const 3)

theorem polyCost_decRunZ (S' : Prog) : PolyCost fun z d => decRunZ G U UT S' z d.size :=
  ((PolyCost.poly _ ((polyCost_vZ.add (polyCost_tfZ G U UT S')).add
    (PolyCost.ofIndex (polyBounded_feZ G U UT S')))).add
    ((PolyCost.const 3).mul polyCost_vZ)).add (PolyCost.ofIndex (polyBounded_ovZ G U UT S'))

/-- **The decider's cost, in polynomial form**: a polynomial `Q` and a degree `k`, depending on
`G`, `U`, `UT` and `S'` alone, with `dec M λ` halting on `(n, d)` within
`Q (n + |M| + λ) · (|d| + 1) ^ k`. -/
theorem exists_dec_cost_poly (S' : Prog) : ∃ (Q : Polynomial ℕ) (k : ℕ),
    ∀ (M : Prog) (lam n : ℕ) (d : Data), ∃ r t,
      t ≤ Q.eval (n + esize M + lam) * (d.size + 1) ^ k ∧
        (dec G U UT S' M lam).Runs (.cons (encode n) d) r t := by
  obtain ⟨Cq, k, hCq, hb⟩ := polyCost_decRunZ G U UT S'
  refine ⟨hCq.poly, k, fun M lam n d => ?_⟩
  obtain ⟨r, t, ht, h⟩ := dec_cost G U UT S' M lam n d
  exact ⟨r, t, ht.trans ((hb _ d).trans (Nat.mul_le_mul_right _ (hCq.le_poly_eval _))), h⟩

/-- The polynomial of the decider's cost. -/
noncomputable def decCostPoly (S' : Prog) : Polynomial ℕ :=
  (exists_dec_cost_poly G U UT S').choose

/-- The degree of the decider's cost in the input size. -/
noncomputable def decCostDeg (S' : Prog) : ℕ :=
  (exists_dec_cost_poly G U UT S').choose_spec.choose

theorem dec_cost_spec (S' M : Prog) (lam n : ℕ) (d : Data) : ∃ r t,
    t ≤ (decCostPoly G U UT S').eval (n + esize M + lam) * (d.size + 1) ^ decCostDeg G U UT S' ∧
      (dec G U UT S' M lam).Runs (.cons (encode n) d) r t :=
  (exists_dec_cost_poly G U UT S').choose_spec.choose_spec M lam n d

/-! ## The wrapped decider -/

/-- **The decider of `𝒱^halt`, on every input**: the wrapper's cost with the inner cost in
polynomial form. -/
theorem Vhalt_decider_cost (S' M : Prog) (lam n : ℕ) (d : Data) :
    ∃ r t, t ≤ wrapCoreCost U (G.sampler lam) (dec G U UT S' M lam)
        (fun m => G.bound.eval (m + lam)) G.deg n
        ((decCostPoly G U UT S').eval (n + esize M + lam) * (d.size + 1) ^ decCostDeg G U UT S')
        d.size ∧
      (Vhalt G U UT S' M lam).decider.prog.Runs (.cons (encode n) d) r t :=
  wrapCore_cost' U (G.sampler lam) (dec G U UT S' M lam) _ G.deg
    (fun m d => G.sampler_time lam m d) n
    (fun s => (decCostPoly G U UT S').eval (n + esize M + lam) * (s + 1) ^ decCostDeg G U UT S')
    (fun d => dec_cost_spec G U UT S' M lam n d) d

/-- The compressed sampler's program at `λ` has size at most `samplerProg`'s time bound at
`|λ|`. -/
theorem esize_sampler_prog_le (lam : ℕ) :
    esize (G.sampler lam).prog ≤ G.samplerProg.timeBound.eval (esize lam) := by
  rw [← G.samplerProg_eq]
  exact G.samplerProg.esize_apply_le lam

/-- The size of the compressed sampler's program, in `z`. -/
noncomputable def sampSizeZ (z : ℕ) : ℕ := G.samplerProg.timeBound.eval (muZ z)

/-- The compressor's bound `poly(m, λ)`, in `z`. -/
noncomputable def betaZ (z : ℕ) : ℕ := G.bound.eval (2 * z)

/-- `wrapHeadZ`, in `z`. -/
noncomputable def headWZ (z : ℕ) : ℕ :=
  sampSizeZ G z + muZ z + (encode CL.Sampler.Query.dimension : Data).size + (4 * betaZ G z + 1) +
    betaZ G z * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ G.deg +
    U.bound.eval (sampSizeZ G z + (muZ z + (encode CL.Sampler.Query.dimension : Data).size + 1) +
      betaZ G z * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ G.deg) +
    (betaZ G z + 2) * ((betaZ G z + 1) * (4 * betaZ G z + 14) + 7 * (4 * betaZ G z + 1) +
      8 * betaZ G z + 90) + 10

/-- **The master bound on the wrapped decider's cost**, in `z`: `wrapCoreCost` with every atom
replaced by its bound. -/
noncomputable def WZ (S' : Prog) (z : ℕ) : ℕ :=
  (60 * headWZ G U z ^ 2 + 4) + 2 * (60 * (z + betaZ G z + 30) ^ 2) +
    (2 * (eZ G U UT S' z + muZ z + z + 2) +
      U.bound.eval (eZ G U UT S' z + (muZ z + z + 1) +
        (decCostPoly G U UT S').eval (3 * z) * (z + 1) ^ decCostDeg G U UT S')) + 20

theorem polyBounded_sampSizeZ : PolyBounded (sampSizeZ G) := PolyBounded.eval _ polyBounded_muZ

theorem polyBounded_betaZ : PolyBounded (betaZ G) :=
  PolyBounded.eval _ (PolyBounded.id.const_mul 2)

theorem polyBounded_headWZ : PolyBounded (headWZ G U) := by
  have hσ := polyBounded_sampSizeZ G
  have hβ := polyBounded_betaZ G
  have hμ := polyBounded_muZ
  unfold headWZ
  exact (((((((hσ.add hμ).add (PolyBounded.const _)).add ((hβ.const_mul 4).add_const 1)).add
    (hβ.mul (PolyBounded.const _))).add
    (PolyBounded.eval _ ((hσ.add ((hμ.add_const _).add_const 1)).add
      (hβ.mul (PolyBounded.const _))))).add
    ((hβ.add_const 2).mul ((((hβ.add_const 1).mul ((hβ.const_mul 4).add_const 14)).add
      (((hβ.const_mul 4).add_const 1).const_mul 7)).add
      ((hβ.const_mul 8).add_const 90)))).add_const 10)

theorem polyBounded_WZ (S' : Prog) : PolyBounded (WZ G U UT S') := by
  have hz := PolyBounded.id
  have hμ := polyBounded_muZ
  have he := polyBounded_eZ G U UT S'
  unfold WZ
  exact ((((((polyBounded_headWZ G U).pow 2).const_mul 60).add_const 4).add
    (((((hz.add (polyBounded_betaZ G)).add_const 30).pow 2).const_mul 60).const_mul 2)).add
    (((((he.add hμ).add hz).add_const 2).const_mul 2).add
      (PolyBounded.eval _ (((he.add ((hμ.add hz).add_const 1)).add
        ((PolyBounded.eval _ (hz.const_mul 3)).mul ((hz.add_const 1).pow _))))))).add_const 20

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

/-- **The wrapped decider's cost is below the master bound** at any `z` above the index, `|M|`,
`λ` and the input size. -/
theorem wrapCoreCost_le_WZ (S' M : Prog) {lam m s z : ℕ} (hM : esize M ≤ z) (hm : m ≤ z)
    (hl : lam ≤ z) (hs : s ≤ z) :
    wrapCoreCost U (G.sampler lam) (dec G U UT S' M lam) (fun m => G.bound.eval (m + lam)) G.deg
        m ((decCostPoly G U UT S').eval (m + esize M + lam) * (s + 1) ^ decCostDeg G U UT S') s ≤
      WZ G U UT S' z := by
  have hμ : esize M + esize lam ≤ muZ z := by
    have := esize_nat_le_self lam; unfold muZ; omega
  have hem : esize m ≤ muZ z := by
    have := esize_nat_le_self m; unfold muZ; omega
  have hel : esize lam ≤ muZ z := by
    have := esize_nat_le_self lam; unfold muZ; omega
  have hσ : esize (G.sampler lam).prog ≤ sampSizeZ G z :=
    (esize_sampler_prog_le G lam).trans (polynomial_eval_mono _ hel)
  have hβ : G.bound.eval (m + lam) ≤ betaZ G z := polynomial_eval_mono _ (by omega)
  have hdim : (G.sampler lam).dim m ≤ betaZ G z := (G.sampler_dim _ m).trans hβ
  have hedim : esize ((G.sampler lam).dim m) ≤ 4 * betaZ G z + 1 :=
    (esize_nat_le_self _).trans (by omega)
  have hsdim : Nat.size ((G.sampler lam).dim m) ≤ betaZ G z :=
    (Nat.size_le.2 Nat.lt_two_pow_self).trans hdim
  have he : esize (dec G U UT S' M lam) ≤ eZ G U UT S' z := by
    rw [esize_dec]; unfold eZ; omega
  have hQ : (decCostPoly G U UT S').eval (m + esize M + lam) * (s + 1) ^ decCostDeg G U UT S' ≤
      (decCostPoly G U UT S').eval (3 * z) * (z + 1) ^ decCostDeg G U UT S' :=
    Nat.mul_le_mul (polynomial_eval_mono _ (by omega)) (Nat.pow_le_pow_left (by omega) _)
  have hcheck : checkCost s ((G.sampler lam).dim m) ≤ 60 * (z + betaZ G z + 30) ^ 2 := by
    unfold checkCost; gcongr
  have hhead : wrapHeadZ U (G.sampler lam) (fun m => G.bound.eval (m + lam)) G.deg m ≤
      headWZ G U z := by
    unfold wrapHeadZ headWZ; gcongr
  unfold wrapCoreCost WZ
  gcongr

/-! ## The clauses of `IsBounded` -/

/-- **The sampler clauses and the parameter inequality**: past a threshold on `λ`, at every
index `m ≥ 2` the compressor's bound `poly(m, λ)` is below `m ^ λ`, so the compressed sampler
at `λ` has dimension at most `m ^ λ` and runs within `m ^ λ · (|d| + 1) ^ λ`. -/
theorem sampler_clauses_paper : ∃ n₀, ∀ lam, n₀ ≤ lam → ∀ m, 2 ≤ m →
    G.bound.eval (m + lam) ≤ m ^ lam ∧ (G.sampler lam).dim m ≤ m ^ lam ∧
      (G.sampler lam).TimeBoundAt m (m ^ lam) lam := by
  obtain ⟨n₀, hn₀⟩ := (PolyBounded.eval G.bound PolyBounded.id).absorb
  refine ⟨max n₀ G.deg, fun lam hl m hm => ?_⟩
  have h1 : G.bound.eval (m + lam) ≤ m ^ lam := by
    have := hn₀ lam (le_trans (le_max_left _ _) hl) m hm 1 le_rfl
    rw [one_pow, mul_one, mul_one] at this
    exact (polynomial_eval_mono _ (by omega)).trans this
  exact ⟨h1, (G.sampler_dim _ m).trans h1,
    (G.sampler_time lam m).mono h1 (le_trans (le_max_right _ _) hl)⟩

/-- **The decider clause**: past a threshold on `λ`, for `|M| ≤ λ`, the decider of `𝒱^halt`
runs within `m ^ λ · (|d| + 1) ^ λ` at every index `m ≥ 2`. -/
theorem decider_clause_paper (S' : Prog) : ∃ n₀, ∀ (M : Prog) (lam : ℕ), n₀ ≤ lam →
    esize M ≤ lam → ∀ m, 2 ≤ m →
    (Vhalt G U UT S' M lam).decider.TimeBoundAt m (m ^ lam) lam := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_WZ G U UT S').absorb
  refine ⟨n₀, fun M lam hl hM m hm d => ?_⟩
  obtain ⟨r, t, ht, hrun⟩ := Vhalt_decider_cost G U UT S' M lam m d
  refine ⟨r, t, ht.trans ?_, hrun⟩
  have hz := hn₀ lam hl m hm (d.size + 1) (by omega)
  refine le_trans (wrapCoreCost_le_WZ G U UT S' M ?_ ?_ ?_ ?_) hz
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- The size of `𝒱^halt` beyond `2|M|`, as a function of `|λ|`. -/
noncomputable def vsizeZ (S' : Prog) (l : ℕ) : ℕ :=
  G.samplerProg.timeBound.eval l + 2 * l + (cD G U UT S' + 2 * esize U.univ + wrapNodes)

theorem polyBounded_vsizeZ (S' : Prog) : PolyBounded (vsizeZ G U UT S') :=
  ((PolyBounded.eval _ PolyBounded.id).add (PolyBounded.id.const_mul 2)).add_const _

/-- The size of `𝒱^halt M λ` is at most `2|M| + vsizeZ |λ|`. -/
theorem Vhalt_size_le (S' M : Prog) (lam : ℕ) :
    (Vhalt G U UT S' M lam).size ≤ 2 * esize M + vsizeZ G U UT S' (esize lam) := by
  have h1 := esize_sampler_prog_le G lam
  have h2 : esize (Vhalt G U UT S' M lam).decider.prog =
      esize (G.sampler lam).prog + esize (dec G U UT S' M lam) + 2 * esize U.univ + wrapNodes := by
    rw [Vhalt_decider_prog, esize_wrapCore]
  have h3 := esize_dec G U UT S' M lam
  rw [Verifier.size]
  refine max_le ?_ ?_
  · show esize (G.sampler lam).prog ≤ _
    unfold vsizeZ; omega
  · show esize (Vhalt G U UT S' M lam).decider.prog ≤ _
    rw [h2, h3]; unfold vsizeZ; omega

/-- **The size clause**: past a threshold on `λ`, for `4|M| ≤ λ`, `|𝒱^halt M λ| ≤ λ`. -/
theorem size_clause_paper (S' : Prog) : ∃ n₀, ∀ (M : Prog) (lam : ℕ), n₀ ≤ lam →
    4 * esize M ≤ lam → (Vhalt G U UT S' M lam).size ≤ lam := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_vsizeZ G U UT S').absorb_log 1 4
  refine ⟨n₀, fun M lam hl hM => ?_⟩
  have h := hn₀ lam hl
  have h1 : vsizeZ G U UT S' (esize lam) ≤ vsizeZ G U UT S' (1 + 4 * Nat.size lam) := by
    have := esize_nat_le lam
    unfold vsizeZ
    have := polynomial_eval_mono G.samplerProg.timeBound
      (show esize lam ≤ 1 + 4 * Nat.size lam by omega)
    omega
  have h2 := Vhalt_size_le G U UT S' M lam
  omega

/-! ## `lem:lambda` -/

/-- **`lem:lambda`, the paper's form**: there is a threshold `Λ₀`, depending on `G`, `U`, `UT`
and `S'` alone, such that for every machine `M` and every `λ ≥ Λ₀ + 4|M|`, the verifier
`𝒱^halt M λ` is `λ`-bounded and the compressor's bound `poly(n, λ)` is below `n ^ λ` at every
level `n ≥ 2`. -/
theorem exists_lamBound (S' : Prog) : ∃ Λ₀ : ℕ, ∀ (M : Prog) (lam : ℕ),
    Λ₀ + 4 * esize M ≤ lam →
      (Vhalt G U UT S' M lam).IsBounded lam ∧
        ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam := by
  obtain ⟨nS, hS⟩ := sampler_clauses_paper G
  obtain ⟨nD, hD⟩ := decider_clause_paper G U UT S'
  obtain ⟨nZ, hZ⟩ := size_clause_paper G U UT S'
  refine ⟨max nS (max nD nZ), fun M lam hl => ⟨⟨fun m hm => ?_, ?_⟩, fun n hn => ?_⟩⟩
  · obtain ⟨-, h1, h2⟩ := hS lam (by omega) m hm
    exact ⟨h1, h2, hD M lam (by omega) (by omega) m hm⟩
  · exact hZ M lam (by omega) (by omega)
  · exact (hS lam (by omega) n hn).1

/-- The threshold of `lem:lambda`. -/
noncomputable def Lam0 (S' : Prog) : ℕ := (exists_lamBound G U UT S').choose

end MIPRE.Halting


