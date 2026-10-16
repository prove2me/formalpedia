-- Prove2me | Definitions.Def_MIPRE_Foundations_Pipeline_Budget
-- name    : MIPRE_Foundations_Pipeline_Budget
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:20:41.009342+00:00
-- url     : https://prove2.me/theorems/33a57e09-86cd-40c2-8bf2-fe3c69a9fa17
-- title:
--   Resource budgets of a normal form verifier at one index
-- statement:
--   The four pipeline transformations (introspection, oracularization, answer reduction, parallel repetition) state their complexity as bounds on the output verifier in terms of bounds on the input: the paper's $\mathrm{TIME}_{\mathcal S}(n)$, $\mathrm{TIME}_{\mathcal D}(n)$, dimension $s(n)$ and parsing bound $B_{\mathcal D}(n)$. This bundle is the vocabulary for those clauses.
--
--   A `Budget` is a structure of five naturals: `S`, bounding the sampler's running-time coefficient; `d`, the dimension of its questions; `D`, the decider's running-time coefficient; `k`, the degree of both running times in the size of the input; `B`, the length of the answers the decider can accept. `Budget.uniform z k` is $\langle z,z,z,k,z\rangle$. `Budget.Le R R'` is the pointwise comparison $R.S \le R'.S \wedge R.d \le R'.d \wedge R.D \le R'.D \wedge R.k \le R'.k \wedge R.B \le R'.B$.
--
--   For a normal form verifier $V$ of any level, an index $n$ and a budget $R$, `Verifier.Within V n R` says that $V$ respects $R$ at $n$:
--
--   $$V.\mathrm{Within}\ n\ R \;:=\; \mathcal S_V.\mathrm{TimeBoundAt}\ n\ R.S\ R.k \;\wedge\; \mathcal S_V.\mathrm{dim}\ n \le R.d \;\wedge\; \mathcal D_V.\mathrm{TimeBoundAt}\ n\ R.D\ R.k \;\wedge\; V.\mathrm{RejectsLong}\ n\ R.B .$$
--
--   The embedded lemmas are the five simp lemmas for the projections of `uniform z k`, the monotonicity of `RejectsLong` in its bound and of `Within` along `Budget.Le`, the four projections of a `Within` hypothesis, and `Within.valStar_eq`: if `V.Within n R` and `R.B ≤ T` then `V.valStar n T = V.valStar n R.B`.
--
--   `Introspection`, `AnswerReduction` and `Repetition` state their complexity clauses with `Within`; `GapCompression.ofPipeline` chains them through `Within.mono` and `Within.valStar_eq`.
--
--   **Formalization Note** `D.TimeBoundAt n T k` means that on every datum `d` the program halts on `(encode n, d)` within cost `T * (d.size + 1) ^ k`: coefficient `T`, input-size degree `k`; the degree is the fifth quantity, which the paper's absolute-time statements do not carry. `V.RejectsLong n T` is `∀ x y a b, T < a.length ∨ T < b.length → ¬ V.decider.Accepts n x y a b`, the ambient reading of "the decider first parses its answers against $B_{\mathcal D}(n)$". `valStar n T` is the entangled value of the game at index `n` with answers of length at most `T`. `Budget` is a `structure` (listed as `inductive`); nothing here has content beyond the definitions.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/Budget.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/Budget.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue

/-!
# Resource budgets of a verifier at one index

The four transformations of chapter 6 of the blueprint (introspection, oracularization,
answer reduction, parallel repetition) each take a normal form verifier and return one, and
each states its complexity as bounds on the output *in terms of bounds on the input*: the
paper's `TIME_𝒮(n)`, `TIME_𝒟(n)`, the dimension `s(n)` and the timeout bound `B_𝒟(n)` of a
decider in timeout-counter form. In the ambient cost model these are five numbers per index
(`MIPRE.Verifier` explains the degree): the running-time coefficients of the sampler and the
decider, their common degree in the size of the input, a bound on the dimension of the
questions, and a length of answers beyond which the decider rejects (`Verifier.RejectsLong`,
the ambient reading of "the decider first parses its answers against `B_𝒟(n)`"). `Budget`
collects them and `Verifier.Within V n R` says `V` respects `R` at index `n`.

Nothing here has content: it is the vocabulary in which the hypothesis structures of
`MIPRE.Foundations.Pipeline` state their complexity clauses, so that the composition
`MIPRE.GapCompression.ofPipeline` can chain them.
-/

namespace MIPRE

open Cost

/-- A resource budget at one index: a bound `S` on the sampler's running-time coefficient, `d`
on the dimension of its questions, `D` on the decider's running-time coefficient, `k` on the
degree of both running times in the size of the input, and `B` on the length of the answers
the decider can accept. -/
structure Budget where
  /-- Sampler running-time coefficient (`TIME_𝒮(n)`). -/
  S : ℕ
  /-- Dimension of the questions (`s(n)`). -/
  d : ℕ
  /-- Decider running-time coefficient (`TIME_𝒟(n)`). -/
  D : ℕ
  /-- Degree of both running times in the size of the input. -/
  k : ℕ
  /-- Length beyond which the decider rejects an answer (`B_𝒟(n)`). -/
  B : ℕ

namespace Budget

/-- The budget with the same bound `z` on every quantity, at degree `k`. -/
def uniform (z k : ℕ) : Budget := ⟨z, z, z, k, z⟩

@[simp] theorem uniform_S (z k : ℕ) : (uniform z k).S = z := rfl
@[simp] theorem uniform_d (z k : ℕ) : (uniform z k).d = z := rfl
@[simp] theorem uniform_D (z k : ℕ) : (uniform z k).D = z := rfl
@[simp] theorem uniform_k (z k : ℕ) : (uniform z k).k = k := rfl
@[simp] theorem uniform_B (z k : ℕ) : (uniform z k).B = z := rfl

/-- Pointwise comparison of budgets. -/
def Le (R R' : Budget) : Prop :=
  R.S ≤ R'.S ∧ R.d ≤ R'.d ∧ R.D ≤ R'.D ∧ R.k ≤ R'.k ∧ R.B ≤ R'.B

end Budget

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- `V` respects the budget `R` at index `n`: its sampler runs within `R.S` at degree `R.k`,
its questions have dimension at most `R.d`, its decider runs within `R.D` at degree `R.k`, and
its decider rejects every answer longer than `R.B`. -/
def Within (n : ℕ) (R : Budget) : Prop :=
  V.sampler.TimeBoundAt n R.S R.k ∧ V.sampler.dim n ≤ R.d ∧
    V.decider.TimeBoundAt n R.D R.k ∧ V.RejectsLong n R.B

variable {V}

theorem RejectsLong.mono {n T T' : ℕ} (hT : T ≤ T') (h : V.RejectsLong n T) :
    V.RejectsLong n T' := fun x y a b hab =>
  h x y a b (by omega)

theorem Within.mono {n : ℕ} {R R' : Budget} (h : V.Within n R) (hle : R.Le R') :
    V.Within n R' :=
  ⟨h.1.mono hle.1 hle.2.2.2.1, h.2.1.trans hle.2.1, h.2.2.1.mono hle.2.2.1 hle.2.2.2.1,
    RejectsLong.mono hle.2.2.2.2 h.2.2.2⟩

theorem Within.sampler_time {n : ℕ} {R : Budget} (h : V.Within n R) :
    V.sampler.TimeBoundAt n R.S R.k := h.1

theorem Within.sampler_dim {n : ℕ} {R : Budget} (h : V.Within n R) :
    V.sampler.dim n ≤ R.d := h.2.1

theorem Within.decider_time {n : ℕ} {R : Budget} (h : V.Within n R) :
    V.decider.TimeBoundAt n R.D R.k := h.2.2.1

theorem Within.rejectsLong {n : ℕ} {R : Budget} (h : V.Within n R) :
    V.RejectsLong n R.B := h.2.2.2

/-- A verifier respecting a budget has, at any larger answer bound, the same value as at the
budget's answer bound. -/
theorem Within.valStar_eq {n : ℕ} {R : Budget} (h : V.Within n R) {T : ℕ} (hT : R.B ≤ T) :
    V.valStar n T = V.valStar n R.B :=
  V.valStar_eq_of_rejects hT h.rejectsLong

end Verifier

end MIPRE


