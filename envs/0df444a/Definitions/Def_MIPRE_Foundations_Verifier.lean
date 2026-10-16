-- Prove2me | Definitions.Def_MIPRE_Foundations_Verifier
-- name    : MIPRE_Foundations_Verifier
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:28:40.365758+00:00
-- url     : https://prove2.me/theorems/1f25f977-6f49-44cc-8261-a810ad8a024b
-- title:
--   Deciders, normal form verifiers, their games and $\lambda$-boundedness
-- statement:
--   This bundle holds the module defining normal form verifiers, the pipeline's presentation of infinite families of games (blueprint `def:decider`, `def:normal-verifier`, `def:lambda-bounded`). A `Decider` is a structure with a program `prog` of the ambient cost model and a proof `closed` that it is well scoped at one variable. For a decider $\mathcal{D}$: `Decider.Accepts n x y a b` says that $\mathcal{D}$ halts on $\mathrm{encode}(n, x, y, a, b)$ with output $\mathrm{encode}\,\mathrm{true}$; `Decider.TimeBoundAt n T k`, the reading of $\mathrm{TIME}_{\mathcal{D}}(n) \le T$, says
--
--   $$\forall d : \mathrm{Data},\quad \mathrm{HaltsWithin}\ \mathcal{D}.\mathrm{prog}\ \big(\mathrm{cons}\,(\mathrm{encode}\,n)\,d\big)\ \big(T \cdot (|d| + 1)^k\big),$$
--
--   a bound on every input of index $n$; `Decider.size` is $\mathrm{esize}(\mathrm{prog})$. A `Verifier ℓ` is a structure with a sampler `sampler : CL.Sampler ℓ`, a decider, and the field `accepts_length`: accepted questions have the sampler's dimension, $|x| = |y| = s(n)$. For a verifier $\mathcal{V}$: `size` is $\max(|\mathcal{S}|, |\mathcal{D}|)$; `Answers T` is the type of bit strings of length at most $T$ (with `DecidableEq` and `Fintype` instances); `Questions n` is $\mathbb{F}_2^{s(n)}$; `game n T` is the game $\mathcal{V}_n$ with answers of length at most $T$, questions distributed by the sampler at $n$, a pair accepted when the decider accepts the bit strings of questions and answers; `valStar n T` is its quantum value; `IsBounded λ` says that for all $n \ge 2$, $s(n) \le n^\lambda$ and both sampler and decider satisfy `TimeBoundAt n (n^λ) λ`, and $|\mathcal{V}| \le \lambda$. The embedded lemmas are the monotonicity of `TimeBoundAt` in $T$ and $k$, the injectivity of an answer's bit reads below $T + 1$ with the finiteness of `Answers T`, and `IsBounded.two_le`: $\lambda$-boundedness forces $2 \le \lambda$.
--
--   **Formalization Note** The paper's $\mathcal{V}_n$ is the case $T = \mathrm{TIME}_{\mathcal{D}}(n)$; timeouts are not modelled. The paper's bound is uniform over all inputs; the ambient model has no cursor into its input, so the bound is read as polynomial in the input size with coefficient $T$ and degree $k$, the degree a separate parameter because the universal machine's overhead composes degrees. The clause $s(n) \le n^\lambda$, in the paper a consequence of the sampler's running time, is required directly. `Answers T` is `{a : BitStr // a.length ≤ T}`; `Questions n` is an `abbrev`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Verifier.lean; blueprint def:decider, def:lambda-bounded, def:normal-verifier; paper games.tex, Definitions def:decider, def:normal-ver, def:normal-game, def:lambda (ledger node 1.1.3)

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Verifier.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Deciders and normal form verifiers

Blueprint `def:decider`, `def:normal-verifier` and `def:lambda-bounded` (paper `games.tex`,
Definitions `def:decider`, `def:normal-ver`, `def:normal-game`, `def:lambda`; ledger node
`1.1.3`). A normal form verifier is the uniform way the pipeline presents an infinite family
of games: a sampler (`MIPRE.CL.Sampler`), which produces the questions, and a decider, which
checks the answers, both programs of the ambient cost model (`MIPRE.Cost`).

* `MIPRE.Decider`: a program whose one input is `encode (n, x, y, a, b)`; it *accepts* when it
  halts with output `1` (`Decider.Accepts`), and rejects otherwise.
  `Decider.TimeBoundAt n T k` is `TIME_𝒟(n) ≤ T`, read as halting within cost
  `T · (|d| + 1)^k` on every input `(n, d)`, well formed or not: the paper's bound is uniform
  over all inputs, which the ambient model cannot achieve (see below), so the running time is
  bounded by a polynomial in the size of the input whose coefficient is `T` and whose degree
  is `k`.
* `MIPRE.Verifier ℓ`: a sampler and a decider, with the paper's requirement that the decider
  accept only questions of the sampler's dimension `s(n)` (it "first checks
  `|x| = |y| = s(n)`", `Verifier.accepts_length`).
* `Verifier.game n T`: the game `𝒱_n` — questions `𝔽₂^{s(n)}`, answers the bit strings of
  length at most `T` (`Verifier.Answers T`), the sampler's distribution, and acceptance by the
  decider. The paper's `𝒱_n` is the case `T = TIME_𝒟(n)`; the bound is a parameter here
  because every statement about `𝒱_n` carries an explicit time bound anyway, and taking the
  exact supremum would only add a degenerate case (`TIME_𝒟(n) = ∞`, where the paper's game is
  undefined) to every definition. `Verifier.syncGame` is the same game as a
  `SynchronousGame`, under the condition on the decider that makes it one
  (`Verifier.IsSynchronousAt`).
* `Verifier.IsBounded λ`: `def:lambda-bounded`, `TIME_𝒮(n), TIME_𝒟(n) ≤ n^λ` with degree `λ`
  in the input size, and `s(n) ≤ n^λ`, for `n ≥ 2`, and `|𝒱| ≤ λ`.

Timeouts are not modelled: in the ambient cost model a decider with `TIME_𝒟(n) < ∞` halts on
every input of index `n`, and the paper's convention that a timeout is a rejection is the
convention that anything but halting with output `1` is.

## Why the time bound is a polynomial in the input size

The paper's `TIME_𝒟(n)` is the maximum of the running time over *all* inputs of index `n`,
finite because a Turing machine can stop reading after a bounded prefix. The ambient model
has no cursor into its input: a value is inspected in place by `elim`, one node per step, but
a loop can carry the rest of a list from one iteration to the next only by copying it
(`Eval.var` costs the size of the value), so walking `j` cells of a list of size `s` costs
about `j · s`, and no program can check `|x| = s(n)` for unbounded `s(n)` within a cost
independent of `|x|`. A bound uniform over all inputs is therefore satisfiable only by
deciders that never look past a fixed depth of their input — none that satisfies
`Verifier.accepts_length` with `s(n) → ∞`.

The degree `k` is needed as well as the coefficient `T`, and this is forced by the one thing
every decider of the pipeline does: run another program through the universal machine. The
overhead of `MIPRE.Cost.UniversalMachine` is a polynomial `Q` in `|c| + |v| + t`, of degree
well above one (`Cost.Universal.univPoly`), so a simulated run costing `T · (|d| + 1)^k`
becomes one costing about `Q(T · (|d| + 1)^k)`, of degree `k · deg Q` in the input size. No
fixed degree is closed under the composition the deciders perform; a *bounded* degree is, and
`k` is that bound. Taking one parameter for both — `T · (|d| + 1)^T` — would be closed too,
but then `λ`-boundedness would read as degree `n^λ` in the input size, which is not a
polynomial-time condition at all and would make `MIPRE.GapCompression` assume compression of
verifiers the paper's proof cannot compress.

So `TimeBoundAt n T k` is "cost at most `T · (|d| + 1)^k`", and `λ`-boundedness bounds both
parameters by `λ`'s: coefficient `n^λ`, degree `λ`. The consequence `s(n) ≤ TIME_𝒮(n)` of the
paper, which depended on the uniform bound, is put into `IsBounded` as a clause.
-/

namespace MIPRE

open Cost

/-! ## Deciders -/

/-- `def:decider`: a decider is a program whose one input is `encode (n, x, y, a, b)` — an
index `n` and the questions and answers `x, y, a, b` of the two players. -/
structure Decider where
  /-- The program. -/
  prog : Prog
  /-- The program is closed. -/
  closed : prog.WellScoped 1

namespace Decider

variable (D : Decider)

/-- The decider **accepts** `(n, x, y, a, b)`: it halts with output `1`. Any other outcome —
output `0`, or not halting — is rejection. -/
def Accepts (n : ℕ) (x y a b : BitStr) : Prop :=
  ∃ t, D.prog.Runs (encode (n, x, y, a, b)) (encode true) t

/-- `TIME_𝒟(n) ≤ T`: the decider halts within cost `T · (|d| + 1)^k` on every input `(n, d)`,
well formed or not — the paper's bound, read as a polynomial in the size of the input with
coefficient `T` and degree `k` (see the module docstring). -/
def TimeBoundAt (n T k : ℕ) : Prop :=
  ∀ d : Data, HaltsWithin D.prog (.cons (encode n) d) (T * (d.size + 1) ^ k)

/-- The bound is monotone in both parameters. -/
theorem TimeBoundAt.mono {D : Decider} {n T k T' k' : ℕ} (h : D.TimeBoundAt n T k)
    (hT : T ≤ T') (hk : k ≤ k') : D.TimeBoundAt n T' k' := fun d =>
  let ⟨r, t, ht, hrun⟩ := h d
  ⟨r, t, ht.trans (Nat.mul_le_mul hT (Nat.pow_le_pow_right (by omega) hk)), hrun⟩

/-- The description length `|𝒟|`. -/
def size : ℕ := esize D.prog

end Decider

/-! ## Normal form verifiers -/

/-- `def:normal-verifier`: a normal form verifier is a sampler and a decider, the decider
accepting only questions of the sampler's dimension (the paper's requirement that it first
check `|x| = |y| = s(n)` and reject otherwise). The number of levels of the verifier is that
of its sampler. -/
structure Verifier (ℓ : ℕ) where
  /-- The sampler, producing the questions. -/
  sampler : CL.Sampler ℓ
  /-- The decider, checking the answers. -/
  decider : Decider
  /-- The decider accepts only questions of the sampler's dimension. -/
  accepts_length : ∀ n x y a b, decider.Accepts n x y a b →
    x.length = sampler.dim n ∧ y.length = sampler.dim n

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- The description length `|𝒱| = max(|𝒮|, |𝒟|)`. -/
def size : ℕ := max V.sampler.size V.decider.size

/-- The answer alphabet of `𝒱_n`: the bit strings of length at most `T`, the paper's
`{0,1}^{≤ TIME_𝒟(n)}`. -/
def Answers (T : ℕ) : Type := {a : BitStr // a.length ≤ T}

namespace Answers

instance (T : ℕ) : DecidableEq (Answers T) :=
  inferInstanceAs (DecidableEq {a : BitStr // a.length ≤ T})

/-- An answer is determined by its bits at the positions below `T + 1`. -/
theorem getElem?_injective (T : ℕ) :
    Function.Injective fun (a : Answers T) (i : Fin (T + 1)) => a.1[(i : ℕ)]? := by
  intro a b h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < T + 1
  · exact congrFun h ⟨i, hi⟩
  · have ha := a.2
    have hb := b.2
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

instance (T : ℕ) : Finite (Answers T) := Finite.of_injective _ (getElem?_injective T)

noncomputable instance (T : ℕ) : Fintype (Answers T) := Fintype.ofFinite _

end Answers

/-- The question alphabet of `𝒱_n`: `𝔽₂^{s(n)}`. -/
abbrev Questions (n : ℕ) : Type := Fin (V.sampler.dim n) → CL.𝔽₂

open Classical in
/-- The game `𝒱_n` with answers of length at most `T` (the paper's `def:normal-game`, at
`T = TIME_𝒟(n)`): questions `𝔽₂^{s(n)}` distributed as the sampler prescribes, answers
accepted when the decider accepts them. -/
noncomputable def game (n T : ℕ) :
    Game (V.Questions n) (V.Questions n) (Answers T) (Answers T) where
  μ := V.sampler.dist n
  μ_nonneg := V.sampler.dist_nonneg n
  μ_sum_one := V.sampler.sum_dist n
  D x y a b := decide (V.decider.Accepts n (CL.toBits x) (CL.toBits y) a.1 b.1)

/-- `val*(𝒱_n)`, the quantum value of the `n`-th game with answers of length at most `T`. -/
noncomputable def valStar (n T : ℕ) : ℝ := quantumValue (V.game n T)

/-- `def:lambda-bounded`: `TIME_𝒮(n), TIME_𝒟(n) ≤ n^λ` — at degree `λ` in the size of the
input (`TimeBoundAt`) — and `s(n) ≤ n^λ`, for all `n ≥ 2`, and `|𝒱| ≤ λ`. The clause
`s(n) ≤ n^λ` is, in the paper, a consequence of the time bound (the sampler writes `s(n)`
output cells); with the running time bounded by a polynomial in the input size it is not, and
it is required directly. -/
def IsBounded (lam : ℕ) : Prop :=
  (∀ n, 2 ≤ n → V.sampler.dim n ≤ n ^ lam ∧
    V.sampler.TimeBoundAt n (n ^ lam) lam ∧ V.decider.TimeBoundAt n (n ^ lam) lam) ∧
    V.size ≤ lam

/-- **`λ`-boundedness forces `2 ≤ λ`**, through the size clause: every program encodes to a
`Data.cons`, so `2 ≤ |𝒟| ≤ |𝒱| ≤ λ` (`Cost.Prog.two_le_esize`).

This is small and entirely load-bearing. The time clauses of `IsBounded` are all guarded by
`2 ≤ n`, so at `n = 0, 1` they say nothing and no budget exists — acceptance at those indices
is genuinely `Σ₁`. What rules those indices out is not an extra hypothesis anywhere but this
lemma: a verifier that is `n`-bounded is so at an `n` that is at least `2`. **If the
`V.size ≤ lam` clause is ever dropped from `IsBounded`, `MIPRE.Halting.accOf_iff` becomes
unprovable, and with it the acceptance table of the tabulation, obligation O2.**

`accOf_iff` is the one bridge still hostage to it. The two sampler runs of the tabulation are
budgeted from `MIPRE.GapCompression.sampler_time`, a bound at *every* index carrying no
hypothesis, so `MIPRE.Halting.dimOf_eq` and `MIPRE.Halting.margOf_eq` hold at `n = 0` and
`n = 1` as well and appeal neither to `IsBounded` nor to this lemma. The decider cannot be
budgeted that way — the one a string denotes is the string's own, wrapped, and only
`IsBounded n` bounds it — so `accOf_iff` runs at the budget `n ^ n` that boundedness supplies,
needs `2 ≤ n` to have it, and carries `MIPRE.Halting.acc_mem_iff`, `tab_match` and `tab_value`
with it. -/
theorem IsBounded.two_le {lam : ℕ} (h : V.IsBounded lam) : 2 ≤ lam :=
  le_trans (le_trans (Cost.Prog.two_le_esize V.decider.prog) (le_max_right _ _)) h.2

end Verifier

end MIPRE


