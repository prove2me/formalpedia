-- Prove2me | Definitions.Def_MIPRE_Foundations_GapCompression
-- name    : MIPRE_Foundations_GapCompression
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:29:19.063854+00:00
-- url     : https://prove2.me/theorems/20081111-93cf-4210-9826-5995789bfc82
-- title:
--   Gap-preserving compression as a structure, the doubled game of a verifier and perfect PCC strategies
-- statement:
--   This bundle holds the module stating blueprint `thm:compression` as data: the structure `GapCompression`, whose inhabitation is the theorem, with two definitions on a verifier $\mathcal{V}$. `Verifier.doubledGame n T` is the game $\mathcal{V}_n$ with answers of length at most $T$ on the doubled question set (`Game.doubled`), a `SynchronousGame` for every verifier. `Verifier.HasPerfectPCC n T` says that this doubled game has a synchronous strategy $S$ with `S.IsPCC` (blueprint `def:pcc`) and `S.value = 1`. A `GapCompression` consists of: a constant $C_0$; a compressed sampler `sampler λ : CL.Sampler 7` depending only on $\lambda$, with its program given by a `PolyTimeFun ℕ Prog`; `compress : PolyTimeFun ((Prog × Prog) × ℕ) Prog`; an `output : Prog × Prog → ℕ → Verifier 7` whose sampler is `sampler λ` and whose decider's program is `compress (V, λ)`; a polynomial `bound` and a degree `deg` such that at every index $n$ the compressed sampler and decider satisfy `TimeBoundAt n (bound(n + λ)) deg`, the sampler's dimension is at most $\mathrm{bound}(n + \lambda)$, and the compressed decider accepts no answer longer than $\mathrm{bound}(n + \lambda)$; and two guarantees for every `V : Verifier 7`, $\lambda$, $n$ with `V.IsBounded λ` and $C_0 \le n$, writing $N = 2^n$ and $V' = \mathrm{output}\,(V.\mathrm{sampler.prog}, V.\mathrm{decider.prog})\,\lambda$:
--
--   $$V.\mathrm{HasPerfectPCC}\,N\,(N^\lambda) \Rightarrow V'.\mathrm{HasPerfectPCC}\,n\,(\mathrm{bound}(n+\lambda)), \qquad V.\mathrm{valStar}\,N\,(N^\lambda) \le \tfrac12 \Rightarrow V'.\mathrm{valStar}\,n\,(\mathrm{bound}(n+\lambda)) \le \tfrac12.$$
--
--   No theorem is embedded; the halting reduction consumes an instance through the compressibility criterion.
--
--   **Formalization Note** `HasPerfectPCC` is read on the doubled game rather than on $\mathcal{V}_n$ (issue #77): the paper's completeness clause does not make the decider synchronous, while the doubled game is synchronous for every verifier. The level count is $7$ (the blueprint's direct repetition; the paper's is $9$). `bound : Polynomial ℕ` is evaluated at `n + lam`; `completeness` and `soundness` are quantified as `∀ (V : Verifier 7) (lam n : ℕ), V.IsBounded lam → C₀ ≤ n → …`, with $\mathcal{V}_N$ taken with answers of length at most `(2 ^ n) ^ lam`. `doubledGame n T := (V.game n T).doubled`; `HasPerfectPCC n T := ∃ S : SyncStrategy (V.doubledGame n T), S.IsPCC ∧ S.value = 1`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GapCompression.lean; blueprint thm:compression; paper recursive.tex, thm:compression (ledger nodes 1.5, 1.5.7, 1.5.1)

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GapCompression.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Gap-preserving compression, as a hypothesis

Blueprint `thm:compression` (paper `recursive.tex`, `thm:compression`; ledger nodes `1.5`,
`1.5.7`) and `lem:compress-sampler-indep` (node `1.5.1`), stated as the data a compression
procedure provides: the structure `GapCompression`. Its inhabitation is the theorem, to be
proved by the chain introspection → oracularization → answer reduction → repetition of
chapter 6 of the blueprint; nothing here proves it. The halting reduction (`thm:halting`)
consumes an instance through the per-level compressibility criterion
(`MIPRE.Cost.compressibility_criterion_levels`, blueprint `rem:compression-abstract`).

The reading of the paper's statement in the vocabulary of `MIPRE.Verifier`:

* `Compress` is a polynomial-time function of the pair of programs `(S̄, D̄)` of the input
  verifier and of `λ`, returning the program of the compressed decider. The compressed sampler
  `S^compr_λ` depends only on `λ`, is a valid 7-level sampler for every `λ`, and its program is
  computable from `λ` in time polynomial in the length of `λ` (the paper's `polylog(λ)`).
* On every input, well-formed or not, the output is a normal form verifier: `output` packages
  the compressed sampler and decider as a `Verifier 7`. Its sampler and decider run within
  `bound (n + λ)` at index `n`, at the degree `deg` in the size of the input that
  `TimeBoundAt` carries, the paper's `poly(n, λ)`; the compressed sampler has dimension at most `bound (n + λ)`, the
  paper's `s(n) ≤ TIME_S(n)`; and the compressed decider accepts no answer longer than
  `bound (n + λ)` (`output_rejects_long`), the property of the paper's repeated decider that
  its amended proof of `lem:dhalt-values` relies on — it accepts only after fully parsing the
  answers, so an answer longer than its time bound forces a timeout. In the ambient model,
  where the running time scales with the input, this is a demand on the construction (an
  explicit length check), recorded as a field.
* For a `λ`-bounded 7-level input `V`, at every `n ≥ C₀` and with `N = 2 ^ n`: a value-`1`
  PCC strategy for `V_N` yields one for `V^compr_n` (completeness), and `val*(V_N) ≤ 1/2`
  implies `val*(V^compr_n) ≤ 1/2` (soundness, in value form).

Answer alphabets: `V_N` is taken with answers of length at most `N ^ λ`, the bound that
`λ`-boundedness puts on the running time of its decider, and `V^compr_n` with answers of
length at most `bound (n + λ)`, the bound on the running time of the compressed decider,
beyond which it rejects (`output_rejects_long`), so that by `Verifier.valStar_eq_of_rejects`
its value is the same with any larger alphabet; the paper's alphabets are cut at the exact
running times, which are not functions of the verifier in this formalization (see
`Verifier.game`). The level count is `7`, the blueprint's (direct repetition); the paper's is
`9`, with anchoring.
-/

namespace MIPRE

open Cost

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- **`𝒱_n` on the doubled question set.** Alice is asked `(false, x)`, Bob `(true, y)`; every
other pair carries no weight and is rejected (`MIPRE.Game.doubled`). A synchronous game for
*every* verifier, with no hypothesis on the decider, because the distribution puts no weight on
the diagonal. -/
noncomputable def doubledGame (n T : ℕ) : SynchronousGame (Bool × V.Questions n) (Answers T) :=
  (V.game n T).doubled

/-- `𝒱_n`, with answers of length at most `T`, has a value-`1` PCC strategy: some PCC
synchronous strategy (blueprint `def:pcc`) for the game on the doubled question set wins it
with certainty — a single family of projective measurements, played by both players, commuting
on the support of the question distribution.

Read on the doubled game rather than on `𝒱_n` itself (issue #77): a synchronous game has to
reject unequal answers to equal questions, which is a property of the *decider*
(`IsSynchronousAt`) that the paper's completeness clause does not supply and the paper does not
state — there, synchronous is a property of a strategy — while the doubled game is synchronous
for every verifier. What the paper's clause supplies, identical measurement operators for the
two players commuting on the support, is exactly a PCC strategy of the doubled game. -/
def HasPerfectPCC (n T : ℕ) : Prop :=
  ∃ S : SyncStrategy (V.doubledGame n T), S.IsPCC ∧ S.value = 1

end Verifier

/-- **Gap-preserving compression** (blueprint `thm:compression`): the data of a compression
procedure together with the guarantees of the theorem. An instance of this structure is the
theorem; the pipeline of chapter 6 is its proof. -/
structure GapCompression where
  /-- The universal constant `C₀` above which the guarantees hold. -/
  C₀ : ℕ
  /-- The compressed sampler `S^compr_λ`, depending only on `λ`
  (blueprint `lem:compress-sampler-indep`). -/
  sampler : ℕ → CL.Sampler 7
  /-- Its program is computable from `λ`, in time polynomial in the length of `λ`
  (the paper's `ComputeSampler`). -/
  samplerProg : PolyTimeFun ℕ Prog
  samplerProg_eq : ∀ lam : ℕ, samplerProg lam = (sampler lam).prog
  /-- `Compress`: from the programs of a verifier and `λ`, the program of the compressed
  decider, in polynomial time. -/
  compress : PolyTimeFun ((Prog × Prog) × ℕ) Prog
  /-- The output on any input is a normal form verifier, with the compressed sampler and the
  compressed decider. -/
  output : Prog × Prog → ℕ → Verifier 7
  output_sampler : ∀ (V : Prog × Prog) (lam : ℕ), (output V lam).sampler = sampler lam
  output_decider : ∀ (V : Prog × Prog) (lam : ℕ), (output V lam).decider.prog = compress (V, lam)
  /-- The polynomial `poly(n, λ)` bounding the running times of the output at index `n`, the
  dimension of the compressed sampler, and the length of the answers the compressed decider
  can accept. -/
  bound : Polynomial ℕ
  /-- The degree, in the size of the input, of the running times of the output: a universal
  constant of the construction (see the module docstring of `MIPRE.Foundations.Verifier`). -/
  deg : ℕ
  sampler_time : ∀ lam n : ℕ, (sampler lam).TimeBoundAt n (bound.eval (n + lam)) deg
  /-- `s(n) ≤ poly(n, λ)` for the compressed sampler (in the paper, from its running time). -/
  sampler_dim : ∀ lam n : ℕ, (sampler lam).dim n ≤ bound.eval (n + lam)
  decider_time : ∀ (V : Prog × Prog) (lam n : ℕ),
    (output V lam).decider.TimeBoundAt n (bound.eval (n + lam)) deg
  /-- The compressed decider accepts no answer longer than its time bound: the paper's
  repeated decider accepts only after fully parsing the answers. -/
  output_rejects_long : ∀ (V : Prog × Prog) (lam n : ℕ) (x y a b : BitStr),
    bound.eval (n + lam) < a.length ∨ bound.eval (n + lam) < b.length →
      ¬ (output V lam).decider.Accepts n x y a b
  /-- **Completeness.** For a `λ`-bounded input and `n ≥ C₀`: a value-`1` PCC strategy for
  `V_{2^n}` gives one for `V^compr_n`. -/
  completeness : ∀ (V : Verifier 7) (lam n : ℕ), V.IsBounded lam → C₀ ≤ n →
    V.HasPerfectPCC (2 ^ n) ((2 ^ n) ^ lam) →
    (output (V.sampler.prog, V.decider.prog) lam).HasPerfectPCC n (bound.eval (n + lam))
  /-- **Soundness**, value form. For a `λ`-bounded input and `n ≥ C₀`: `val*(V_{2^n}) ≤ 1/2`
  implies `val*(V^compr_n) ≤ 1/2`. -/
  soundness : ∀ (V : Verifier 7) (lam n : ℕ), V.IsBounded lam → C₀ ≤ n →
    V.valStar (2 ^ n) ((2 ^ n) ^ lam) ≤ 1 / 2 →
    (output (V.sampler.prog, V.decider.prog) lam).valStar n (bound.eval (n + lam)) ≤ 1 / 2

end MIPRE


