-- Prove2me | Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
-- name    : MIPRE_Foundations_Pipeline_Introspection
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:21:53.896244+00:00
-- url     : https://prove2.me/theorems/2c01b115-4325-4ed9-bfae-409c83f7f37f
-- title:
--   Introspection as a hypothesis structure: the data and guarantees of ComputeIntroVerifier
-- statement:
--   Blueprint `thm:introspection` (paper `introspection.tex`, `thm:introspection`) as the data the theorem provides. For a level $\ell$ of the input, `Introspection ℓ` has: reals `a`, `b` with $1 \le a$, $0 < b \le 1$; the complexity constant `C`; `sampler : ℕ → CL.Sampler 5`, the introspective sampler depending only on $\lambda$, with its program `samplerProg : PolyTimeFun ℕ Prog` (`samplerProg_eq`); `compute : PolyTimeFun ((Prog × Prog) × ℕ) Prog`, the procedure `ComputeIntroVerifier` returning the introspective decider's program; `output : Prog × Prog → ℕ → Verifier 5`, whose sampler is `sampler λ` and whose decider's program is `compute (V, λ)`; and four guarantees.
--
--   Parameters: `ansBound C λ n` $= 2^{(\lambda n+1)^C}$; `budget C λ n` $= \langle (\lambda n+1)^C, (\lambda n+1)^C, 2^{(\lambda n+1)^C}, C, 2^{(\lambda n+1)^C}\rangle$; `delta a b λ n ε` $= a((\lambda n)^a\varepsilon^b + (\lambda n)^{-b})$.
--
--   `within`: for every `V : Prog × Prog` and all $\lambda, n$, `(output V λ).Within n (budget C λ n)`. `decider_size`: `(output V λ).decider.size ≤ C * (λ + 1) ^ C` for every `V`, $\lambda$. `completeness`: for `V : Verifier ℓ` with `V.IsBounded λ`, `V.HasPerfectPCC (2 ^ n) ((2 ^ n) ^ λ)` gives `(output (V.sampler.prog, V.decider.prog) λ).HasPerfectPCC n (ansBound C λ n)`. `soundness`: for `V.IsBounded λ`, $1 \le n$, $0 < \varepsilon$ and $1-\varepsilon < \mathrm{val}^*(\mathcal V^{\mathrm{intro}}_n)$ at answer bound `ansBound C λ n`,
--
--   $$1 - a\big((\lambda n)^{a}\varepsilon^{b} + (\lambda n)^{-b}\big) \le \mathrm{val}^*(\mathcal V_{2^n})\quad\text{at answer bound } (2^n)^{\lambda}.$$
--
--   An instance is the theorem; `GapCompression.ofPipeline` consumes one at $\ell = 7$.
--
--   **Formalization Note** Nothing here proves introspection; its inhabitation is the rigidity argument through the Pauli basis test `thm:qld`. `ansBound` is an `abbrev`; `delta` uses `Real.rpow`. The complexity clauses hold for every input; the exponent $(\lambda n+1)^C$ is the module's explicit adaptation of the paper's absolute bound $2^{C\lambda n}$ to the ambient input-size degree, and the budget's `B` field makes the output reject answers longer than its time bound. Soundness requires $1 \le n$ because at $n = 0$ the loss vanishes; the paper's $a > 0$ is normalized to $a \ge 1$, which only weakens the clause. The input is read with answers of length at most $(2^n)^\lambda$, the output with answers of length at most `ansBound`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/Introspection.lean; blueprint def:introspection-contract; paper introspection.tex, thm:introspection

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/Introspection.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget

/-!
# Introspection, as a hypothesis

Blueprint `thm:introspection` (paper `introspection.tex`, `thm:introspection`; ledger nodes
`1.2`, `1.2.3.8`), stated as the data the theorem provides: the structure `Introspection ℓ`.
Its inhabitation is the theorem — the rigidity argument of the paper's Section 8 through the
Pauli basis test `thm:qld` — and nothing here proves it. The composition
`MIPRE.GapCompression.ofPipeline` consumes an instance at `ℓ = 7`.

The reading of the paper's statement in the vocabulary of `MIPRE.Verifier`:

* `ComputeIntroVerifier` takes `(𝒱, λ, ℓ)`; with `ℓ` a parameter of the structure, the
  procedure is a polynomial-time function `compute` of `((S̄, D̄), λ)` returning the program of
  the introspective decider, and the introspective sampler `𝒮^intro_λ` depends only on `λ`
  (paper `lem:intro-sampler-complexity`), with its program computable from `λ`
  (`samplerProg`). On every input, well-formed or not, the output is a `5`-level normal form
  verifier (`output`).
* The ambient complexity clauses hold for every input and every index:
  `TIME_𝒮(n) ≤ (λn + 1)^C`, `TIME_𝒟(n) ≤ 2^{(λn + 1)^C}` and
  `|𝒟^intro| ≤ C(λ+1)^C`. The polynomial exponent is an explicit adaptation of the
  paper's absolute-time bound `2^{Cλn}`: `IsBounded λ` permits input-size degree `λ`,
  which introduces a quadratic exponent in `λ` on legal answers of length `(2^n)^λ`.
  The running times carry the fixed degree `C` in the size of the output verifier's
  input, and the decider rejects every answer longer than its bound (`Budget.B`).
  Answer reduction consumes the same polynomial-exponent budget, and the proved
  compression composition still has polynomial output bounds. The introspective decider keeps `𝒟` within its own
  description only up to `λ` bits (paper `lem:intro-decider-complexity`), which is why the
  size bound does not depend on the input.
* For a `λ`-bounded `ℓ`-level input: a value-`1` PCC strategy for `𝒱_{2^n}` gives
  one for `𝒱^intro_n` (completeness), and `val*(𝒱^intro_n) > 1 - ε` gives
  `val*(𝒱_{2^n}) ≥ 1 - δ(ε, n)` with `δ(ε, n) = a((λn)^a ε^b + (λn)^{-b})` (soundness), the
  constants `a, b` depending on `ℓ` only. Soundness requires `1 ≤ n`, as in the construction's
  indexing convention: the original input is bounded only at `2 ≤ 2^n`. At zero the displayed
  error would vanish and assert an unintended exact conclusion. The paper has `a > 0`; `a ≥ 1` is assumed here,
  which only weakens the clause and is what the proof of `thm:compression` uses.

Answer alphabets follow `MIPRE.GapCompression`: `𝒱_{2^n}` is read with answers of length at
most `(2^n)^λ`, and `𝒱^intro_n` with answers of length at most its time bound, beyond which
its decider rejects.
-/

namespace MIPRE

open Cost

namespace Introspection

/-- The answer bound of the introspective verifier at level `λ` and index `n`: its decider's
running-time coefficient `2^{(λn + 1)^C}`. -/
abbrev ansBound (C lam n : ℕ) : ℕ := 2 ^ ((lam * n + 1) ^ C)

/-- The budget of the introspective verifier at level `λ` and index `n`: sampler within
`(λn + 1)^C`, questions of dimension at most `(λn + 1)^C`, decider within `2^{(λn + 1)^C}`, both
at degree `C`, and no answer longer than `2^{(λn + 1)^C}` accepted. -/
def budget (C lam n : ℕ) : Budget :=
  ⟨(lam * n + 1) ^ C, (lam * n + 1) ^ C, ansBound C lam n, C, ansBound C lam n⟩

/-- The soundness loss `δ(ε, n) = a((λn)^a ε^b + (λn)^{-b})`. -/
noncomputable def delta (a b : ℝ) (lam n : ℕ) (ε : ℝ) : ℝ :=
  a * (((lam : ℝ) * n) ^ a * ε ^ b + ((lam : ℝ) * n) ^ (-b))

end Introspection

/-- **Introspection** (blueprint `thm:introspection`) for `ℓ`-level inputs: the data of the
procedure `ComputeIntroVerifier` together with the guarantees of the theorem. An instance of
this structure is the theorem. -/
structure Introspection (ℓ : ℕ) where
  /-- The constant `a` of the soundness loss, normalized to `a ≥ 1`. -/
  a : ℝ
  /-- The exponent `b` of the soundness loss, `0 < b ≤ 1`. -/
  b : ℝ
  one_le_a : 1 ≤ a
  b_pos : 0 < b
  b_le_one : b ≤ 1
  /-- The complexity constant `C_intro`. -/
  C : ℕ
  /-- The introspective sampler `𝒮^intro_λ`, depending only on `λ`. -/
  sampler : ℕ → CL.Sampler 5
  /-- Its program, computable from `λ` in polynomial time. -/
  samplerProg : PolyTimeFun ℕ Prog
  samplerProg_eq : ∀ lam : ℕ, samplerProg lam = (sampler lam).prog
  /-- `ComputeIntroVerifier`: from the programs of a verifier and `λ`, the program of the
  introspective decider, in polynomial time. -/
  compute : PolyTimeFun ((Prog × Prog) × ℕ) Prog
  /-- The output on any input is a `5`-level normal form verifier, with the introspective
  sampler and the introspective decider. -/
  output : Prog × Prog → ℕ → Verifier 5
  output_sampler : ∀ (V : Prog × Prog) (lam : ℕ), (output V lam).sampler = sampler lam
  output_decider : ∀ (V : Prog × Prog) (lam : ℕ), (output V lam).decider.prog = compute (V, lam)
  /-- The complexity clauses, for every input and index. -/
  within : ∀ (V : Prog × Prog) (lam n : ℕ), (output V lam).Within n (Introspection.budget C lam n)
  /-- `|𝒟^intro| ≤ C λ^C`, for every input. -/
  decider_size : ∀ (V : Prog × Prog) (lam : ℕ), (output V lam).decider.size ≤ C * (lam + 1) ^ C
  /-- **Completeness.** For a `λ`-bounded input: a value-`1` PCC strategy for `𝒱_{2^n}` gives
  one for `𝒱^intro_n`. -/
  completeness : ∀ (V : Verifier ℓ) (lam n : ℕ), V.IsBounded lam →
    V.HasPerfectPCC (2 ^ n) ((2 ^ n) ^ lam) →
    (output (V.sampler.prog, V.decider.prog) lam).HasPerfectPCC n (Introspection.ansBound C lam n)
  /-- **Soundness.** For a `λ`-bounded input and `n ≥ 1`: `val*(𝒱^intro_n) > 1 - ε` gives
  `val*(𝒱_{2^n}) ≥ 1 - δ(ε, n)`. -/
  soundness : ∀ (V : Verifier ℓ) (lam n : ℕ) (ε : ℝ), V.IsBounded lam → 1 ≤ n → 0 < ε →
    1 - ε < (output (V.sampler.prog, V.decider.prog) lam).valStar n (Introspection.ansBound C lam n) →
    1 - Introspection.delta a b lam n ε ≤ V.valStar (2 ^ n) ((2 ^ n) ^ lam)

end MIPRE


