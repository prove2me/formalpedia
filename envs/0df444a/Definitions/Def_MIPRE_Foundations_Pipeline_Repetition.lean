-- Prove2me | Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
-- name    : MIPRE_Foundations_Pipeline_Repetition
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:22:12.187613+00:00
-- url     : https://prove2.me/theorems/05f3ce85-5aa2-4294-8b2e-250157542db5
-- title:
--   Parallel repetition of normal form verifiers as a hypothesis structure
-- statement:
--   Blueprint `thm:parallel-repetition` (paper `parallel_amplification.tex`, `thm:repetition`, direct form) as the data the theorem provides. For a level $\ell$, `Repetition ℓ` has: a real `c` with $0 < c$; polynomials `bound`, `ansBound` and a degree multiplier `deg`; `sampler : CL.Sampler ℓ → ℕ → ℕ → CL.Sampler ℓ`, the repeated sampler at $(\lambda,\tau)$, with polynomial-time program `samplerProg`; `compute`, the polynomial-time `ComputeParrepVerifier` on the input programs and $(\lambda,\tau,\beta)$; `output : Verifier ℓ → ℕ → ℕ → ℕ → Verifier ℓ` (sampler `sampler`, decider program `compute`); and three guarantees.
--
--   Parameters, with $|\cdot|$ the bit length `Nat.size`: `reps λ τ n` $= k(n) = 2^{\tau(|\lambda|+|n|)}$; `parseBound λ β n` $= B = 2^{\beta(|\lambda|+|n|)}$, the per-coordinate parse length; `arg λ τ β n R s` $= k(n) + B + R.S + R.d + R.D + R.B + s + \lambda + \tau + \beta + n + 10^{R.k}$; `ansArg λ τ β n` $= k(n) + B$; `soundBound c ε k B` is the bound displayed below.
--
--   `within`: `V.Within n R` gives `(output V λ τ β).Within n ⟨bound.eval (arg ..), bound.eval (arg ..), bound.eval (arg ..), deg * (R.k + 1), ansBound.eval (ansArg ..)⟩`, `arg` taken at `V.size`. `completeness`: `V.HasPerfectPCC n (parseBound λ β n)` gives `(output V λ τ β).HasPerfectPCC n (ansBound.eval (ansArg ..))`. `soundness`: for $0 < \varepsilon \le 1$, if $\mathrm{val}^*(\mathcal V_n) \le 1-\varepsilon$ at answer bound $B$, then at answer bound `ansBound.eval (ansArg ..)`
--
--   $$\mathrm{val}^*(\mathcal V^{\mathrm{rep}}_n) \le \exp\!\Big(-\frac{c\,\varepsilon^{13}\,k(n)}{B+1}\Big).$$
--
--   **Formalization Note** An instance is the theorem, unproved here (its inhabitation is the game-level `thm:direct-repetition-q`, `MIPRE.Repetition.quantumValue_repeat_le`, vendored, whose exponent $13$ this is); `GapCompression.ofPipeline` consumes one at $\ell = 7$. `reps`, `parseBound`, `arg`, `ansArg` are `abbrev`s on naturals; `soundBound` is `Real.exp`. Departures from the paper (module docstring): $k(n)$ is $2^{\tau(|\lambda|+|n|)}$, the power of two just above $(\lambda n)^\tau$; the parse length $B_{\mathcal D}(n)$ is an extra parameter $\beta$; `arg` adds the raw parameters (as $\tau = 0$ is allowed) and $10^{R.k}$, the input's cost on the dimension query of fixed size $9$; the degree is affine in the input's (universal-machine overhead). The input is read at answer bound $B$, the output at its own bound, beyond which its decider rejects.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/Repetition.lean; blueprint thm:parallel-repetition; paper parallel_amplification.tex, thm:repetition

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/Repetition.lean (definition bundle: declarations the uploaded statements rest on);
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
# Parallel repetition of normal form verifiers, as a hypothesis

Blueprint `thm:parallel-repetition` (paper `parallel_amplification.tex`, `thm:repetition`, in
its direct rather than anchored form; ledger nodes `1.4`, `1.4.3`, `1.4.3.1`), stated as the
data the theorem provides: the structure `Repetition ℓ`. Its inhabitation is the theorem: the
game-level direct repetition theorem `thm:direct-repetition-q`
(`MIPRE.Repetition.quantumValue_repeat_le`, vendored) packaged at the level of verifiers — a
sampler running `k(n)` independent copies of the input sampler, a decider parsing a
self-delimiting `k(n)`-tuple of answers and running the input decider on every coordinate.
Nothing here proves it. The composition `MIPRE.GapCompression.ofPipeline` consumes an
instance at `ℓ = 7`.

The reading of the paper's statement in the vocabulary of `MIPRE.Verifier`:

* `ComputeParrepVerifier` takes `(𝒱, ℓ, λ, τ)`; the number of repetitions is
  `k(n) = (λn)^τ`, read as `2^{τ(|λ| + |n|)}` with `|·|` the bit length — the power of two just
  above `(λn)^τ` (`Nat.size`), which a program of the ambient model writes down by a walk over
  the bits of `λ` and `n`, where the paper's expression would need multiplication. The repeated
  decider parses each coordinate of an answer against a length `2^{β(|λ| + |n|)}` — the paper's
  `B_𝒟(n)`, read from the timeout-counter form of the decider there, and a further parameter
  `β` here — so the procedure is a polynomial-time function of the input programs and
  `(λ, τ, β)` (`compute`); the repeated sampler depends only on the input sampler and `(λ, τ)`
  (`sampler`).
* The complexity clause bounds the output at index `n` by a polynomial in `k(n)`, the parse
  length, the input's budget at `n`, the input's description length, the raw parameters and the
  input's cost on the dimension query (`Repetition.arg`; the paper's
  `poly(k(n), TIME_𝒮(n))` and `poly(k(n), B_𝒟(n))`), at a degree affine in the input's — the
  repeated decider runs the input decider through the universal machine, whose overhead is
  polynomial — and the answers it accepts by a polynomial in `k(n)` and the parse length alone.
* Completeness: a value-`1` PCC strategy for `𝒱_n` gives one for `𝒱^rep_n`.
* Soundness: `val*(𝒱_n) ≤ 1 - ε` gives `val*(𝒱^rep_n) ≤ exp(-c ε^13 k(n) / (B + 1))`, with
  `B = 2^{β(|λ| + |n|)}` the parse length: `thm:direct-repetition-q` with `log(|𝒜||ℬ|) ≤ 2(B + 1)`
  for answer alphabets of strings of length at most `B`, the constant `c` absorbing the
  factor `3`. The exponent `13` is the vendored theorem's.

Answer alphabets: `𝒱_n` is read with answers of length at most the parse length, so that the
repeated game is exactly the direct repetition of `𝒱_n` at that alphabet, and `𝒱^rep_n` with
answers of length at most its own bound, beyond which its decider rejects.
-/

namespace MIPRE

open Cost

namespace Repetition

/-- The number of repetitions `k(n) = 2^{τ(|λ| + |n|)}`, at least `(λn + 1)^τ`. -/
abbrev reps (lam tau n : ℕ) : ℕ := 2 ^ (tau * (Nat.size lam + Nat.size n))

/-- The length against which each coordinate of an answer is parsed: `2^{β(|λ| + |n|)}`, at
least `(λn + 1)^β` and at most `(λn + 1)^{6β}` for `λ, n ≥ 1`. -/
abbrev parseBound (lam beta n : ℕ) : ℕ := 2 ^ (beta * (Nat.size lam + Nat.size n))

/-- The argument of the polynomial bounding the running times of the output at index `n`: the
repetition count, the parse length, the input's budget and description length, the raw
parameters `λ, τ, β, n` (the paper's `poly(k(n), TIME_𝒮(n))` dominates them when `τ ≥ 1`; here
they are added, since `τ = 0` is allowed), and `10^{R.k}`, the input's time on the dimension
query — an input of fixed size `9`, which the output asks on every input of its own,
including the empty one, and whose cost at degree `R.k` no polynomial in the other quantities
dominates. -/
abbrev arg (lam tau beta n : ℕ) (R : Budget) (s : ℕ) : ℕ :=
  reps lam tau n + parseBound lam beta n + R.S + R.d + R.D + R.B + s + lam + tau + beta + n +
    10 ^ R.k

/-- The argument of the polynomial bounding the answers of the output at index `n`. -/
abbrev ansArg (lam tau beta n : ℕ) : ℕ := reps lam tau n + parseBound lam beta n

/-- The soundness bound `exp(-c ε^13 k / (B + 1))`. -/
noncomputable def soundBound (c ε : ℝ) (k B : ℕ) : ℝ :=
  Real.exp (-(c * ε ^ 13 * (k : ℝ) / ((B : ℝ) + 1)))

end Repetition

/-- **Parallel repetition of normal form verifiers** (blueprint `thm:parallel-repetition`) for
`ℓ`-level inputs: the data of the procedure `ComputeParrepVerifier` together with the
guarantees of the theorem. An instance of this structure is the theorem. -/
structure Repetition (ℓ : ℕ) where
  /-- The constant of the soundness exponent. -/
  c : ℝ
  c_pos : 0 < c
  /-- The polynomial bounding the running times and dimension of the output. -/
  bound : Polynomial ℕ
  /-- The polynomial bounding the length of the answers the output accepts, in `k(n)` and the
  parse length. -/
  ansBound : Polynomial ℕ
  /-- The degree multiplier of the output's running times. -/
  deg : ℕ
  /-- The repeated sampler, a function of the input sampler and `(λ, τ)`. -/
  sampler : CL.Sampler ℓ → ℕ → ℕ → CL.Sampler ℓ
  /-- Its program, computable from the input sampler's program and `(λ, τ)` in polynomial
  time. -/
  samplerProg : PolyTimeFun (Prog × ℕ × ℕ) Prog
  samplerProg_eq : ∀ (S : CL.Sampler ℓ) (lam tau : ℕ),
    samplerProg (S.prog, lam, tau) = (sampler S lam tau).prog
  /-- `ComputeParrepVerifier`: the repeated decider, from the input programs and `(λ, τ, β)`,
  in polynomial time. -/
  compute : PolyTimeFun ((Prog × Prog) × ℕ × ℕ × ℕ) Prog
  /-- The output on a normal form input, at parameters `(λ, τ, β)`. -/
  output : Verifier ℓ → ℕ → ℕ → ℕ → Verifier ℓ
  output_sampler : ∀ (V : Verifier ℓ) (lam tau beta : ℕ),
    (output V lam tau beta).sampler = sampler V.sampler lam tau
  output_decider : ∀ (V : Verifier ℓ) (lam tau beta : ℕ),
    (output V lam tau beta).decider.prog =
      compute ((V.sampler.prog, V.decider.prog), lam, tau, beta)
  /-- The complexity clause: within a polynomial of `k(n)`, the parse length, the input's
  budget and the input's description length, at degree `deg (k + 1)`, and answers within a
  polynomial of `k(n)` and the parse length. -/
  within : ∀ (V : Verifier ℓ) (lam tau beta n : ℕ) (R : Budget), V.Within n R →
    (output V lam tau beta).Within n
      ⟨bound.eval (Repetition.arg lam tau beta n R V.size),
        bound.eval (Repetition.arg lam tau beta n R V.size),
        bound.eval (Repetition.arg lam tau beta n R V.size), deg * (R.k + 1),
        ansBound.eval (Repetition.ansArg lam tau beta n)⟩
  /-- **Completeness.** -/
  completeness : ∀ (V : Verifier ℓ) (lam tau beta n : ℕ),
    V.HasPerfectPCC n (Repetition.parseBound lam beta n) →
    (output V lam tau beta).HasPerfectPCC n (ansBound.eval (Repetition.ansArg lam tau beta n))
  /-- **Soundness.** `val*(𝒱_n) ≤ 1 - ε` gives `val*(𝒱^rep_n) ≤ exp(-c ε^13 k(n) / (B + 1))`. -/
  soundness : ∀ (V : Verifier ℓ) (lam tau beta n : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    V.valStar n (Repetition.parseBound lam beta n) ≤ 1 - ε →
    (output V lam tau beta).valStar n (ansBound.eval (Repetition.ansArg lam tau beta n)) ≤
      Repetition.soundBound c ε (Repetition.reps lam tau n) (Repetition.parseBound lam beta n)

end MIPRE


