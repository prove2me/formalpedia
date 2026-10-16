-- Prove2me | Definitions.Def_MIPRE_Foundations_Pipeline_Compress
-- name    : MIPRE_Foundations_Pipeline_Compress
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:24:13.739469+00:00
-- url     : https://prove2.me/theorems/3ddb4a01-5cd5-4591-97b5-6807a2b66834
-- title:
--   The compression theorem from its three stages: the parameters of Compress and GapCompression.ofPipeline
-- statement:
--   Blueprint `thm:compression` (paper `recursive.tex`) and `lem:compress-sampler-indep`. From $I$ : `Introspection 7`, $A$ : `AnswerReduction 5` and $R$ : `Repetition 7`, `Compress` is introspection, then answer reduction at $(\lambda,\mu,\sigma(\lambda))$, then repetition at $(\lambda,\tau,\beta)$:
--
--   $$\mathtt{output}(V,\lambda) = R.\mathrm{output}\big(A.\mathrm{output}(I.\mathrm{output}(V,\lambda),\lambda,\mu,\sigma(\lambda)),\lambda,\tau,\beta\big) : \mathrm{Verifier}\ 7.$$
--
--   Size parameter: `twoPowFun` ($n \mapsto 2^{2\,\mathrm{size}(n)}$, polynomial-time) and `sigmaFun C`, its $C$-fold iterate on $2n+1$; `s₁`, `cS` bound $I$'s sampler-program size; `Csig` $= I.C + \mathtt{cS} + \deg$; `sigma λ` $=$ `sigmaFun Csig λ`; `K` has $\sigma(z) \le z^K$ for $z \ge 2$. Margins: `mu`, `N₁` from `exists_mu` (lower bound $I.C + 1$); `beta` with $A.\mathrm{bound}(z^\mu + \sigma(z) + 2z)^{\mu+1} \le z^\beta$ for $z \ge 2$; `P`, `N₂` from `exists_eps2_lower`; `tau` from `exists_tau` at $(P, 6\beta)$; `C₁` $= \lceil(4 I.a)^{1/I.b}\rceil$; `C₀` $= \max(2, C_1, N_1, N_2, A.C, \tau)$. Data: `arOutput`, `arSampler` ($A$ at these parameters); `sampler λ`, the compressed sampler, depending only on $\lambda$, and its polynomial-time program `samplerProg`; `compress`, the polynomial-time map from the input programs and $\lambda$ to the compressed decider's program. Accounting: `pArg`, `wSize` bound the encoded parameters and the answer-reduced verifier's size; `arBound`, `arDegree` are $A$'s output bound and degree; `timeB`, `ansB` are $R$'s time and answer bounds; `G z` $=$ `timeB z z + ansB z z`; `bound` is the polynomial chosen above `G`. `GapCompression.ofPipeline I A R` has these `C₀`, `sampler`, `samplerProg`, `compress`, `output`, `bound` and `deg := R.deg * (arDegree + 1)`.
--
--   The embedded lemmas supply the parameter arithmetic (`sigmaFun`'s growth and polynomial boundedness, the size bounds, the specifications of $\mu,\beta,P,\tau,C_0$), the budget chain up to `bound.eval (n + λ)`, the output's programs, and the value chain `output_hasPerfectPCC`, `output_valStar_le` for $\lambda$-bounded $V$, $n \ge C_0$.
--
--   **Formalization Note** $\sigma$ is `sigmaFun Csig λ`, not the paper's $\lceil C\lambda^C\rceil$, for which the toolkit has no polynomial-time arithmetic; any dominating polynomial serves. `K`, `mu`, `beta`, `P`, `tau`, the thresholds and `bound` are chosen witnesses of existence lemmas, hence noncomputable. Oracularization is not a stage.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/Compress.lean; blueprint lem:compress-sampler-indep; blueprint thm:compression; paper recursive.tex, proof of thm:compression

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/Compress.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Definitions.Def_MIPRE_Foundations_Halting_CompressorProgram
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_AnswerReduction
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Pipeline_Margin

/-!
# The compression theorem from its three stages

Blueprint `thm:compression`, its proof (paper `recursive.tex`, Section "Proof of Theorem
compression"; ledger nodes `1.5`, `1.5.7`, `1.5.8`): `Compress` is introspection at `ℓ = 7`,
then answer reduction at `(λ, μ, σ(λ))`, then parallel repetition at `(λ, τ, β)`, and its
guarantees are those of the three stages chained through the margins of
`MIPRE.Foundations.Pipeline.Margin`. `GapCompression.ofPipeline` is that composition: from an
`Introspection 7`, an `AnswerReduction 5` and a `Repetition 7` it builds a `GapCompression`.
Oracularization is not a stage of `Compress` (it is the first step of the proof of answer
reduction) and is not consumed here.

The parameters, all determined by the three structures:

* `σ(λ)`: the paper's `⌈C λ^C⌉`, any polynomial in `λ` computable in polynomial time that
  dominates the size `C(λ + 1)^C` of the introspective decider and the size `s₁(λ)` of the
  introspective sampler — the second because answer reduction runs the input sampler through
  the universal machine, whose overhead grows with the program simulated, so its complexity
  clause asks `|𝒮|, |𝒟| ≤ σ`. It is `sigmaFun C_σ λ`, the
  `C_σ`-fold iterate of `n ↦ 2^{2·size n}` on `2λ + 1`, which is `2^{C(size λ + 2)}` at least
  and is computed by iterating `lamProg`; there is no polynomial-time arithmetic in the
  toolkit to compute the paper's expression directly, and any dominating polynomial serves.
* `μ`: the margin claim `exists_mu`, at least `C + 1`: at least `C` so that the introspective
  verifier is within answer reduction's input budget, and positive, as answer reduction's
  completeness asks.
* `β`: an exponent with `poly((λn + 1)^μ + σ(λ) + λ + n)^(μ + 1) ≤ (λn + 1)^β`, the parse length
  handed to repetition, dominating the ambient answer bound of the answer-reduced verifier.
* `τ`: the repetition exponent `exists_tau`, from the lower bound `ε₂ ≥ x^{-P}` of
  `exists_eps2_lower`, against the parse length `2^{β(|λ| + |n|)} ≤ (λn + 1)^{6β}`.
* `C₀`: the largest of the thresholds — `2`, the introspection margin's, the margin claim's,
  the lower bound's, answer reduction's own `C_ar`, and `τ`.

The complexity accounting is `PolyBounded` arithmetic: every bound of the repeated verifier at
`(λ, n)` is a monotone polynomial expression in `λ`, `n`, `σ(λ)` and the sizes of the programs
along the chain, hence at most a polynomial in `n + λ` (`bound`). The value chain is the one
of `rem:compression-chain`: each soundness clause contrapositively, landing inside the margin
the previous stage left.
-/

namespace MIPRE.Pipeline

open Cost Polynomial

/-! ## The size parameter `σ` -/

/-- `n ↦ 2^{2·size n}` as a polynomial-time function (`lamProg`). -/
noncomputable def twoPowFun : PolyTimeFun ℕ ℕ where
  toFun n := 2 ^ (2 * Nat.size n)
  code := Prog.lamProg
  closed := Prog.lamProg_wellScoped
  timeBound := 50 * (X + C 5) ^ 2
  computes n := by
    obtain ⟨t, ht, h⟩ := Prog.lamProg_runs n
    exact ⟨t, by simpa using ht, h⟩

/-- `sigmaFun C`: the `C`-fold iterate of `n ↦ 2^{2·size n}` on `2n + 1`, a polynomial-time
function of `n` bounded below by `2^{C(size n + 2)}` and above by a polynomial in `n`. -/
noncomputable def sigmaFun : ℕ → PolyTimeFun ℕ ℕ
  | 0 => PolyTimeFun.next
  | C + 1 => twoPowFun.comp (sigmaFun C)

theorem sigmaFun_zero (n : ℕ) : sigmaFun 0 n = 2 * n + 1 := rfl

theorem sigmaFun_succ (C n : ℕ) : sigmaFun (C + 1) n = 2 ^ (2 * Nat.size (sigmaFun C n)) := rfl

theorem size_sigmaFun (C n : ℕ) :
    C * (Nat.size n + 2) + Nat.size n + 1 ≤ Nat.size (sigmaFun C n) := by
  induction C with
  | zero => rw [sigmaFun_zero, size_two_mul_add_one]; omega
  | succ C ih =>
    rw [sigmaFun_succ, Nat.size_pow]
    nlinarith [ih, Nat.zero_le (C * (Nat.size n + 2))]

theorem one_le_sigmaFun (C n : ℕ) : 1 ≤ sigmaFun C n :=
  Nat.size_pos.1 (by have := size_sigmaFun C n; omega)

/-- `C (n + 1)^C ≤ sigmaFun C n`: the size of the introspective decider is dominated. -/
theorem le_sigmaFun (C n : ℕ) : C * (n + 1) ^ C ≤ sigmaFun C n := by
  have h1 : C * (n + 1) ^ C ≤ 2 ^ (C * (Nat.size n + 1)) := by
    calc C * (n + 1) ^ C ≤ 2 ^ C * (2 ^ Nat.size n) ^ C :=
          Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left (Nat.lt_size_self n) C)
      _ = 2 ^ (C * (Nat.size n + 1)) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have h2 : 2 ^ (C * (Nat.size n + 1)) ≤ sigmaFun C n := by
    rw [← Nat.lt_size]; have := size_sigmaFun C n; nlinarith
  exact h1.trans h2

theorem sigmaFun_mono (C : ℕ) {m n : ℕ} (h : m ≤ n) : sigmaFun C m ≤ sigmaFun C n := by
  induction C with
  | zero => simp only [sigmaFun_zero]; omega
  | succ C ih =>
    rw [sigmaFun_succ, sigmaFun_succ]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.size_le_size ih))

theorem polyBounded_sigmaFun (C : ℕ) : PolyBounded (sigmaFun C) := by
  induction C with
  | zero => exact PolyBounded.two_mul_add_one.mono fun n => (sigmaFun_zero n).le
  | succ C ih =>
    refine (((ih.const_mul 2).add_const 1).pow 2).mono fun n => ?_
    rw [sigmaFun_succ, pow_mul']
    exact Nat.pow_le_pow_left (two_pow_size_le _) 2

/-! ## The parameters -/

variable (I : Introspection 7) (A : AnswerReduction 5) (R : Repetition 7)

/-- A bound on the size of the introspective sampler's program. -/
noncomputable def s₁ (lam : ℕ) : ℕ := I.samplerProg.timeBound.eval (4 * Nat.size lam + 1)

theorem sampler_size_le_s₁ (lam : ℕ) : (I.sampler lam).size ≤ s₁ I lam := by
  show esize (I.sampler lam).prog ≤ _
  rw [← I.samplerProg_eq]
  exact (I.samplerProg.esize_apply_le lam).trans (polynomial_eval_mono _ (esize_nat_le lam))

/-- The coefficient of the monomial bound on `s₁`. -/
noncomputable def cS : ℕ :=
  (∑ i ∈ Finset.range (I.samplerProg.timeBound.natDegree + 1), I.samplerProg.timeBound.coeff i) *
    4 ^ I.samplerProg.timeBound.natDegree

theorem s₁_le (lam : ℕ) : s₁ I lam ≤ cS I * (lam + 1) ^ I.samplerProg.timeBound.natDegree := by
  have hs : 4 * Nat.size lam + 1 ≤ 4 * (lam + 1) := by
    have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := lam)); omega
  refine (polynomial_eval_mono _ hs).trans ((polynomial_eval_le_sum_coeff_mul_pow _
    (by omega)).trans (le_of_eq ?_))
  rw [cS, mul_pow, Nat.mul_assoc]

/-- The exponent of `σ`: large enough that `C_σ (λ + 1)^{C_σ}` dominates both the introspective
decider's size `C(λ + 1)^C` and the introspective sampler's size `s₁`. -/
noncomputable def Csig : ℕ := I.C + cS I + I.samplerProg.timeBound.natDegree

theorem mul_pow_le_Csig {c d : ℕ} (hc : c ≤ Csig I) (hd : d ≤ Csig I) (lam : ℕ) :
    c * (lam + 1) ^ d ≤ Csig I * (lam + 1) ^ Csig I :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd)

/-- `σ(λ) = sigmaFun C_σ λ`. -/
noncomputable def sigma (lam : ℕ) : ℕ := sigmaFun (Csig I) lam

theorem decider_size_le_sigma (V : Prog × Prog) (lam : ℕ) :
    (I.output V lam).decider.size ≤ sigma I lam :=
  ((I.decider_size V lam).trans (mul_pow_le_Csig I (by unfold Csig; omega)
    (by unfold Csig; omega) lam)).trans (le_sigmaFun _ _)

theorem sampler_size_le_sigma (V : Prog × Prog) (lam : ℕ) :
    (I.output V lam).sampler.size ≤ sigma I lam := by
  rw [I.output_sampler]
  exact (((sampler_size_le_s₁ I lam).trans (s₁_le I lam)).trans (mul_pow_le_Csig I
    (by unfold Csig; omega) (by unfold Csig; omega) lam)).trans (le_sigmaFun _ _)

/-- Both programs of the introspective verifier are within `σ(λ)`. -/
theorem size_le_sigma (V : Prog × Prog) (lam : ℕ) : (I.output V lam).size ≤ sigma I lam :=
  max_le (sampler_size_le_sigma I V lam) (decider_size_le_sigma I V lam)

theorem one_le_sigma (lam : ℕ) : 1 ≤ sigma I lam := one_le_sigmaFun _ _

theorem sigma_mono {m n : ℕ} (h : m ≤ n) : sigma I m ≤ sigma I n := sigmaFun_mono _ h

/-- The exponent `K` with `σ(z) ≤ z^K` for `z ≥ 2`. -/
noncomputable def K : ℕ := (polyBounded_sigmaFun (Csig I)).exists_le_pow.choose

theorem sigma_le_pow : ∀ z, 2 ≤ z → sigma I z ≤ z ^ K I :=
  (polyBounded_sigmaFun (Csig I)).exists_le_pow.choose_spec

/-- `μ`, from the margin claim. -/
noncomputable def mu : ℕ :=
  (exists_mu (b₁ := I.b) I.one_le_a A.one_le_a A.b_pos (K I) (I.C + 1)).choose

theorem C_succ_le_mu : I.C + 1 ≤ mu I A :=
  (exists_mu (b₁ := I.b) I.one_le_a A.one_le_a A.b_pos (K I) (I.C + 1)).choose_spec.1

theorem C_le_mu : I.C ≤ mu I A := (Nat.le_succ _).trans (C_succ_le_mu I A)

/-- `μ ≥ 1`, which answer reduction's completeness asks. -/
theorem one_le_mu : 1 ≤ mu I A := (Nat.le_add_left 1 _).trans (C_succ_le_mu I A)

/-- The threshold of the margin claim. -/
noncomputable def N₁ : ℕ :=
  (exists_mu (b₁ := I.b) I.one_le_a A.one_le_a A.b_pos (K I) (I.C + 1)).choose_spec.2.choose

theorem margin_spec : ∀ x : ℝ, (N₁ I A : ℝ) ≤ x → ∀ s : ℝ, 1 ≤ s → s ≤ x ^ (K I : ℝ) →
    s ^ A.a * x ^ (-((mu I A : ℝ) * A.b)) < eps1 I.a I.b x / 2 :=
  (exists_mu (b₁ := I.b) I.one_le_a A.one_le_a A.b_pos (K I) (I.C + 1)).choose_spec.2.choose_spec

theorem polyBounded_arBound :
    PolyBounded fun z => (A.bound.eval (z ^ mu I A + sigma I z + z + z)) ^ (mu I A + 1) :=
  (PolyBounded.eval A.bound ((((PolyBounded.id.pow _).add (polyBounded_sigmaFun (Csig I))).add
    PolyBounded.id).add PolyBounded.id)).pow _

/-- `β`, the parse-length exponent handed to repetition. -/
noncomputable def beta : ℕ := (polyBounded_arBound I A).exists_le_pow.choose

theorem arBound_le_pow :
    ∀ z, 2 ≤ z → (A.bound.eval (z ^ mu I A + sigma I z + z + z)) ^ (mu I A + 1) ≤ z ^ beta I A :=
  (polyBounded_arBound I A).exists_le_pow.choose_spec

/-- `P`, with `ε₂ ≥ x^{-P}`. -/
noncomputable def P : ℕ :=
  (exists_eps2_lower I.one_le_a I.b_pos A.one_le_a A.b_pos (mu I A) (K I)).choose

/-- The threshold of the lower bound on `ε₂`. -/
noncomputable def N₂ : ℕ :=
  (exists_eps2_lower I.one_le_a I.b_pos A.one_le_a A.b_pos (mu I A) (K I)).choose_spec.choose

theorem eps2_lower_spec : ∀ x : ℝ, (N₂ I A : ℝ) ≤ x → ∀ s : ℝ, 1 ≤ s → s ≤ x ^ (K I : ℝ) →
    x ^ (-(P I A : ℝ)) ≤ eps2 I.a I.b A.a A.b (mu I A) s x :=
  (exists_eps2_lower I.one_le_a I.b_pos A.one_le_a A.b_pos (mu I A) (K I)).choose_spec.choose_spec

/-- `τ`, the repetition exponent, against the parse length `2^{β(|λ| + |n|)} ≤ (λn + 1)^{6β}`. -/
noncomputable def tau : ℕ := (exists_tau R.c_pos (P I A) (6 * beta I A)).choose

theorem tau_spec : ∀ z : ℝ, (tau I A R : ℝ) ≤ z → ∀ k : ℝ, z ^ tau I A R ≤ k →
    ∀ B : ℝ, 0 ≤ B → B ≤ z ^ (6 * beta I A) → ∀ ε : ℝ, 0 < ε → z ^ (-(P I A : ℝ)) ≤ ε →
    Real.exp (-(R.c * ε ^ 13 * k / (B + 1))) ≤ 1 / 2 :=
  (exists_tau R.c_pos (P I A) (6 * beta I A)).choose_spec

/-- `|λn + 1| ≤ |λ| + |n|` for `λ ≥ 1`. -/
theorem size_mul_add_one_le {lam n : ℕ} (hl : 1 ≤ lam) :
    Nat.size (lam * n + 1) ≤ Nat.size lam + Nat.size n := by
  rw [Nat.size_le, pow_add]
  have h1 : lam + 1 ≤ 2 ^ Nat.size lam := Nat.lt_size_self lam
  have h2 : n + 1 ≤ 2 ^ Nat.size n := Nat.lt_size_self n
  have := Nat.mul_le_mul h1 h2
  nlinarith

/-- `(λn + 1)^τ ≤ k(n)`. -/
theorem pow_le_reps {lam n : ℕ} (hl : 1 ≤ lam) (tau : ℕ) :
    (lam * n + 1) ^ tau ≤ Repetition.reps lam tau n := by
  calc (lam * n + 1) ^ tau ≤ (2 ^ Nat.size (lam * n + 1)) ^ tau :=
        Nat.pow_le_pow_left (Nat.lt_size_self _).le _
    _ = 2 ^ (tau * Nat.size (lam * n + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ Repetition.reps lam tau n :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (size_mul_add_one_le hl))

/-- `B(n) ≤ (λn + 1)^{6β}` for `λ, n ≥ 1`. -/
theorem parseBound_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (beta : ℕ) :
    Repetition.parseBound lam beta n ≤ (lam * n + 1) ^ (6 * beta) := by
  have h1 : 2 ^ Nat.size lam ≤ 3 * (lam * n + 1) := by
    have := two_pow_size_le lam; nlinarith
  have h2 : 2 ^ Nat.size n ≤ 3 * (lam * n + 1) := by
    have := two_pow_size_le n; nlinarith
  have h9 : 9 ≤ (lam * n + 1) ^ 4 := by
    have : 2 ≤ lam * n + 1 := by nlinarith
    calc 9 ≤ 2 ^ 4 := by norm_num
      _ ≤ (lam * n + 1) ^ 4 := Nat.pow_le_pow_left this 4
  calc Repetition.parseBound lam beta n = (2 ^ Nat.size lam) ^ beta * (2 ^ Nat.size n) ^ beta := by
        rw [Repetition.parseBound, ← pow_mul, ← pow_mul, ← pow_add, Nat.mul_add, Nat.mul_comm beta,
          Nat.mul_comm beta]
    _ ≤ (3 * (lam * n + 1)) ^ beta * (3 * (lam * n + 1)) ^ beta :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h1 _) (Nat.pow_le_pow_left h2 _)
    _ = 9 ^ beta * (lam * n + 1) ^ (2 * beta) := by
        rw [← mul_pow, show 3 * (lam * n + 1) * (3 * (lam * n + 1)) =
          9 * (lam * n + 1) ^ 2 by ring, mul_pow, ← pow_mul]
    _ ≤ ((lam * n + 1) ^ 4) ^ beta * (lam * n + 1) ^ (2 * beta) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h9 _)
    _ = (lam * n + 1) ^ (6 * beta) := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- The threshold of the introspection margin, `⌈(4a)^{1/b}⌉`. -/
noncomputable def C₁ : ℕ := ⌈(4 * I.a) ^ (1 / I.b)⌉₊

/-- `C₀`, the threshold of the compression theorem. -/
noncomputable def C₀ : ℕ :=
  max (max (max 2 (C₁ I)) (max (N₁ I A) (N₂ I A))) (max A.C (tau I A R))

theorem C₀_spec {n : ℕ} (hn : C₀ I A R ≤ n) :
    2 ≤ n ∧ C₁ I ≤ n ∧ N₁ I A ≤ n ∧ N₂ I A ≤ n ∧ A.C ≤ n ∧ tau I A R ≤ n := by
  unfold C₀ at hn
  omega

/-! ## The data -/

/-- The answer-reduced verifier, at level `7 = max (5 + 2) 5`. -/
noncomputable def arOutput (V₁ : Verifier 5) (lam : ℕ) : Verifier 7 :=
  A.output V₁ lam (mu I A) (sigma I lam)

/-- The answer-reduced sampler, at level `7`. -/
noncomputable def arSampler (S : CL.Sampler 5) (lam : ℕ) : CL.Sampler 7 :=
  A.sampler S lam (mu I A) (sigma I lam)

theorem arOutput_sampler (V₁ : Verifier 5) (lam : ℕ) :
    (arOutput I A V₁ lam).sampler = arSampler I A V₁.sampler lam :=
  A.output_sampler V₁ lam _ _

theorem arSampler_prog (S : CL.Sampler 5) (lam : ℕ) :
    A.samplerProg (S.prog, lam, mu I A, sigma I lam) = (arSampler I A S lam).prog :=
  A.samplerProg_eq S lam _ _

theorem arOutput_decider (V₁ : Verifier 5) (lam : ℕ) :
    (arOutput I A V₁ lam).decider.prog =
      A.compute ((V₁.sampler.prog, V₁.decider.prog), lam, mu I A, sigma I lam) :=
  A.output_decider V₁ lam _ _

/-- The compressed sampler `𝒮^compr_λ`. -/
noncomputable def sampler (lam : ℕ) : CL.Sampler 7 :=
  R.sampler (arSampler I A (I.sampler lam) lam) lam (tau I A R)

/-- Its program, as a polynomial-time function of `λ`. -/
noncomputable def samplerProg : PolyTimeFun ℕ Prog :=
  R.samplerProg.comp
    ((A.samplerProg.comp
      (I.samplerProg.pair
        ((PolyTimeFun.id ℕ).pair ((PolyTimeFun.const (mu I A)).pair (sigmaFun (Csig I)))))).pair
      ((PolyTimeFun.id ℕ).pair (PolyTimeFun.const (tau I A R))))

theorem samplerProg_eq (lam : ℕ) : samplerProg I A R lam = (sampler I A R lam).prog := by
  simp only [samplerProg, sampler, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply,
    PolyTimeFun.id_apply, PolyTimeFun.const_apply]
  change R.samplerProg (A.samplerProg (I.samplerProg lam, lam, mu I A, sigma I lam), lam,
    tau I A R) = _
  rw [I.samplerProg_eq, arSampler_prog, R.samplerProg_eq]

/-- `Compress`: the program of the compressed decider, as a polynomial-time function of the
input programs and `λ`. -/
noncomputable def compress : PolyTimeFun ((Prog × Prog) × ℕ) Prog :=
  let lamF : PolyTimeFun ((Prog × Prog) × ℕ) ℕ := PolyTimeFun.snd
  let S₁ := I.samplerProg.comp lamF
  let params := lamF.pair ((PolyTimeFun.const (mu I A)).pair ((sigmaFun (Csig I)).comp lamF))
  let S₂ := A.samplerProg.comp (S₁.pair params)
  let D₂ := A.compute.comp ((S₁.pair I.compute).pair params)
  R.compute.comp ((S₂.pair D₂).pair
    (lamF.pair ((PolyTimeFun.const (tau I A R)).pair (PolyTimeFun.const (beta I A)))))

/-- The output of `Compress` on any input, as a `7`-level normal form verifier. -/
noncomputable def output (V : Prog × Prog) (lam : ℕ) : Verifier 7 :=
  R.output (arOutput I A (I.output V lam) lam) lam (tau I A R) (beta I A)

theorem output_sampler (V : Prog × Prog) (lam : ℕ) : (output I A R V lam).sampler = sampler I A R lam := by
  rw [output, R.output_sampler, arOutput_sampler, I.output_sampler, sampler]

theorem output_decider (V : Prog × Prog) (lam : ℕ) :
    (output I A R V lam).decider.prog = compress I A R (V, lam) := by
  simp only [compress, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.snd_apply,
    PolyTimeFun.const_apply]
  rw [output, R.output_decider, arOutput_decider, arOutput_sampler, ← arSampler_prog,
    I.output_sampler, I.output_decider, I.samplerProg_eq]
  rfl

/-! ## The accounting -/

/-- A bound on the size of the encoded parameters `(λ, μ, σ(λ))`. -/
noncomputable def pArg (lam : ℕ) : ℕ :=
  4 * Nat.size lam + 1 + (esize (mu I A) + (4 * Nat.size (sigma I lam) + 1) + 1) + 1

theorem esize_params_le (lam : ℕ) : esize (lam, mu I A, sigma I lam) ≤ pArg I A lam := by
  simp only [esize_prod, pArg]
  have := esize_nat_le lam
  have := esize_nat_le (sigma I lam)
  omega

/-- A bound on the size of the answer-reduced verifier, as a function of `λ`. -/
noncomputable def wSize (lam : ℕ) : ℕ :=
  max (A.samplerProg.timeBound.eval (s₁ I lam + pArg I A lam + 1))
    (A.compute.timeBound.eval (s₁ I lam + I.C * (lam + 1) ^ I.C + 1 + pArg I A lam + 1))

theorem arOutput_size_le (V : Prog × Prog) (lam : ℕ) :
    (arOutput I A (I.output V lam) lam).size ≤ wSize I A lam := by
  have hS : (I.output V lam).sampler.size ≤ s₁ I lam := by
    rw [I.output_sampler]; exact sampler_size_le_s₁ I lam
  have hD : (I.output V lam).decider.size ≤ I.C * (lam + 1) ^ I.C := I.decider_size V lam
  have hp := esize_params_le I A lam
  simp only [esize_prod] at hp
  refine max_le ?_ ?_
  · show esize (arOutput I A (I.output V lam) lam).sampler.prog ≤ _
    rw [arOutput_sampler, ← arSampler_prog]
    refine (A.samplerProg.esize_apply_le _).trans ((polynomial_eval_mono _ ?_).trans (le_max_left _ _))
    simp only [esize_prod]
    have : esize (I.output V lam).sampler.prog = (I.output V lam).sampler.size := rfl
    omega
  · show esize (arOutput I A (I.output V lam) lam).decider.prog ≤ _
    rw [arOutput_decider]
    refine (A.compute.esize_apply_le _).trans ((polynomial_eval_mono _ ?_).trans (le_max_right _ _))
    simp only [esize_prod]
    have : esize (I.output V lam).sampler.prog = (I.output V lam).sampler.size := rfl
    have : esize (I.output V lam).decider.prog = (I.output V lam).decider.size := rfl
    omega

/-- The bound of the answer-reduced verifier at `(λ, n)`. -/
noncomputable def arBound (lam n : ℕ) : ℕ :=
  AnswerReduction.outBound A.bound lam (mu I A) (sigma I lam) n

/-- The answer-reduced verifier's input-size degree. The pipeline fixes `μ`, so this
degree is independent of `λ`, `n`, and the input verifier. -/
noncomputable def arDegree : ℕ := AnswerReduction.outDegree A.deg (mu I A)

/-- The running-time bound of the compressed verifier at `(λ, n)`. -/
noncomputable def timeB (lam n : ℕ) : ℕ :=
  R.bound.eval (Repetition.arg lam (tau I A R) (beta I A) n
    (Budget.uniform (arBound I A lam n) (arDegree I A)) (wSize I A lam))

/-- The answer bound of the compressed verifier at `(λ, n)`. -/
noncomputable def ansB (lam n : ℕ) : ℕ :=
  R.ansBound.eval (Repetition.ansArg lam (tau I A R) (beta I A) n)

/-- Both bounds, as one function of `z = n + λ`. -/
noncomputable def G (z : ℕ) : ℕ := timeB I A R z z + ansB I A R z z

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size MIPRE.Pipeline.sigmaFun_mono

theorem timeB_mono {lam n lam' n' : ℕ} (hl : lam ≤ lam') (hn : n ≤ n') :
    timeB I A R lam n ≤ timeB I A R lam' n' := by
  unfold timeB Repetition.arg Repetition.reps Repetition.parseBound arBound
    AnswerReduction.outBound AnswerReduction.arg wSize pArg s₁ sigma
  simp only [Budget.uniform_S, Budget.uniform_d, Budget.uniform_D, Budget.uniform_B, Budget.uniform_k]
  gcongr <;> norm_num

theorem ansB_mono {lam n lam' n' : ℕ} (hl : lam ≤ lam') (hn : n ≤ n') :
    ansB I A R lam n ≤ ansB I A R lam' n' := by
  unfold ansB Repetition.ansArg Repetition.reps Repetition.parseBound
  gcongr <;> norm_num

theorem timeB_le_G (lam n : ℕ) : timeB I A R lam n ≤ G I A R (n + lam) :=
  (timeB_mono I A R (by omega) (by omega)).trans (Nat.le_add_right _ _)

theorem ansB_le_G (lam n : ℕ) : ansB I A R lam n ≤ G I A R (n + lam) :=
  (ansB_mono I A R (by omega) (by omega)).trans (Nat.le_add_left _ _)

theorem polyBounded_G : PolyBounded (G I A R) := by
  have hz : PolyBounded fun z : ℕ => z * z + 1 := (PolyBounded.id.mul PolyBounded.id).add_const 1
  have hpow2 : ∀ e : ℕ, PolyBounded fun z : ℕ => 2 ^ (e * (Nat.size z + Nat.size z)) := fun e =>
    (PolyBounded.two_pow_size 0 (2 * e)).mono fun z => le_of_eq (by ring_nf)
  have hsig : PolyBounded fun z : ℕ => sigma I z := polyBounded_sigmaFun (Csig I)
  have hs₁ : PolyBounded fun z : ℕ => s₁ I z :=
    PolyBounded.eval _ ((PolyBounded.size.const_mul 4).add_const 1)
  have hp : PolyBounded fun z : ℕ => pArg I A z := by
    unfold pArg
    exact ((((PolyBounded.size.const_mul 4).add_const 1).add
      ((PolyBounded.const _).add (((PolyBounded.size.comp hsig).const_mul 4).add_const 1)
        |>.add_const 1)).add_const 1)
  have hw : PolyBounded fun z : ℕ => wSize I A z := by
    refine ((PolyBounded.eval A.samplerProg.timeBound ((hs₁.add hp).add_const 1)).add
      (PolyBounded.eval A.compute.timeBound ((((hs₁.add ((PolyBounded.const I.C).mul
        ((PolyBounded.id.add_const 1).pow I.C))).add_const 1).add hp).add_const 1))).mono
      fun z => ?_
    exact max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _)
  have har : PolyBounded fun z : ℕ => arBound I A z z :=
    (PolyBounded.eval _ ((((hz.pow _).add hsig).add PolyBounded.id).add PolyBounded.id)).pow _
  have ht : PolyBounded fun z : ℕ => timeB I A R z z := by
    unfold timeB Repetition.arg
    simp only [Budget.uniform_S, Budget.uniform_d, Budget.uniform_D, Budget.uniform_B,
      Budget.uniform_k]
    exact PolyBounded.eval _ ((((((hpow2 _).add (hpow2 _)).add har).add har).add har).add har
      |>.add hw |>.add PolyBounded.id |>.add (PolyBounded.const _) |>.add (PolyBounded.const _)
      |>.add PolyBounded.id |>.add (PolyBounded.const _))
  have ha : PolyBounded fun z : ℕ => ansB I A R z z := by
    unfold ansB Repetition.ansArg
    exact PolyBounded.eval _ ((hpow2 _).add (hpow2 _))
  exact ht.add ha

/-- The polynomial `poly(n, λ)` of the compression theorem. -/
noncomputable def bound : Polynomial ℕ := (polyBounded_G I A R).poly

theorem timeB_le_bound (lam n : ℕ) : timeB I A R lam n ≤ (bound I A R).eval (n + lam) :=
  (timeB_le_G I A R lam n).trans ((polyBounded_G I A R).le_poly_eval _)

theorem ansB_le_bound (lam n : ℕ) : ansB I A R lam n ≤ (bound I A R).eval (n + lam) :=
  (ansB_le_G I A R lam n).trans ((polyBounded_G I A R).le_poly_eval _)

/-- The introspective verifier is within answer reduction's input budget. -/
theorem introOutput_within (V : Prog × Prog) (lam n : ℕ) :
    (I.output V lam).Within n (AnswerReduction.inBudget lam (mu I A) n) := by
  refine (I.within V lam n).mono ⟨?_, ?_, ?_, C_le_mu I A, ?_⟩ <;>
    simp only [Introspection.budget, AnswerReduction.inBudget, Introspection.ansBound,
      AnswerReduction.inAns]
  · exact Nat.pow_le_pow_right (by omega) (C_le_mu I A)
  · exact Nat.pow_le_pow_right (by omega) (C_le_mu I A)
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) (C_le_mu I A))
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) (C_le_mu I A))

theorem ansBound_le_inAns (lam n : ℕ) :
    Introspection.ansBound I.C lam n ≤ AnswerReduction.inAns lam (mu I A) n :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) (C_le_mu I A))

/-- The answer-reduced verifier is within its bound. -/
theorem arOutput_within (V : Prog × Prog) (lam n : ℕ) :
    (arOutput I A (I.output V lam) lam).Within n
      (Budget.uniform (arBound I A lam n) (arDegree I A)) :=
  A.within (I.output V lam) lam (mu I A) (sigma I lam) n (introOutput_within I A V lam n)
    (size_le_sigma I V lam)

/-- The compressed verifier is within its bounds. -/
theorem output_within (V : Prog × Prog) (lam n : ℕ) :
    (output I A R V lam).Within n
      ⟨timeB I A R lam n, timeB I A R lam n, timeB I A R lam n, R.deg * (arDegree I A + 1),
        ansB I A R lam n⟩ := by
  have h := R.within (arOutput I A (I.output V lam) lam) lam (tau I A R) (beta I A) n _
    (arOutput_within I A V lam n)
  refine h.mono ⟨?_, ?_, ?_, le_rfl, le_rfl⟩ <;>
  · show R.bound.eval _ ≤ timeB I A R lam n
    unfold timeB
    exact polynomial_eval_mono _ (by
      unfold Repetition.arg
      have := arOutput_size_le I A V lam
      omega)

/-- The answer bound of the answer-reduced verifier is below the parse length handed to
repetition, for `λ ≥ 1` and `n ≥ 1`. -/
theorem arBound_le_parseBound {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    arBound I A lam n ≤ Repetition.parseBound lam (beta I A) n := by
  have hz : 2 ≤ lam * n + 1 := by nlinarith
  have hs : sigma I lam ≤ sigma I (lam * n + 1) := sigma_mono I (by nlinarith)
  calc arBound I A lam n ≤
        (A.bound.eval ((lam * n + 1) ^ mu I A + sigma I (lam * n + 1) + (lam * n + 1) +
          (lam * n + 1))) ^ (mu I A + 1) :=
        Nat.pow_le_pow_left (polynomial_eval_mono _ (by
          unfold AnswerReduction.arg
          have h1 : lam ≤ lam * n + 1 := by nlinarith
          have h2 : n ≤ lam * n + 1 := by nlinarith
          omega)) _
    _ ≤ (lam * n + 1) ^ beta I A := arBound_le_pow I A _ hz
    _ ≤ _ := pow_le_reps hl _

/-! ## The value chain -/

/-- **Completeness of `Compress`**: the three completeness clauses chained. -/
theorem output_hasPerfectPCC (V : Verifier 7) (lam n : ℕ) (hB : V.IsBounded lam)
    (hn : C₀ I A R ≤ n) (h : V.HasPerfectPCC (2 ^ n) ((2 ^ n) ^ lam)) :
    (output I A R (V.sampler.prog, V.decider.prog) lam).HasPerfectPCC n (ansB I A R lam n) := by
  obtain ⟨h2, -, -, -, hC, -⟩ := C₀_spec I A R hn
  have hlam : 1 ≤ lam := by have := hB.two_le; omega
  have h₁ := I.completeness V lam n hB h
  have h₁' := (I.output _ lam).hasPerfectPCC_of_le (ansBound_le_inAns I A lam n) h₁
  have h₂ := A.completeness (I.output _ lam) lam (mu I A) (sigma I lam) n hC hlam (one_le_mu I A)
    (introOutput_within I A _ lam n) (decider_size_le_sigma I _ lam) h₁'
  have h₂' : (arOutput I A (I.output _ lam) lam).HasPerfectPCC n
      (Repetition.parseBound lam (beta I A) n) :=
    Verifier.hasPerfectPCC_of_le _ (arBound_le_parseBound I A hlam (by omega)) h₂
  exact R.completeness _ lam (tau I A R) (beta I A) n h₂'

/-- **Soundness of `Compress`**, value form: the three soundness clauses contrapositively,
through the margins. -/
theorem output_valStar_le (V : Verifier 7) (lam n : ℕ) (hB : V.IsBounded lam)
    (hn : C₀ I A R ≤ n) (h : V.valStar (2 ^ n) ((2 ^ n) ^ lam) ≤ 1 / 2) :
    (output I A R (V.sampler.prog, V.decider.prog) lam).valStar n (ansB I A R lam n) ≤ 1 / 2 := by
  obtain ⟨h2, hC₁, hN₁, hN₂, hC, htau⟩ := C₀_spec I A R hn
  have hlam : 1 ≤ lam := by have := hB.two_le; omega
  -- the real parameters
  set x : ℝ := (lam : ℝ) * n with hx
  have hnx : (n : ℝ) ≤ x := by
    rw [hx]; exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hlam)
  have hx1 : 1 ≤ x := le_trans (by exact_mod_cast (show 1 ≤ n by omega)) hnx
  have hx0 : 0 < x := by linarith
  set s : ℝ := (sigma I lam : ℝ) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact_mod_cast one_le_sigma I lam
  have hsx : s ≤ x ^ (K I : ℝ) := by
    have h1 : sigma I lam ≤ (lam * n) ^ K I :=
      (sigma_mono I (by nlinarith)).trans (sigma_le_pow I _ (by nlinarith))
    rw [hs, hx, Real.rpow_natCast]
    exact_mod_cast h1
  set ε₁ := eps1 I.a I.b x with hε₁
  set ε₂ := eps2 I.a I.b A.a A.b (mu I A) s x with hε₂
  have hε₁0 : 0 < ε₁ := eps1_pos I.one_le_a hx0
  have hε₂0 : 0 < ε₂ := eps2_pos I.one_le_a (by linarith) hx0
  have hε₂1 : ε₂ ≤ 1 := eps2_le_one I.one_le_a I.b_pos A.one_le_a A.b_pos hs1 hx1
  -- step 1: the introspective verifier has value at most `1 - ε₁`
  have h₁ : (I.output (V.sampler.prog, V.decider.prog) lam).valStar n
      (Introspection.ansBound I.C lam n) ≤ 1 - ε₁ := by
    by_contra hc
    push Not at hc
    have hsound := I.soundness V lam n ε₁ hB (by omega) hε₁0 hc
    have hC₁' : (4 * I.a) ^ (1 / I.b) ≤ x := by
      have := Nat.le_ceil ((4 * I.a) ^ (1 / I.b))
      have : ((C₁ I : ℕ) : ℝ) ≤ n := by exact_mod_cast hC₁
      unfold C₁ at this
      linarith
    have hm := intro_margin I.one_le_a I.b_pos hx1 hC₁'
    unfold Introspection.delta at hsound
    linarith
  -- step 2: the answer-reduced verifier has value at most `1 - ε₂`
  have h₂ : (arOutput I A (I.output (V.sampler.prog, V.decider.prog) lam) lam).valStar n
      (arBound I A lam n) ≤ 1 - ε₂ := by
    by_contra hc
    push Not at hc
    have hsound := A.soundness (I.output _ lam) lam (mu I A) (sigma I lam) n ε₂ hC h2 hlam
      (introOutput_within I A _ lam n) (decider_size_le_sigma I _ lam) hε₂0 hc
    have hN₁' : (N₁ I A : ℝ) ≤ x := le_trans (by exact_mod_cast hN₁) hnx
    have hm := ar_margin I.one_le_a A.b_pos (by linarith : 0 < s) hx0
      (margin_spec I A x hN₁' s hs1 hsx)
    have heq : (I.output (V.sampler.prog, V.decider.prog) lam).valStar n
        (AnswerReduction.inAns lam (mu I A) n) =
        (I.output (V.sampler.prog, V.decider.prog) lam).valStar n
          (Introspection.ansBound I.C lam n) :=
      (I.within _ lam n).valStar_eq (ansBound_le_inAns I A lam n)
    unfold AnswerReduction.delta at hsound
    rw [heq] at hsound
    linarith
  -- step 3: the same at the parse length
  have h₃ : (arOutput I A (I.output (V.sampler.prog, V.decider.prog) lam) lam).valStar n
      (Repetition.parseBound lam (beta I A) n) ≤ 1 - ε₂ := by
    rwa [(arOutput_within I A _ lam n).valStar_eq (arBound_le_parseBound I A hlam (by omega))]
  -- step 4: repetition
  have h₄ := R.soundness _ lam (tau I A R) (beta I A) n ε₂ hε₂0 hε₂1 h₃
  refine h₄.trans ?_
  have hz : (tau I A R : ℝ) ≤ ((lam * n + 1 : ℕ) : ℝ) := by
    have : tau I A R ≤ lam * n + 1 := by nlinarith
    exact_mod_cast this
  have hxz : x ≤ ((lam * n + 1 : ℕ) : ℝ) := by rw [hx]; push_cast; linarith
  have hlow : ((lam * n + 1 : ℕ) : ℝ) ^ (-(P I A : ℝ)) ≤ ε₂ := by
    refine le_trans ?_ (eps2_lower_spec I A x (le_trans (by exact_mod_cast hN₂) hnx) s hs1 hsx)
    rw [Real.rpow_neg hx0.le, Real.rpow_neg (by positivity)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx0 _) (Real.rpow_le_rpow hx0.le hxz (by positivity))
  have hk : ((lam * n + 1 : ℕ) : ℝ) ^ tau I A R ≤ (Repetition.reps lam (tau I A R) n : ℝ) := by
    exact_mod_cast pow_le_reps hlam (tau I A R)
  have hBle : (Repetition.parseBound lam (beta I A) n : ℝ) ≤
      ((lam * n + 1 : ℕ) : ℝ) ^ (6 * beta I A) := by
    exact_mod_cast parseBound_le hlam (by omega) (beta I A)
  exact tau_spec I A R _ hz _ hk _ (by positivity) hBle ε₂ hε₂0 hlow

end MIPRE.Pipeline

namespace MIPRE

open Cost

/-- **The compression theorem from its stages** (blueprint `thm:compression`, proof): an
`Introspection 7`, an `AnswerReduction 5` and a `Repetition 7` give a `GapCompression`. -/
noncomputable def GapCompression.ofPipeline (I : Introspection 7) (A : AnswerReduction 5)
    (R : Repetition 7) : GapCompression where
  C₀ := Pipeline.C₀ I A R
  sampler := Pipeline.sampler I A R
  samplerProg := Pipeline.samplerProg I A R
  samplerProg_eq := Pipeline.samplerProg_eq I A R
  compress := Pipeline.compress I A R
  output := Pipeline.output I A R
  output_sampler := Pipeline.output_sampler I A R
  output_decider := Pipeline.output_decider I A R
  bound := Pipeline.bound I A R
  deg := R.deg * (Pipeline.arDegree I A + 1)
  sampler_time lam n := by
    have h := (Pipeline.output_within I A R (.nil, .nil) lam n).sampler_time
    rw [Pipeline.output_sampler] at h
    exact h.mono (Pipeline.timeB_le_bound I A R lam n) le_rfl
  sampler_dim lam n := by
    have h := (Pipeline.output_within I A R (.nil, .nil) lam n).sampler_dim
    rw [Pipeline.output_sampler] at h
    exact h.trans (Pipeline.timeB_le_bound I A R lam n)
  decider_time V lam n :=
    (Pipeline.output_within I A R V lam n).decider_time.mono
      (Pipeline.timeB_le_bound I A R lam n) le_rfl
  output_rejects_long V lam n x y a b hlen :=
    Verifier.RejectsLong.mono (Pipeline.ansB_le_bound I A R lam n)
      (Pipeline.output_within I A R V lam n).rejectsLong x y a b hlen
  completeness V lam n hB hn h :=
    Verifier.hasPerfectPCC_of_le _ (Pipeline.ansB_le_bound I A R lam n)
      (Pipeline.output_hasPerfectPCC I A R V lam n hB hn h)
  soundness V lam n hB hn h := by
    rw [(Pipeline.output_within I A R _ lam n).valStar_eq (Pipeline.ansB_le_bound I A R lam n)]
    exact Pipeline.output_valStar_le I A R V lam n hB hn h

end MIPRE


