-- Prove2me | Definitions.Def_ExactParallelSampling_QuasiUniform_Sampler
-- name    : ExactParallelSampling_QuasiUniform_Sampler
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:50:53.645061+00:00
-- url     : https://prove2.me/theorems/092ae7c3-7fd8-412d-b4d2-6bcdc0e51bcf
-- title:
--   Algorithm 1 (Sample) on conditional laws of marginals, parameterized by an iteration procedure; T(m, D) and T̄(m, D)
-- statement:
--   Algorithm 1 (pp. 21–22) and the quantities of Lemma 4.5 (p. 23). Section 4 uses Iterate "only through the guarantees of Theorem 6.1" (p. 20), so `Sample` takes an iteration algorithm `It` (an `IterAlgorithm`) and the round cost $\rho$ of a $\mathrm{Rec}$ phase as parameters.
--
--   A call `sampleAux p It ρ n n₀ fuel A K y ω` samples the law $\nu$ of $X_A$ given $X_K=y$ through the oracle of $\mu$ (Lemma 2.1). It returns the full assignment equal to $y$ off $A$ and to the sample on $A$, its number of rounds, and whether some run of Iterate in it returned "fail". In order:
--
--   1. **Line 1.** One round of queries $\Pr[X_j=a]$. The coordinates $E_1$ with one possible value are constants.
--   2. **Line 2.** If $|E'|\le\max(\log^3n,n_0)$, with $E'=A\setminus E_1$ and $n$ the original number of coordinates, sample $X_{E'}$ by the chain rule, one coordinate per round, in increasing order. Each coordinate is drawn exactly from its computed conditional law by the inverse distribution function.
--   3. **Line 3.** Otherwise run `It` on $I(\nu)$ restricted to $E'$, relabelled increasingly as $\mathrm{Fin}\,|E'|$, with fresh sub-tapes until a run does not fail. Independence queries are answered as in Lemma 4.1, and $\mathrm{Rec}$ instances by the exact circuit families, as Lemma 7.2 computes them, each phase charged $\rho$ rounds.
--   4. **Contract $U$.** Draw $z$ uniformly from $\prod_{j\in U}\Omega_j$ and recurse on $X_{E'\setminus U}$ given $X_U=z$.
--   5. **Defer $R$.** Recurse on $X_{E'\setminus R}$ (main call), then on $X_R$ given its output (residual call).
--
--   Rounds add: $1+{}$(chain-rule rounds, or Iterate rounds plus the rounds of the recursive calls). A call's tape is split into disjoint sub-tapes for its own draws, for the runs of Iterate and for each recursive call. A fuel argument decreases at every call; at fuel $0$ there is no output, which cannot happen when every recursive call is on fewer coordinates. `sample` is the top-level call on all coordinates.
--
--   - `IterGuarantee It ρ n₀`: Theorem 6.1's output guarantees on every ground set of $m\ge n_0$ elements, every independence system with (A1) and every correct $\mathrm{Rec}$. Every run halts and returns either "contract" with $U\in I$, $|U|\ge m/(5000\log m)$, or "defer" with $|R|\ge2^{-26}m/\log m$ and certificates $T_x\subseteq E\setminus R$, $T_x\in I$, $T_x+x\notin I$, or "fail"; and $\Pr[\text{fail}]\le2^{-m/2}$.
--   - `condLawsUpTo p λ m D` lists the triples $(A,K,y)$ with $A\cap K=\emptyset$, $\Pr[X_K=y]>0$, $|A|\le m$ and $D_\lambda(\nu)\le D$. `Texp` $=T(m,D)$ is the supremum of $\mathbb E[\text{rounds of Sample}(\nu)]$ over them. `Tbar` $=\bar T(m,D)$ is the supremum, over them and over the runs in which no run of Iterate fails, of the number of rounds.
--
--   For a probability distribution, `drawFrom` always returns a positive-mass value, including at u=1 where it returns the largest such value. This retains the exact draw law and the all-run interpretation of T̄. `IterGuarantee` includes validity of every recovery input under (A2).
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Algorithm 1, §4.2–4.3 and Lemma 4.5, p. 20–23; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol

noncomputable section
open Classical MeasureTheory

namespace ExactParallelSampling.QuasiUniform

/-! # Algorithm 1: Sample(ν), the deferral sampler (§4.2–4.3, pp. 21–23)

Section 4 uses the iteration procedure of Section 6 "only through the guarantees of Theorem 6.1"
(p. 20), so `Sample` is parameterized by an iteration algorithm `It` in the independence-oracle
model (`IterAlgorithm`), run on `I(ν)` restricted to the non-constant coordinates `E'` (relabelled
increasingly as `Fin |E'|`). Its independence queries are answered by Lemma 4.1 (one counting query
each) and its `Rec` instances by the moment recovery of Lemma 7.2, which returns the family of all
circuits of `B + x` exactly and is charged `ρ` rounds (`ρ = R_q` in §7).

Every call receives the law `ν` of `X_A` given `X_K = y` for disjoint `A, K ⊆ E`, accessed through
the oracle of `μ` (Lemma 2.1). A call returns the full assignment equal to `y` off `A` and to the
sample on `A`, the number of rounds it used, and whether some run of Iterate in it returned
"fail". Calls run one after another, so rounds add. Randomness: the tape `ω` of a call is split into
disjoint sub-tapes (`subTape ω 0` for its own draws, `subTape ω 1` for the runs of Iterate,
`subTape ω 2` and `subTape ω 3` for its first and second recursive call), so the selection
randomness is independent of every later sample draw. The recursion is on a fuel argument that
decreases at every call; a call made with fuel `0` returns no output (unreachable when every
recursive call is on fewer coordinates, as Theorem 6.1's outputs guarantee). -/

variable {E α : Type*} [Fintype E] [LinearOrder E] [Fintype α] [LinearOrder α] [Nonempty α]

/-- The `k`-th sub-tape of a tape (disjoint coordinates for distinct `k`). -/
def subTape (ω : Tape) (k : ℕ) : Tape := fun i => ω (Nat.pair k i)

/-- Exact sampling from a computed distribution `w` on `α` with one uniform number `u`
(inverse distribution function along the order of `α`). At the endpoint `u = 1`, choose the
largest positive-mass value, so every tape yields a supported draw for a probability distribution;
this matters for the supremum over all failure-free runs in Lemma 4.5. -/
def drawFrom (w : α → ℝ) (u : ℝ) : α :=
  let positive := Finset.univ.filter (fun a => 0 < w a)
  let good := positive.filter (fun a => u < ∑ b ∈ Finset.univ.filter (· ≤ a), w b)
  if h : good.Nonempty then good.min' h
  else if h : positive.Nonempty then positive.max' h else Classical.arbitrary α

/-- A uniform draw from a finite set `S`. -/
def drawUniform (S : Finset α) (u : ℝ) : α :=
  drawFrom (fun a => if a ∈ S then 1 / (S.card : ℝ) else 0) u

/-- The chain rule (line 2): the coordinates of the list are sampled one per round, each from its
conditional law given `X_K = y` and the values already drawn; the `t`-th uses tape entry `t`. -/
def chainRule (p : (E → α) → ℝ) : List E → ℕ → Finset E → (E → α) → Tape → E → α
  | [], _, _, y, _ => y
  | j :: js, t, K, y, ω =>
    let a := drawFrom (fun a => condCount p K y {j} (fun _ => a)) (ω t)
    chainRule p js (t + 1) (insert j K) (Function.update y j a) ω

/-- The result of a call of Sample: output assignment (`none` if the call does not end), number
of rounds (`⊤` if it does not end), and whether some run of Iterate returned "fail". -/
structure SampleResult (E α : Type*) where
  out : Option (E → α)
  rounds : ℕ∞
  failed : Bool

/-- The position of a coordinate in the order of `E` (to index tape entries). -/
def coordIndex (j : E) : ℕ := (Finset.univ.filter (· < j)).card

/-- `I(ν)` on `E'`, relabelled as `Fin |E'|`, for `ν` the law of `X_A` given `X_K = y`. -/
def relabelIndep (p : (E → α) → ℝ) (K : Finset E) (y : E → α) (E' : Finset E) :
    Finset (Fin E'.card) → Prop :=
  fun T => IsCondIndep p K y (T.map (E'.orderEmbOfFin rfl).toEmbedding)

/-- The oracle seen by Iterate on `E'`: independence queries by Lemma 4.1, `Rec` by the exact
circuit families (Lemma 7.2). -/
def iterOracle (p : (E → α) → ℝ) (K : Finset E) (y : E → α) (E' : Finset E) :
    IQuery (Fin E'.card) → IAnswer (Fin E'.card) :=
  indepOracle (relabelIndep p K y E') (fun B x => circuitsIn (relabelIndep p K y E') (insert x B))

/-- Algorithm 1, `Sample(ν)` for `ν` the law of `X_A` given `X_K = y`, with `n` the original number
of coordinates, `n0` the size threshold (line 2 uses `max(log³ n, n₀)` with the original `n`),
`It` the iteration algorithm and `ρ` the round cost of one `Rec` phase. -/
def sampleAux (p : (E → α) → ℝ) (It : IterAlgorithm) (ρ n n0 : ℕ) :
    ℕ → Finset E → Finset E → (E → α) → Tape → SampleResult E α
  | 0, _, _, _, _ => ⟨none, ⊤, false⟩
  | f + 1, A, K, y, ω =>
    -- line 1: one round of queries `Pr[X_j = a]`; constant coordinates `E₁`
    let E1 := A.filter (fun j => (condSingleSupp p K y j).card = 1)
    let yc : E → α := fun j =>
      if j ∈ E1 then
        (if h : (condSingleSupp p K y j).Nonempty then (condSingleSupp p K y j).min' h else y j)
      else y j
    let E' := A \ E1
    if (E'.card : ℝ) ≤ max ((Real.logb 2 n) ^ 3) (n0 : ℝ) then
      -- line 2: the chain rule, one coordinate per round
      ⟨some (chainRule p (E'.sort (· ≤ ·)) 0 K yc (subTape ω 0)), 1 + (E'.card : ℕ∞), false⟩
    else
      -- line 3: run Iterate with fresh selection randomness until it does not fail
      let P := It E'.card ρ
      let ans := iterOracle p K y E'
      let τ : ℕ → Tape := fun k => subTape (subTape ω 1) k
      if h : ∃ k, P.output ans (τ k) ≠ some IterOutput.fail then
        let k := Nat.find h
        let cost : ℕ∞ := ∑ i ∈ Finset.range (k + 1), iterRounds P ρ ans (τ i)
        let fl : Bool := decide (0 < k)
        let e := (E'.orderEmbOfFin rfl).toEmbedding
        match P.output ans (τ k) with
        | some (IterOutput.contract U) =>
          -- lines 4–5: draw `z` uniformly from `∏_{j ∈ U} Ω_j`, recurse on `X_{E'∖U}` given `X_U = z`
          let U' := U.map e
          let z : E → α := fun j =>
            if j ∈ U' then drawUniform (condSingleSupp p K y j) (subTape ω 0 (coordIndex j))
            else yc j
          let r := sampleAux p It ρ n n0 f (E' \ U') (K ∪ U') z (subTape ω 2)
          ⟨r.out, 1 + cost + r.rounds, fl || r.failed⟩
        | some (IterOutput.defer R _) =>
          -- lines 6–7: sample `X_{E'∖R}`, then `X_R` given it (main call, then residual call)
          let R' := R.map e
          let r1 := sampleAux p It ρ n n0 f (E' \ R') K yc (subTape ω 2)
          match r1.out with
          | some y1 =>
            let r2 := sampleAux p It ρ n n0 f R' (K ∪ (E' \ R')) y1 (subTape ω 3)
            ⟨r2.out, 1 + cost + r1.rounds + r2.rounds, fl || r1.failed || r2.failed⟩
          | none => ⟨none, ⊤, fl || r1.failed⟩
        | _ => ⟨none, ⊤, fl⟩
      else ⟨none, ⊤, true⟩

/-- `Sample(ν)` for `ν` the law of `X_A` given `X_K = y`, with `n = |E|` the original number of
coordinates of `μ`. -/
def sampleCond (p : (E → α) → ℝ) (It : IterAlgorithm) (ρ n0 : ℕ) (A K : Finset E) (y : E → α)
    (ω : Tape) : SampleResult E α :=
  sampleAux p It ρ (Fintype.card E) n0 (A.card + 1) A K y ω

/-- `Sample(μ)` on all coordinates. -/
def sample (p : (E → α) → ℝ) (It : IterAlgorithm) (ρ n0 : ℕ) (ω : Tape) : SampleResult E α :=
  sampleCond p It ρ n0 Finset.univ ∅ (fun _ => Classical.arbitrary α) ω

/-- The guarantees of Theorem 6.1 that Section 4 uses, for an iteration algorithm `It` on ground
sets of every size `m ≥ n₀` with `Rec` costing `ρ` rounds: on every independence system with (A1)
and every correct circuit recovery, every run halts and returns "contract" with `U ∈ I`,
`|U| ≥ m/(5000 log m)`, or "defer" with `|R| ≥ 2^{−26} m / log m` and certificates
`T_x ⊆ E ∖ R`, `T_x ∈ I`, `T_x + x ∉ I`, or "fail"; and "fail" has probability at most `2^{−m/2}`. -/
def IterGuarantee (It : IterAlgorithm) (ρ n0 : ℕ) : Prop :=
  ∀ m : ℕ, n0 ≤ m → ∀ I : Finset (Fin m) → Prop, SubsamplingSM.Offline.IsIndepSystem I →
    (∀ x, I {x}) → ∀ recAns, IsCircuitRecovery I recAns →
      (∀ ω, (It m ρ).rounds (indepOracle I recAns) ω ≠ ⊤ ∧
        RecoveryCallsValid (It m ρ) I (indepOracle I recAns) ω ∧
        (∀ U, (It m ρ).output (indepOracle I recAns) ω = some (IterOutput.contract U) →
          I U ∧ (m : ℝ) / (5000 * Real.logb 2 m) ≤ U.card) ∧
        (∀ R cert, (It m ρ).output (indepOracle I recAns) ω = some (IterOutput.defer R cert) →
          (2 : ℝ) ^ (-26 : ℤ) * m / Real.logb 2 m ≤ R.card ∧
          ∀ x ∈ R, cert x ⊆ Finset.univ \ R ∧ I (cert x) ∧ ¬ I (insert x (cert x)))) ∧
      tapeLaw {ω | (It m ρ).output (indepOracle I recAns) ω = some IterOutput.fail} ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(m : ℝ) / 2))

/-- The conditional laws of marginals of `μ` on at most `m` coordinates with level at most `D`:
triples `(A, K, y)` with `A ∩ K = ∅`, `Pr[X_K = y] > 0`, `|A| ≤ m` and `D_λ(ν) ≤ D`, `ν` the law
of `X_A` given `X_K = y`. -/
def condLawsUpTo (p : (E → α) → ℝ) (lam : ℕ → ℕ) (m D : ℕ) : Set (Finset E × Finset E × (E → α)) :=
  {ν | Disjoint ν.1 ν.2.1 ∧ 0 < count p ν.2.1 ν.2.2 ∧ ν.1.card ≤ m ∧
    condLevel p lam ν.1 ν.2.1 ν.2.2 ≤ D}

/-- `T(m, D)`: the supremum of the expected number of rounds of `Sample(ν)` over those `ν`. -/
def Texp (p : (E → α) → ℝ) (It : IterAlgorithm) (ρ n0 : ℕ) (lam : ℕ → ℕ) (m D : ℕ) : ENNReal :=
  ⨆ ν ∈ condLawsUpTo p lam m D,
    ∫⁻ ω, (((sampleCond p It ρ n0 ν.1 ν.2.1 ν.2.2 ω).rounds : ℕ∞) : ENNReal) ∂tapeLaw

/-- `T̄(m, D)`: the supremum, over the same `ν` and over all runs of `Sample(ν)` in which no run of
Iterate returns "fail", of the number of rounds of the run. -/
def Tbar (p : (E → α) → ℝ) (It : IterAlgorithm) (ρ n0 : ℕ) (lam : ℕ → ℕ) (m D : ℕ) : ENNReal :=
  ⨆ ν ∈ condLawsUpTo p lam m D, ⨆ ω,
    ⨆ (_ : (sampleCond p It ρ n0 ν.1 ν.2.1 ν.2.2 ω).failed = false),
      (((sampleCond p It ρ n0 ν.1 ν.2.1 ν.2.2 ω).rounds : ℕ∞) : ENNReal)

end ExactParallelSampling.QuasiUniform


