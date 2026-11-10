-- Prove2me | Definitions.Def_BayesOptStop_Scheme_Algorithms
-- name    : BayesOptStop_Scheme_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:19:55.646205+00:00
-- url     : https://prove2.me/theorems/62084aaf-7336-4be4-b680-f2e8e990d24a
-- title:
--   Randomized online stopping policies, estimators, Algorithms 1–2 and the output law of Algorithm 3
-- statement:
--   A **policy** draws internal randomness $u$ from a probability space, independent of the path, and selects at time $\tau(u,\omega)$ ($\ge n$: never, reward $0$); it is valid when measurable in $u$ and **online**: stopping at time $s$ depends only on $h_{s+1}$. Its reward $r(A)=\mathbb E[X_\tau]$ is over world, path and $u$. $A$ is $\alpha$-competitive against $(Z_t)=\mathbb E[M\mid F_t]$ if $r(A)\ge\alpha\,\mathbb E[Z_1]$.
--
--   An **estimator** of a process $Z$ draws a seed $e$ and outputs $L_t(h_t)$; the **guarantee** with accuracy $\beta$ (Algorithm 1 line 8, Step 3 of Lemma 5): measurable in the seed, a function of $h_t$ only, and $L_t/Z_t\in[1-\beta,1]$ with probability at least $1-\beta/n$ at every reachable $h_t$.
--
--   **Algorithm 1** on $(A,\alpha,L)$: with probability $\gamma=1/(1+\ln(1/\alpha))$ run $A$; otherwise draw $Q\in[\alpha,1]$ with density $1/(q\ln(1/\alpha))$ (as $Q=\alpha^V$, $V\sim U(0,1)$; $Q=1$ when $\alpha=1$, where that branch has probability $0$), draw fresh independent seeds $U_1,\dots,U_n$, and accept the first $X_t\ge QL_t(h_t)$. **Algorithm 2**: $A_0=A$, $A_{j+1}$ is Algorithm 1 applied to $A_j$, $\alpha_j$ and the level-$j$ estimator of $Z^{(j)}$.
--
--   **Algorithm 3** is specified by a finite weighted computation tree: at level zero return 1; otherwise use the printed cube-root accuracy, ceiling sample count and failure allocation, independently draw biased continuations at every time, recursively estimate and average, take the maximum ratio, and multiply by a fresh recursive estimate on the original path. `algorithm3Law` specifies the complete output law; it grants no machine instruction or runtime. Claim 3 requires a timed program realizing this law.
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Algorithm 1 p. 12; Primal-Dual Improvement and Algorithm 2 pp. 14–15; Lemma 5 Step 3 p. 22; Algorithm 3 p. 20; App. B.4 pp. 41–42

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement

open scoped BigOperators
open MeasureTheory

namespace BayesOptStop.Scheme

/-!
# Randomized online stopping policies, Algorithm 1 and Algorithm 2 (§§3.1–3.2, 3.4)

Source: AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), held STOC 2027 submission,
SHA-256 fecfa05a…c4241: Algorithm 1 (p. 12), Primal-Dual Improvement and Algorithm 2
(pp. 14–15), Lemma 5 and Step 3 of its proof (pp. 20–22).

* A **policy** draws its internal randomness `u` from a probability space `(Seed, law)`,
  independent of the path, and stops at the (0-based) time `stop u ω`; a value `≥ n` means it
  never selects and earns `0`. It is **online** when, for every `u`, stopping at time `s`
  depends only on the history `h_{s+1}` (`Policy.IsValid`). Its expected reward
  `r(A) = E[X_τ]` is over the world, the path and `u`.
* `α`-competitive against the dual martingale of a terminal `M`: `r(A) ≥ α · E[Z_1]`,
  `Z_1 = E[M | F_1]` (p. 10).
* An **estimator** of a process `Z` draws a seed `e` from `(Seed, law)` and outputs
  `est e t ω = L_t(h_t)`; it depends on the path only through the history `h_t`. It meets the
  accuracy-`β`, failure-`β/n` guarantee of Algorithm 1 line 8 / Step 3 of Lemma 5 at every
  reachable history (`Estimator.Guarantee`).
* `primalImprove` is Algorithm 1 with fresh, independent seeds `U_1, …, U_n` for the estimates
  `L_1, …, L_n`. The coin is a uniform `c ∈ (0,1)`: run `A` iff `c < γ = 1/(1 + ln(1/α))`.
  The cutoff is `Q = α^V` with `V` uniform on `(0,1)`, whose law on `[α, 1]` has the density
  `1/(q ln(1/α))` of line 5 when `0 < α < 1`; when `α = 1` the density is undefined, `Q = 1`, and
  that branch has probability `1 - γ = 0`.
* `alg2` is Algorithm 2: `A_0 = A`, `A_{j+1}` = Algorithm 1 applied to `A_j`, `α_j` and the
  level-`j` estimator of `Z^(j)`.
-/

/-- The uniform law on `(0,1)`. -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

instance : IsProbabilityMeasure unif01 := ⟨by simp [unif01]⟩

/-- A randomized stopping policy on paths of length `n` with values indexed by `Fin m`. -/
structure Policy (m n : ℕ) where
  /-- The space of internal randomness. -/
  Seed : Type
  /-- Its σ-algebra. -/
  [ms : MeasurableSpace Seed]
  /-- The law of the internal randomness. -/
  law : Measure Seed
  /-- It is a probability measure. -/
  [isProb : IsProbabilityMeasure law]
  /-- The (0-based) time at which the policy selects; `≥ n` means it never selects. -/
  stop : Seed → (Fin n → Fin m) → ℕ

attribute [instance] Policy.ms Policy.isProb

/-- An estimator of a process: a seed law and the estimate `est e t ω = L_t(h_t)`. -/
structure Estimator (m n : ℕ) where
  /-- The space of one seed. -/
  Seed : Type
  /-- Its σ-algebra. -/
  [ms : MeasurableSpace Seed]
  /-- The law of one seed. -/
  law : Measure Seed
  /-- It is a probability measure. -/
  [isProb : IsProbabilityMeasure law]
  /-- The estimate at history length `t` of the path `ω` with seed `e`. -/
  est : Seed → ℕ → (Fin n → Fin m) → ℝ

attribute [instance] Estimator.ms Estimator.isProb

namespace Instance

variable {K m n : ℕ} (I : Instance K m n)

/-- An online policy: measurable in its randomness, and for every seed the decision to stop at
time `s < n` depends only on the history `h_{s+1}`. -/
def PolicyValid (A : Policy m n) : Prop :=
  (∀ ω, Measurable fun u => A.stop u ω) ∧
    ∀ u ω ω' (s : ℕ), s < n → A.stop u ω = s → I.Agree (s + 1) ω ω' → A.stop u ω' = s

/-- The expected reward `r(A) = E[X_τ]` over the world, the path and the internal randomness;
never selecting earns `0`. -/
noncomputable def reward (A : Policy m n) : ℝ :=
  ∫ u, ∑ ω, I.prob ω * I.payoff (A.stop u ω) ω ∂A.law

/-- `A` is `α`-competitive against the Doob martingale `Z_t = E[M | F_t]`:
`r(A) ≥ α · E[Z_1]` (p. 10). -/
def Competitive (A : Policy m n) (α : ℝ) (M : (Fin n → Fin m) → ℝ) : Prop :=
  α * I.expect (I.doob M 1) ≤ I.reward A

/-- The guarantee of Algorithm 1 line 8 with accuracy `β` (Step 3 of Lemma 5, p. 22): the
estimator is measurable in its seed, depends on the path only through `h_t`, and at every
reachable history `h_t`, `t ∈ [n]`, `L_t(h_t)/Z_t(h_t) ∈ [1 - β, 1]` with probability at least
`1 - β/n`. -/
def EstimatorGuarantee (E : Estimator m n) (Z : ℕ → (Fin n → Fin m) → ℝ) (β : ℝ) : Prop :=
  (∀ t ω, Measurable fun e => E.est e t ω) ∧
    (∀ e t ω ω', I.Agree t ω ω' → E.est e t ω = E.est e t ω') ∧
    ∀ t, 1 ≤ t → t ≤ n → ∀ ω, 0 < I.cylProb t ω →
      1 - β / n ≤ E.law.real {e | (1 - β) * Z t ω ≤ E.est e t ω ∧ E.est e t ω ≤ Z t ω}

open Classical in
/-- The stopping time of `A_thr` (Algorithm 1, lines 6–9): the first (0-based) time `s` with
`X_s ≥ Q · L_{s+1}(h_{s+1})`, the estimate drawn with the seed `seeds s`; `n` if there is none. -/
noncomputable def thresholdStop (E : Estimator m n) (Q : ℝ) (seeds : Fin n → E.Seed)
    (ω : Fin n → Fin m) : ℕ :=
  if h : ∃ k, ∃ hk : k < n, Q * E.est (seeds ⟨k, hk⟩) (k + 1) ω ≤ I.X ⟨k, hk⟩ ω then
    Nat.find h
  else n

/-- Algorithm 1 (primal improvement, p. 12) applied to `A`, `α` and the estimator `E`:
with probability `γ = 1/(1 + ln(1/α))` run `A`; otherwise run `A_thr` with the cutoff `Q = α^V`,
`V ~ Uniform(0,1)` (density `1/(q ln(1/α))` on `[α,1]`), and fresh independent seeds for the
`n` estimates. -/
noncomputable def primalImprove (A : Policy m n) (α : ℝ) (E : Estimator m n) : Policy m n where
  Seed := ℝ × ℝ × (Fin n → E.Seed) × A.Seed
  law := unif01.prod (unif01.prod ((Measure.pi fun _ : Fin n => E.law).prod A.law))
  stop := fun u ω =>
    if u.1 < 1 / (1 + Real.log (1 / α)) then A.stop u.2.2.2 ω
    else I.thresholdStop E (α ^ u.2.1) u.2.2.1 ω

/-- Algorithm 2 (p. 15): `A_0 = A` and `A_{j+1}` is Algorithm 1 applied to `A_j`, `α_j` and the
level-`j` estimator `E j` (of `Z^(j)`). -/
noncomputable def alg2 (A : Policy m n) (α₀ : ℝ) (E : ℕ → Estimator m n) : ℕ → Policy m n
  | 0 => A
  | j + 1 => I.primalImprove (alg2 A α₀ E j) (alphaSeq α₀ j) (E j)

end Instance

/-- A finite probability computation, represented by its outcomes and their weights.
Repeated outcomes are allowed; their weights add. This is a specification, not a machine
instruction or a claimed efficient enumeration. -/
abbrev FiniteLaw (α : Type) := List (α × ℝ)

/-- Independent continuation of a finite probability computation. -/
noncomputable def lawBind {α β : Type} (xs : FiniteLaw α) (f : α → FiniteLaw β) :
    FiniteLaw β :=
  xs.flatMap fun x => (f x.1).map fun y => (y.1, x.2 * y.2)

/-- Apply a deterministic function to the outcomes. -/
def lawMap {α β : Type} (f : α → β) (xs : FiniteLaw α) : FiniteLaw β :=
  xs.map fun x => (f x.1, x.2)

/-- Draw independently once from each of a finite list of laws, preserving order. -/
noncomputable def lawSequence {α : Type} : List (FiniteLaw α) → FiniteLaw (List α)
  | [] => [([], 1)]
  | xs :: rest => lawBind xs fun x => lawMap (x :: ·) (lawSequence rest)

/-- The real-output measure of a finite probability computation. -/
noncomputable def lawMeasure (xs : FiniteLaw ℝ) : Measure ℝ :=
  (xs.map fun x => ENNReal.ofReal x.2 • Measure.dirac x.1).sum

namespace Instance

variable {K m n : ℕ} (I : Instance K m n)

/-- One completed trajectory drawn from the biased conditional law of (10).
Index representatives with identical values are combined by any subsequent value-only
computation. At a null history all weights are zero; no accuracy assertion uses that case. -/
noncomputable def biasedLaw (t : ℕ) (ω : Fin n → Fin m) : FiniteLaw (Fin n → Fin m) :=
  Finset.univ.toList.map fun ω' => (ω', I.biasedProb t ω ω')

/-- The complete output law of Algorithm 3 (p. 20), not an arbitrary accurate estimator.
At level zero return 1. At level j+1 use the printed cube-root accuracy, ceiling sample
count and failure allocation. For every time draw independent biased continuations, recurse
with fresh randomness and average; then take the maximum ratio and multiply by the result
of the independent recursive call on the original path (lines 15–16).
The finite weighted tree specifies the law only: Claim 3 separately requires an efficient
machine realization. In particular this definition supplies no free computational instruction. -/
noncomputable def algorithm3Law (α₀ : ℝ) :
    ℕ → (Fin n → Fin m) → ℝ → ℝ → FiniteLaw ℝ
  | 0, _, _, _ => [(1, 1)]
  | j + 1, ω, η, κ =>
      let η' := 1 - (1 - η) ^ ((1 : ℝ) / 3)
      let r := ⌈3 / (η' ^ 2 * Gprod α₀ (j + 1)) * Real.log (4 * n / κ)⌉₊
      let κ' := κ / (2 * ((n : ℝ) * r + 1))
      let estimates := (List.finRange n).map fun t =>
        let one := lawBind (I.biasedLaw (t.val + 1) ω) fun ω' =>
          algorithm3Law α₀ j ω' η' κ'
        lawMap (fun ws : List ℝ => I.Zseq α₀ 0 (t.val + 1) ω * (ws.sum / r))
          (lawSequence (List.replicate r one))
      lawBind (lawSequence estimates) fun zs =>
        let ρhat := ((List.ofFn fun t : Fin n => I.X t ω).zipWith (· / ·) zs).foldl max 0
        lawMap (fun w => w * max (alphaSeq α₀ j) ρhat)
          (algorithm3Law α₀ j ω η' κ')

end Instance

end BayesOptStop.Scheme


