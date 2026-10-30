-- Prove2me | Definitions.Def_BitcoinBackboneProb
-- name    : BitcoinBackboneProb
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-30T00:11:30.278917+00:00
-- url     : https://prove2.me/theorems/035b55a7-cab9-41b4-994f-e04ef2b592ac
-- title:
--   The random mining process of the synchronous backbone model, and typicality on a horizon
-- statement:
--   The probabilistic layer under the backbone mission's `BitcoinBackbone`, over Mathlib's measure theory.
--
--   **`ber p`** — the Bernoulli($p$) measure on `Bool`. **`Round n t`** — one round's outcomes: one success bit per honest party ($n$ of them) and per adversarial query ($t$ of them); **`roundMeasure n t p`** — the product of independent Bernoulli($p$) bits. **`Trace n t`** — a sequence of rounds; **`P n t p`** — the product measure over all rounds (`Measure.infinitePi`).
--
--   **`honestCount`**, **`advCount`** — the numbers of successful honest parties and adversarial queries in a round; **`roundX`** ($1$ iff some honest success), **`roundY`** ($1$ iff exactly one honest success), **`roundW`** ($Z - Y$); **`X ω r`**, **`Y ω r`**, **`Z ω r`**, **`W ω r`** — the same for round $r$ of a trace. **`margin n t p`** $= n p (1-p)^{n-1} - t p$ ($E[Y] - E[Z]$); **`rate n t p`** $= \text{margin}^2 / (2 (t+1)^2)$.
--
--   **`TypicalOn ω lam L`** — the backbone mission's typicality inequality $\sum_{[a,b]} Z < \sum_{(a,b)} Y$ for every window with $a + \lambda \le b \le L$. **`toExecution ω L base advParent`** — the backbone `Execution` induced by a trace on the horizon $[1, L]$ for any network behaviour `base` and adversarial chain choices `advParent`: honest party $q$ mines in round $r \le L$ iff its bit is set; the adversary finds `Z ω r` blocks; after $L$ the execution is frozen (party 0 mines alone, the adversary finds nothing). **`TypicalTrunc ω lam L`** — the induced execution is typical in the backbone mission's sense.
--
--   **Formalization Note.** Imports Mathlib and the backbone mission. The adversary is modelled by its query count per round; its strategy (which chains it extends, what it delivers) is the arbitrary `advParent`/`base`, quantified universally in the end-to-end theorems.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Mathlib
import Definitions.Def_BitcoinBackbone

/-!
# The Bitcoin backbone protocol: the probabilistic round model

This file sets up the probabilistic model of mining of Garay, Kiayias and Leonardos
(*The Bitcoin Backbone Protocol*, ePrint 2014/765, Section 3 and Definition 9) on top of the
deterministic analysis of `Definitions.Def_BitcoinBackbone`.

* In every round each of the `n` honest parties finds a block independently with probability `p`
  (one proof-of-work query per party and round, as in the paper's `q = 1` flat model), and the
  adversary makes `t` queries each of which succeeds independently with probability `p`.
* A round outcome is a pair `(Fin n → Bool) × (Fin t → Bool)` (which honest parties / adversarial
  queries succeeded); its law `roundMeasure n t p` is the product of Bernoulli(`p`) measures, so the
  honest success count is `Binomial(n, p)` and the adversarial count `Z` is `Binomial(t, p)`.
* A trace is a sequence of round outcomes `ℕ → Round n t`; its law `P n t p` is the infinite product
  measure `MeasureTheory.Measure.infinitePi`, so the rounds are independent.
* `X ω r`, `Y ω r`, `Z ω r` are the paper's random variables: successful round, uniquely successful
  round (exactly one honest block), number of adversarial blocks.
* `margin n t p = E[Y] - E[Z] = n p (1-p)^(n-1) - t p` is the honest-majority margin and
  `rate n t p = margin² / (2 (t+1)²)` the exponential rate of the Hoeffding bounds.
* `TypicalOn ω lam L` is the deterministic typicality hypothesis `Execution.Typical` restricted to
  the windows inside the horizon `[0, L]`.
* `toExecution ω L base advParent` turns a trace into a `BitcoinBackbone.Execution` on the horizon
  `[1, L]` (rounds after `L` are frozen: party `0` mines alone and the adversary finds nothing),
  so that the deterministic theorems (chain growth, common prefix, chain quality) apply to it on
  the event `TypicalTrunc ω lam L` that this execution is typical.
-/

namespace BitcoinBackboneProb

/-- The Bernoulli law on `Bool` with success probability `p`. -/
noncomputable def ber (p : unitInterval) : MeasureTheory.Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false p

instance ber_isProbabilityMeasure (p : unitInterval) :
    MeasureTheory.IsProbabilityMeasure (ber p) := by
  unfold ber; infer_instance

/-- The outcome of one round: which of the `n` honest parties found a block, and which of the `t`
adversarial queries succeeded. -/
abbrev Round (n t : ℕ) : Type := (Fin n → Bool) × (Fin t → Bool)

/-- The law of one round: all `n + t` queries succeed independently with probability `p`. -/
noncomputable def roundMeasure (n t : ℕ) (p : unitInterval) : MeasureTheory.Measure (Round n t) :=
  (MeasureTheory.Measure.pi fun _ : Fin n => ber p).prod
    (MeasureTheory.Measure.pi fun _ : Fin t => ber p)

instance roundMeasure_isProbabilityMeasure (n t : ℕ) (p : unitInterval) :
    MeasureTheory.IsProbabilityMeasure (roundMeasure n t p) := by
  unfold roundMeasure; infer_instance

/-- A trace: the outcomes of rounds `0, 1, 2, …`. -/
abbrev Trace (n t : ℕ) : Type := ℕ → Round n t

/-- The law of a trace: rounds are independent, each distributed as `roundMeasure n t p`. -/
noncomputable def P (n t : ℕ) (p : unitInterval) : MeasureTheory.Measure (Trace n t) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ => roundMeasure n t p

instance P_isProbabilityMeasure (n t : ℕ) (p : unitInterval) :
    MeasureTheory.IsProbabilityMeasure (P n t p) := by
  unfold P; infer_instance

/-- The number of honest parties that found a block in a round outcome. -/
def honestCount {n t : ℕ} (ρ : Round n t) : ℕ :=
  (Finset.univ.filter fun i => ρ.1 i = true).card

/-- The number of adversarial blocks found in a round outcome. -/
def advCount {n t : ℕ} (ρ : Round n t) : ℕ :=
  (Finset.univ.filter fun j => ρ.2 j = true).card

/-- Round-level `X`: `1` if some honest party found a block in the round outcome, else `0`. -/
def roundX {n t : ℕ} (ρ : Round n t) : ℕ := if 0 < honestCount ρ then 1 else 0

/-- Round-level `Y`: `1` if exactly one honest party found a block, else `0`. -/
def roundY {n t : ℕ} (ρ : Round n t) : ℕ := if honestCount ρ = 1 then 1 else 0

/-- Round-level `W = Z - Y` as a real number (it lies in `[-1, t]`). -/
def roundW {n t : ℕ} (ρ : Round n t) : ℝ := (advCount ρ : ℝ) - (roundY ρ : ℝ)

/-- The paper's `X_r`: `1` if round `r` is successful (some honest block), else `0`. -/
def X {n t : ℕ} (ω : Trace n t) (r : ℕ) : ℕ := roundX (ω r)

/-- The paper's `Y_r`: `1` if round `r` is uniquely successful (exactly one honest block), else `0`. -/
def Y {n t : ℕ} (ω : Trace n t) (r : ℕ) : ℕ := roundY (ω r)

/-- The paper's `Z_r`: the number of adversarial blocks found in round `r`. -/
def Z {n t : ℕ} (ω : Trace n t) (r : ℕ) : ℕ := advCount (ω r)

/-- The real-valued round variable `W_r = Z_r - Y_r` (in `[-1, t]`), whose window sums decide
typicality. -/
def W {n t : ℕ} (ω : Trace n t) (r : ℕ) : ℝ := roundW (ω r)

/-- The honest-majority margin `E[Y_r] - E[Z_r] = n p (1 - p)^(n-1) - t p`. -/
noncomputable def margin (n t : ℕ) (p : unitInterval) : ℝ :=
  (n : ℝ) * p * (1 - (p : ℝ)) ^ (n - 1) - (t : ℝ) * p

/-- The exponential rate of the window bounds: `margin² / (2 (t + 1)²)`. -/
noncomputable def rate (n t : ℕ) (p : unitInterval) : ℝ :=
  margin n t p ^ 2 / (2 * ((t : ℝ) + 1) ^ 2)

/-- Typicality on the horizon `[0, L]`: the inequality of `BitcoinBackbone.Execution.Typical` for
every window `[a, b]` with `a + lam ≤ b ≤ L`. -/
def TypicalOn {n t : ℕ} (ω : Trace n t) (lam L : ℕ) : Prop :=
  ∀ a b : ℕ, a + lam ≤ b → b ≤ L →
    (∑ i ∈ Finset.Icc a b, Z ω i) < ∑ i ∈ Finset.Ioo a b, Y ω i

/-- The execution of the backbone protocol induced by a trace on the horizon `[1, L]`, for a given
behaviour of the network (`base`) and of the adversary's chain choices (`advParent`).  Honest party
`p < n` mines in round `1 ≤ r ≤ L` iff its query succeeded in the trace; the adversary finds
`Z ω r` blocks in round `r ≤ L`.  After the horizon the execution is frozen: party `0` mines alone
and the adversary finds nothing, so that typicality after the horizon is automatic. -/
def toExecution {n t : ℕ} (ω : Trace n t) (L : ℕ)
    (base advParent : ℕ → ℕ → BitcoinBackbone.Chain) : BitcoinBackbone.Execution where
  n := n
  mined := fun q r =>
    if h : q < n then (if 1 ≤ r ∧ r ≤ L then (ω r).1 ⟨q, h⟩ else decide (L < r ∧ q = 0))
    else false
  Z := fun r => if r ≤ L then Z ω r else 0
  base := base
  advParent := advParent

/-- The induced execution (for any network/adversary behaviour, which does not matter here) is
typical in the sense of `BitcoinBackbone.Execution.Typical`. -/
def TypicalTrunc {n t : ℕ} (ω : Trace n t) (lam L : ℕ) : Prop :=
  (toExecution ω L (fun _ _ => []) (fun _ _ => [])).Typical lam

end BitcoinBackboneProb


