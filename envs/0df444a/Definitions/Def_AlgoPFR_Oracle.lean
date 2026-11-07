-- Prove2me | Definitions.Def_AlgoPFR_Oracle
-- name    : AlgoPFR_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:49.824239+00:00
-- url     : https://prove2.me/theorems/171ac182-c935-4385-945b-5a1e32288cf1
-- title:
--   Algorithmic access: sampler, density coin, envelope, slack; procedures with call counters; loops
-- statement:
--   **Algorithmic access** to a law $p_X$ is a pair of procedures: a sampler $\mathrm{Sample}_X$ with output law $p_X$, and a density coin $\mathrm{Coin}_X$ which on input $x$ is Bernoulli with parameter
--   $$r_X(x)=\frac{p_X(x)}{M_X},\qquad M_X\ge\|p_X\|_\infty.$$
--   The number $M_X$ is the **envelope**: it belongs to the implementation, not to the law, and procedures never read it. The **slack** is
--   $$\Delta[X]=H[X]+\log M_X.$$
--   The **root access** to $U_A$ is the uniform sampler together with the membership oracle, with envelope $1/|A|$ and slack $0$.
--
--   Protocols are written as probabilistic procedures with a counter of parent calls. A **loop** reruns a trial independently until the first success; it is given by its joint law of output and number of failed trials, and its expected number of trials is an expectation under that law.
--
--   This layer is what lets the mission treat a law of exponentially large support as an object: it is only ever sampled and tested.
--
--   **Formalization Note** The sampler and the coin are represented by their output laws. Definition 4.1's clause "expected time $\mathrm{poly}(n,K)$" is not part of `IsAccess`: by Lemma 4.5 of the source a fiber sampler needs $M_Y/p_Z(z)$ trials in expectation, which is not polynomially bounded for every label. Call counts are stated separately, and time is stated only for machine programs. A loop whose trial never succeeds diverges, and returns a junk point; statements exclude that case.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Definition 4.1, p.18; Eq. (9), p.18

import Mathlib
import Definitions.Def_AlgoPFR_rd

set_option autoImplicit false

open scoped ENNReal

namespace AlgoPFR

noncomputable section

/-- A pair of black-box procedures `(Sample_X, Coin_X)`, represented by their output laws: the law
of one call to the sampler and, for each input `x`, the law of one call to the coin. Repeated
calls are independent. -/
structure Oracle (n : ℕ) where
  /-- The law of one call to `Sample_X`. -/
  sample : PMF (Vec n)
  /-- The law of one call to `Coin_X` on the input `x`. -/
  coin : Vec n → PMF Bool

/-- **Algorithmic access** (Definition 4.1, p.18 of arXiv:2609.20771, sha256 60e45066…): the coin on
input `x` is a Bernoulli variable with parameter `r_X(x) = p_X(x) / M_X`, where `M_X ≥ ‖p_X‖∞` is the
envelope.

**Formalization Note.** The running-time clause of Definition 4.1 ("expected time poly(n, K)") is
not part of this predicate. By the paper's own Lemma 4.5 a fiber sampler needs `M_Y / p_Z(z)` trials
in expectation, which is not polynomially bounded for every label, so that clause cannot be part of
what the protocols produce. Call counts are stated separately, through `Proc`. The envelope is a
number attached to the implementation and is never read by a procedure ("The numerical value of M_X
need not be known to the algorithm", p.18). -/
structure IsAccess {n : ℕ} (O : Oracle n) (M : ℝ) : Prop where
  /-- `M` dominates the mass function of the sampler. -/
  envelope : ∀ x, (O.sample x).toReal ≤ M
  /-- The coin accepts `x` with probability `p(x) / M`. -/
  coin_true : ∀ x, ((O.coin x) true).toReal = (O.sample x).toReal / M

/-- The **slack** `Δ[X] = H[X] + log M_X`, Eq. (9), p.18 of arXiv:2609.20771 (sha256 60e45066…). -/
def slack {n : ℕ} (O : Oracle n) (M : ℝ) : ℝ :=
  entropy O.sample + Real.logb 2 M

open Classical in
/-- The **root access** of arXiv:2609.20771 (sha256 60e45066…), p.18: the uniform sampler for `A`
implements `Sample_{U_A}` and the membership oracle implements `Coin_{U_A}(x) = 1_A(x)`; the envelope
is `M_{U_A} = 1 / |A|`. -/
def rootOracle {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty) : Oracle n where
  sample := uniformLaw A hA
  coin x := PMF.pure (decide (x ∈ A))

/-- A probabilistic procedure with a counter of the parent calls it has made: run on the counter
`0`, it yields the joint law of (output, number of parent calls). -/
abbrev Proc := StateT ℕ PMF

/-- One call to the parent sampler. -/
def Oracle.callSample {n : ℕ} (O : Oracle n) : Proc (Vec n) := do
  modify (· + 1)
  StateT.lift O.sample

/-- One call to the parent coin on the input `x`. -/
def Oracle.callCoin {n : ℕ} (O : Oracle n) (x : Vec n) : Proc Bool := do
  modify (· + 1)
  StateT.lift (O.coin x)

/-- The output law of a procedure, forgetting its call counter. -/
def Proc.law {α : Type} (p : Proc α) : PMF α :=
  (p.run 0).map Prod.fst

/-- The procedure makes exactly `c` parent calls on every outcome of positive probability. -/
def Proc.UsesCalls {α : Type} (p : Proc α) (c : ℕ) : Prop :=
  ∀ y ∈ (p.run 0).support, y.2 = c

/-- `loopMass t (a, k)` is the probability that, in i.i.d. runs of the trial `t` (`none` is a failed
trial), the first `k` trials fail and trial `k + 1` succeeds with the value `a`. -/
def loopMass {α : Type} (t : PMF (Option α)) (y : α × ℕ) : ℝ≥0∞ :=
  t none ^ y.2 * t (some y.1)

theorem hasSum_loopMass {α : Type} (t : PMF (Option α)) (h : t none ≠ 1) :
    HasSum (loopMass t) 1 := by
  have hne : t none ≠ ⊤ := PMF.apply_ne_top t none
  have hsum : t none + ∑' a, t (some a) = 1 := by
    have h1 := t.tsum_coe
    rw [ENNReal.tsum_eq_add_tsum_ite (none : Option α)] at h1
    have h2 : ∑' a : α, t (some a) = ∑' x : Option α, ite (x = none) 0 (t x) := by
      have hinj := Option.some_injective α
      have := hinj.tsum_eq (f := fun x : Option α => ite (x = none) 0 (t x)) (by
        intro x hx
        cases x with
        | none => simp at hx
        | some a => exact ⟨a, rfl⟩)
      simpa using this
    rw [h2]; convert h1
  have hsome : ∑' a, t (some a) = 1 - t none := by
    rw [← hsum, ENNReal.add_sub_cancel_left hne]
  have hle : t none ≤ 1 := by
    rw [← hsum]; exact le_self_add
  have hpos : 1 - t none ≠ 0 := by
    simpa [tsub_eq_zero_iff_le] using lt_of_le_of_ne hle h
  have htop : (1 : ℝ≥0∞) - t none ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  rw [ENNReal.summable.hasSum_iff]
  calc ∑' y, loopMass t y
      = ∑' (a : α) (k : ℕ), t none ^ k * t (some a) := by
        simpa [loopMass] using ENNReal.tsum_prod (f := fun (a : α) (k : ℕ) => t none ^ k * t (some a))
    _ = ∑' a, (1 - t none)⁻¹ * t (some a) := by
        refine tsum_congr fun a => ?_
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    _ = (1 - t none)⁻¹ * (1 - t none) := by rw [ENNReal.tsum_mul_left, hsome]
    _ = 1 := ENNReal.inv_mul_cancel hpos htop

/-- The law with mass function `loopMass t`, for a trial that can succeed. -/
def loopLaw {α : Type} (t : PMF (Option α)) (h : t none ≠ 1) : PMF (α × ℕ) :=
  ⟨loopMass t, hasSum_loopMass t h⟩

open Classical in
/-- **Repeat until the first success.** `loop t` is the joint law of (the value returned, the number
of failed trials before the successful one) when the trial `t` is rerun independently until it
returns `some a`.

**Formalization Note.** If the trial never succeeds the loop diverges; then the definition returns
the junk point `(default, 0)`. Statements only use `loop` where the trial succeeds with positive
probability. -/
def loop {α : Type} [Inhabited α] (t : PMF (Option α)) : PMF (α × ℕ) :=
  if h : t none = 1 then PMF.pure (default, 0) else loopLaw t h

/-- The expected number of trials of a loop, `E[failed trials + 1]`, in `[0, ∞]`. -/
def expectedTrials {α : Type} [Inhabited α] (t : PMF (Option α)) : ℝ≥0∞ :=
  ∑' y, loop t y * ((y.2 : ℝ≥0∞) + 1)

end

end AlgoPFR


