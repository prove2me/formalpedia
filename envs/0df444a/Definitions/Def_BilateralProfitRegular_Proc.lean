-- Prove2me | Definitions.Def_BilateralProfitRegular_Proc
-- name    : BilateralProfitRegular_Proc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:27.55154+00:00
-- url     : https://prove2.me/theorems/eac96fa0-e512-408d-bbb5-551892d352cc
-- title:
--   Sampling procedures with a random number of Bernoulli queries (factories, calibration, loss observations)
-- statement:
--   A **sampling procedure** draws a seed $\omega$ once. At each step it looks at the list of (query, bit) pairs seen so far and either names the next query $q$ or stops with an output. The answer to a query $q$ is a fresh Bernoulli$(\mathrm{prob}(q))$ bit, independent of the past. For trade bits at a price pair $y$, $\mathrm{prob}(y)=P(y)$. For a Bernoulli factory there is a single query, "flip the coin", with $\mathrm{prob}=p$.
--
--   The procedure defines the following random quantities:
--
--   - the number of rounds, a stopping time in $\mathbb N\cup\{\infty\}$;
--   - the output, which is absent if the procedure never stops;
--   - the query made at each step;
--   - the expected number of rounds and the expected total cost $\mathbb E[\sum_{\text{queries }q}g(q)]$ of a nonnegative cost $g$.
--
--   Static properties (all queries in a set, all outputs in a set, at least one query) hold for every seed and every history.
--
--   These procedures model calibration, the Bernoulli factories of Huber and of Lee et al., and the loss observation (53), all of which read an unbounded, random number of trade bits.
--
--   **Formalization Note** The bits are realized from i.i.d. uniforms $U_0,U_1,\dots$ on $[0,1]$, independent of the seed, as $\mathbb 1\{U_n<\mathrm{prob}(q)\}$. This gives each query a Bernoulli$(\mathrm{prob}(q))$ bit given the past, and the procedure sees only the bits. Expectations of nonnegative quantities are lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), proof of Lemma 6.5, pp.41–43 (PDF 43–45)

import Mathlib

namespace BilateralProfitRegular

open MeasureTheory

/-! # Sampling procedures with a random number of Bernoulli queries

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), §6.3, proof of Lemma 6.5,
pp.41–43 (PDF 43–45): calibration, the Bernoulli factories of Huber [27] and Lee et al. [33], and
the loss observation (53) read an unbounded, random number of fresh Bernoulli bits ("trade bits
at a price", or "coin flips") and stop at a random time.

A procedure has a seed `ω` drawn once from `(Ω, P)` and a step function: given the seed and the
list of (query, bit) pairs seen so far (oldest first), it either names the next query
(`Sum.inl q`) or stops with an output (`Sum.inr a`). The bit returned for a query `q` is a fresh
Bernoulli(`prob q`) bit, independent of everything before.

**Formalization Note.** The fresh bits are realized from an i.i.d. sequence `U₀, U₁, …` of uniform
variables on `[0, 1]` (`unitInterval` with Lebesgue measure), independent of the seed: the
`n`-th query `q` receives the bit `1{U_n < prob q}`, which is Bernoulli(`prob q`) given the past.
For trade bits at a price pair `y`, `prob y = P(y)` is the trade probability, so the law of
everything a procedure observes and outputs is that of the paper's procedure fed with fresh
valuations; the procedure itself sees only bits. The number of rounds is the stopping time in
`ℕ∞` (`⊤` if the procedure never stops); expectations of nonnegative quantities are lower
Lebesgue integrals, so no integrability side condition can make them vanish. The step function
is measurable in the seed for every history. -/

/-- A sampling procedure with query type `Q`, output type `α` and seed space `Ω`. -/
structure Proc (Q α Ω : Type) [MeasurableSpace Q] [MeasurableSpace α] [MeasurableSpace Ω] where
  /-- next query (`Sum.inl`) or stop with an output (`Sum.inr`), given the seed and the past -/
  step : Ω → List (Q × Bool) → Q ⊕ α
  measurable_step : ∀ h, Measurable fun ω => step ω h

namespace Proc

variable {Q α Ω : Type} [MeasurableSpace Q] [MeasurableSpace α] [MeasurableSpace Ω]

/-- The list of (query, bit) pairs after `n` steps, with seed `ω` and uniforms `U`; the bit of the
query made at step `m` is `1{U_m < prob q}`. Once the procedure has stopped the list no longer
changes. -/
noncomputable def hist (pr : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω) (U : ℕ → unitInterval) :
    ℕ → List (Q × Bool)
  | 0 => []
  | n + 1 =>
    match pr.step ω (pr.hist prob ω U n) with
    | Sum.inl q => pr.hist prob ω U n ++ [(q, decide ((U n : ℝ) < prob q))]
    | Sum.inr _ => pr.hist prob ω U n

/-- The procedure has stopped by step `n`. -/
def stopped (pr : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω) (U : ℕ → unitInterval) (n : ℕ) : Prop :=
  (pr.step ω (pr.hist prob ω U n)).isRight = true

/-- The number of queries (trading rounds, coin flips) used: the first step at which the
procedure stops, `⊤` if it never stops. -/
noncomputable def rounds (pr : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω) (U : ℕ → unitInterval) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : pr.stopped prob ω U n), (n : ℕ∞)

/-- The query made at step `n` (`none` once the procedure has stopped). -/
noncomputable def query (pr : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω) (U : ℕ → unitInterval)
    (n : ℕ) : Option Q :=
  (pr.step ω (pr.hist prob ω U n)).getLeft?

open Classical in
/-- The output (`none` if the procedure never stops). -/
noncomputable def out (pr : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω) (U : ℕ → unitInterval) :
    Option α :=
  if h : ∃ n, pr.stopped prob ω U n then
    (pr.step ω (pr.hist prob ω U (Nat.find h))).getRight?
  else none

/-- The law of the i.i.d. uniform sequence `U₀, U₁, …`. -/
noncomputable def coinLaw : Measure (ℕ → unitInterval) :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

/-- The law of (seed, uniforms): `P ⊗ coinLaw`. -/
noncomputable def law (P : Measure Ω) : Measure (Ω × (ℕ → unitInterval)) :=
  P.prod coinLaw

/-- The expected number of queries `E[#rounds]`. -/
noncomputable def expRounds (pr : Proc Q α Ω) (prob : Q → ℝ) (P : Measure Ω) : ENNReal :=
  ∫⁻ x, ((pr.rounds prob x.1 x.2 : ℕ∞) : ENNReal) ∂(law P)

/-- The expected total cost `E[∑_{queries q} g(q)]` of the queries made, for a nonnegative cost
`g` (negative values are counted as `0`). -/
noncomputable def expCost (pr : Proc Q α Ω) (prob : Q → ℝ) (P : Measure Ω) (g : Q → ℝ) :
    ENNReal :=
  ∫⁻ x, ∑' n, ((pr.query prob x.1 x.2 n).map fun q => ENNReal.ofReal (g q)).getD 0 ∂(law P)

/-- Every query the procedure can make lies in `S` (a property of the step function, for every
seed and every history). -/
def QueriesIn (pr : Proc Q α Ω) (S : Set Q) : Prop :=
  ∀ ω h q, pr.step ω h = Sum.inl q → q ∈ S

/-- Every output the procedure can return lies in `S`. -/
def OutputsIn (pr : Proc Q α Ω) (S : Set α) : Prop :=
  ∀ ω h a, pr.step ω h = Sum.inr a → a ∈ S

/-- The procedure makes at least one query: its first step is a query. -/
def QueriesFirst (pr : Proc Q α Ω) : Prop :=
  ∀ ω, (pr.step ω []).isLeft = true

end Proc

end BilateralProfitRegular


