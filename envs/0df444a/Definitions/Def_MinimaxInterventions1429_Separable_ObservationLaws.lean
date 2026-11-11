-- Prove2me | Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
-- name    : MinimaxInterventions1429_Separable_ObservationLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:08.952871+00:00
-- url     : https://prove2.me/theorems/ca3daf31-ea77-4d23-827d-3ec85f465882
-- title:
--   Numerical response observations, randomized laws, synopsis decoding and privacy
-- statement:
--   For numerical-response lower bounds, a learner is a function of a private random seed and a complete response map $B\mapsto p(B)\in\Delta_k$, with an arbitrary real-table output or a failure symbol. This grants at least the observations available to any adaptive procedure with any number of calls. Common response maps and exact bit kernels are measurable under the standard Borel array and mixture sigma-algebras. The common response map is chosen without knowing the learner's seed and is identical on the indistinguishable inputs. Random-seed spaces and their probability laws are unrestricted.
--
--   For a returned table $\widehat L$, success at radius $r$ means $d_q(\widehat L,L)\le r$, strict success uses $<r$, and error at least $r$ means $d_q(\widehat L,L)\ge r$. Failure counts as unsuccessful in each case. A pure mixture is a simplex vertex. Thresholding a numerical response uses bit $1$ when its requested coordinate is at least $1/2$.
--
--   A synopsis has a public deterministic decoder $\operatorname{Dec}(s,B)$. Simultaneous accuracy is the event
--
--   $$\forall B\in\mathcal S,\quad \operatorname{Dec}(s,B)\text{ is }\alpha\text{-optimal for }L+B.$$
--
--   The module defines the actual reconstruction run on these decoded bits. For a private interactive transcript it defines public replay from the recorded bits, verifies that replay produces the recorded queries, and extracts the reconstructed output. The released output retains either the reconstructed real table or the failure symbol. The accuracy guarantees separately require a returned table in the high-interaction regime.
--
--   For any database domain with adjacency $\sim$, a mechanism is $(\varepsilon,\delta)$-differentially private when $\Pr[M(d)\in E]\le e^\varepsilon\Pr[M(d')\in E]+\delta$ for every $d\sim d'$ and every measurable $E$. Privacy is imposed on the full domain. The sigma-algebra on optional tables is the Borel disjoint union of a failure point and real tables; finite histories have the standard sigma-algebra obtained from their length and finite coordinate sequences. These definitions contain no success probability or privacy preservation assumption.
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Section 2, response/bit oracles, reusable synopses and privacy, printed pp.8–9 (PDF pp.10–11); Section 3.2 and Theorem 3.5, printed pp.11–12 (PDF pp.13–14); Section 4, printed pp.14–15 (PDF pp.16–17)

import Definitions.Def_MinimaxInterventions1429_Separable_Algorithm
set_option autoImplicit false

noncomputable section

namespace MinimaxInterventions1429.Separable

/-- The usual disjoint-union sigma-algebra: one failure point and a Borel real table. -/
instance tableOptionMeasurableSpace (m k : ℕ) : MeasurableSpace (Option (Table m k)) :=
  MeasurableSpace.comap (fun o => match o with
    | none => (Sum.inl () : Unit ⊕ Table m k)
    | some M => Sum.inr M) inferInstance

/-- Borel surcharge coordinates and the discrete requested action. -/
instance queryMeasurableSpace (m k : ℕ) : MeasurableSpace (Query m k) :=
  MeasurableSpace.comap (fun q => (q.surcharge, q.coordinate.val)) inferInstance

/-- Finite transcripts encoded by their length and padded table/coordinate/bit sequence. -/
instance historyMeasurableSpace (m k : ℕ) : MeasurableSpace (History m k) :=
  MeasurableSpace.comap (fun hist => (hist.length, fun i : ℕ => match hist[i]? with
    | none => ((0, 0, 0) : Table m k × ℕ × ℕ)
    | some (q, v) => (q.surcharge, q.coordinate.val, if v then 1 else 0))) inferInstance

/-- An everywhere exact bit kernel, with Section 2's joint measurability convention. -/
def ExactOracle {m k : ℕ} (L : Table m k) (O : BitOracle m k) : Prop :=
  Measurable (Function.uncurry O) ∧ ∀ hist q, LegalBit L 0 q (O hist q)

/-- A learner granted the entire numerical response map. This includes any measurable
observable-history procedure, even with no finite bound on its number of queries. -/
abbrev FullLearner (Ω : Type*) (m k : ℕ) :=
  Ω → (Table m k → Mixture k) → Option (Table m k)

def Within {m k : ℕ} (L : Table m k) (r : ℝ) (out : Option (Table m k)) : Prop :=
  ∃ M, out = some M ∧ quotientDist M L ≤ r

def StrictlyWithin {m k : ℕ} (L : Table m k) (r : ℝ) (out : Option (Table m k)) : Prop :=
  ∃ M, out = some M ∧ quotientDist M L < r

/-- A failure symbol counts as failure at every radius, including radius zero. -/
def ErrorAtLeast {m k : ℕ} (L : Table m k) (r : ℝ) (out : Option (Table m k)) : Prop :=
  out = none ∨ ∃ M, out = some M ∧ r ≤ quotientDist M L

def Pure {k : ℕ} (p : Mixture k) : Prop :=
  ∃ h : Fin k, ∀ j, p.val j = if j = h then 1 else 0

/-- From a complete response map, take the advertised weak-threshold bit. -/
def thresholdOracle {m k : ℕ} (p : Table m k → Mixture k) : BitOracle m k :=
  fun _ q => decide ((1 : ℝ) / 2 ≤ (p q.surcharge).val q.coordinate)

def synopsisRun {m k : ℕ} [NeZero m] [NeZero k] {S : Type*}
    (Dec : S → Table m k → Mixture k) (α : ℝ) (T : ℕ) (s : S) :=
  (reconstruction m k α T).run (thresholdOracle (Dec s)) []

def synopsisOutput {m k : ℕ} [NeZero m] [NeZero k] {S : Type*}
    (Dec : S → Table m k → Mixture k) (α : ℝ) (T : ℕ) (s : S) : Option (Table m k) :=
  (synopsisRun Dec α T s).1.map Prod.snd

def SimultaneouslyAccurate {m k : ℕ} {S : Type*}
    (Dec : S → Table m k → Mixture k) (L : Table m k) (α : ℝ) (s : S) : Prop :=
  ∀ B, Allowed B → Optimal (L + B) α (Dec s B)

/-- Reconstruct only from the recorded bits, re-computing every public query. -/
def replay {m k : ℕ} [NeZero m] [NeZero k] (α : ℝ) (T : ℕ) (hist : History m k) :=
  (reconstruction m k α T).run
    (fun past _ => ((hist[past.length]?).map Prod.snd).getD false) []

def IsTranscript {m k : ℕ} [NeZero m] [NeZero k] (α : ℝ) (T : ℕ) (hist : History m k) : Prop :=
  (replay α T hist).2 = hist

def transcriptOutput {m k : ℕ} [NeZero m] [NeZero k]
    (α : ℝ) (T : ℕ) (hist : History m k) : Option (Table m k) :=
  (replay α T hist).1.map Prod.snd

/-- Event form of differential privacy on the entire specified database domain. -/
def DifferentiallyPrivate {D S : Type*} [MeasurableSpace S]
    (adj : D → D → Prop) (ε δ : ℝ) (mechanism : D → MeasureTheory.Measure S) : Prop :=
  ∀ d d', adj d d' → ∀ E, MeasurableSet E →
    mechanism d E ≤ ENNReal.ofReal (Real.exp ε) * mechanism d' E + ENNReal.ofReal δ

end MinimaxInterventions1429.Separable


