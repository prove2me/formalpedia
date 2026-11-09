-- Prove2me | Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws
-- name    : RecoveryStorage3SUM_Adaptive_Laws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:57.703902+00:00
-- url     : https://prove2.me/theorems/20f82d3e-b857-46f6-ba7f-d7bb60b0eff5
-- title:
--   The randomness of the preprocessing: sample, prime, balanced partitions, load check, accepted runs
-- statement:
--   All choices of Algorithm 1 other than the coins of the inverters are uniform on finite sets, so probabilities are ratios of cardinalities.
--
--   1. $R$ is uniform among subsets of $A$ of size $|R|$.
--   2. A **fresh attempt** is an independent uniform prime in $[P,2P)$, where $P=\lceil n^{2-\delta}\log^3 n\rceil$, and $K$ independent uniform **balanced partitions** of $A$ into $L$ labelled parts. Balanced means each part has size $\lfloor n/L\rfloor$ or $\lceil n/L\rceil$.
--   3. The **load check** requires $\sum_{i,r}(d_{i,r}^{(k)})^2\le 2n^2\log^2 n$ for every $k$.
--   4. Conditional on being accepted, an attempt of the rejection loop is uniform on the attempts passing the check. The law of $J$ **accepted runs** is the product of $J$ copies of this law, given $R$.
--   5. An **inverter law** is any probability space with answer functions indexed by the structures, such that each is a correct inverter for its self-map except with probability at most $\eta$. No independence between structures is required. The machine of Lemma 2.3 is an instance.
--
--   **Formalization Note** The prime sampler uses $[P,2P)$ for the integer $P=\lceil n^{2-\delta}\log^3n\rceil$; its upper endpoint is twice the rounded lower endpoint. Uniform ratios return zero on empty support and describe probability laws only on nonempty support. In the standing large-$n$ regime, the sample support is nonempty by the cap, prime support by Bertrand's postulate, and balanced-partition support by $L\ge1$. Nonemptiness of the accepted supports and their target-conditioned restrictions also requires the load and class-size estimates; prime existence alone does not supply it. These facts must be established from the definitions and standing assumptions, not assumed as successful preprocessing.
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Section 3, p.6; Section 3.1 and Algorithm 1, p.7; Section 5.2, p.14

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Construction
import Definitions.Def_RecoveryStorage3SUM_Adaptive_OracleMachine

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MeasureTheory

/-!
# The randomness of the preprocessing: Algorithm 1

Carmel, Kosoburd, Krauthgamer, STOC 2027 submission #561, §3, p.6: "run j draws its own uniformly
random prime pj ∈ [n^{2-δ} log³ n, 2 n^{2-δ} log³ n) and its own random partitions of A"; §3.1, p.7:
"The set A is randomly partitioned into L equal sized sets, this is repeated K = Θ(log n) times
independently"; "If the check fails for any k, redraw the run (prime and partitions)."

**Formalization Note.** All choices but the FN coins are uniform on a finite set, so a probability
is a ratio of cardinalities (`unifProb`). Rejection sampling makes the law of an accepted attempt the
uniform law on the attempts passing the load check (`passingAttempts`), and accepted runs are
independent given `R`; this is `acceptedRuns`. Exhausting the `log n` attempts is the separate failure of
line 7 of Algorithm 1. FN coins are modelled by any probability space on which each inverter is
correct except with probability `η` (`InverterLaw`); no independence between inverters is required,
and the machine of Lemma 2.3 is an instance.
-/

open Classical in
/-- The probability of `E` when drawing uniformly from `S`. It is `0` if `S` is empty; each `S` used
below is nonempty once `n` is large. -/
noncomputable def unifProb {α : Type*} (S : Finset α) (E : α → Prop) : ℝ :=
  ((S.filter E).card : ℝ) / (S.card : ℝ)

/-- The expectation of `f` when drawing uniformly from `S`. -/
noncomputable def unifAvg {α : Type*} (S : Finset α) (f : α → ℝ) : ℝ :=
  (∑ x ∈ S, f x) / (S.card : ℝ)

/-- The law of `R`: all subsets of `A` of size `|R|`. -/
noncomputable def sampleSpace (A : Finset ℤ) (δ : ℝ) : Finset (Finset ℤ) :=
  A.powersetCard (sampleSize A.card δ)

/-- The primes in `[⌈n^{2-δ} log³ n⌉, 2⌈n^{2-δ} log³ n⌉)`. -/
noncomputable def primeSpace (n : ℕ) (δ : ℝ) : Finset ℕ :=
  (Finset.Ico (primeLow n δ) (2 * primeLow n δ)).filter Nat.Prime

/-- A balanced partition of `A` into `L` labelled parts: every part has size `⌊|A|/L⌋` or `⌈|A|/L⌉`,
which is "equal sized" when `L` divides `|A|`. -/
def IsBalanced {A : Finset ℤ} {L : ℕ} (π : A → Fin L) : Prop :=
  ∀ i : Fin L, A.card / L ≤ (part π i).card ∧ (part π i).card ≤ (A.card + L - 1) / L

open Classical in
/-- All balanced partitions of `A` into `L` parts. -/
noncomputable def balancedSpace (A : Finset ℤ) (L : ℕ) : Finset (A → Fin L) :=
  Finset.univ.filter IsBalanced

open Classical in
/-- A fresh draw of `K` independent balanced partitions. -/
noncomputable def partitionsSpace (A : Finset ℤ) (K L : ℕ) : Finset (Fin K → A → Fin L) :=
  Fintype.piFinset fun _ => balancedSpace A L

open Classical in
/-- A fresh attempt: an independent uniform prime and `K` balanced partitions. `n = |A|`. -/
noncomputable def attemptSpace (A : Finset ℤ) (δ : ℝ) (K L : ℕ) : Finset (ℕ × (Fin K → A → Fin L)) :=
  primeSpace A.card δ ×ˢ partitionsSpace A K L

/-- The attempt as a run. -/
def toRun {A : Finset ℤ} {K L : ℕ} (x : ℕ × (Fin K → A → Fin L)) : Attempt A K L := ⟨x.1, x.2⟩

/-- The load check: `∑_{i,r} (d_{i,r}^{(k)})² ≤ 2 n² log² n` for every partition `k`. -/
def LoadCheck {A : Finset ℤ} {K L : ℕ} (B R : Finset ℤ) (x : ℕ × (Fin K → A → Fin L)) : Prop :=
  ∀ k : Fin K, (squaredLoad B R x.1 (x.2 k) : ℝ) ≤ 2 * (A.card : ℝ) ^ 2 * Real.log A.card ^ 2

open Classical in
/-- The law of an accepted attempt. -/
noncomputable def passingAttempts (A B R : Finset ℤ) (δ : ℝ) (K L : ℕ) :
    Finset (ℕ × (Fin K → A → Fin L)) :=
  (attemptSpace A δ K L).filter (LoadCheck B R)

open Classical in
/-- The law of `J` accepted runs, independent given `R`. -/
noncomputable def acceptedRuns (A B R : Finset ℤ) (δ : ℝ) (J K L : ℕ) :
    Finset (Fin J → ℕ × (Fin K → A → Fin L)) :=
  Fintype.piFinset fun _ => passingAttempts A B R δ K L

/-- A randomized family of inverters: `build ι N f ω` is the answer function of the structure with
index `ι` built for `f` on `[N]` from the coins `ω`, and for every self-map it is correct on every
query except with probability at most `η`. -/
def InverterLaw {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (build : ι → ℕ → (ℕ → ℕ) → Ω → ℕ → Option ℕ) (η : ℝ) : Prop :=
  ∀ (x : ι) (N : ℕ) (f : ℕ → ℕ), IsSelfMap N f →
    μ {ω | ¬ CorrectInverter N f (build x N f ω)} ≤ ENNReal.ofReal η

/-- The answer functions of the `KL` structures of a run with prime `p`, for the coins `ω`: the
structure of `(k, i)` inverts `G_i^{(k)}` on `[2p]`. -/
noncomputable def runInverters {Ω : Type*} {A : Finset ℤ} {K L : ℕ} (B R : Finset ℤ)
    (build : Fin K × Fin L → ℕ → (ℕ → ℕ) → Ω → ℕ → Option ℕ) (run : Attempt A K L) (ω : Ω) :
    Fin K → Fin L → ℕ → Option ℕ :=
  fun k i => build (k, i) (2 * run.p) (paddedMap (part (run.π k) i) B R run.p) ω

end RecoveryStorage3SUM.Adaptive


