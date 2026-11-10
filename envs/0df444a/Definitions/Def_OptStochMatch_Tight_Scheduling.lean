-- Prove2me | Definitions.Def_OptStochMatch_Tight_Scheduling
-- name    : OptStochMatch_Tight_Scheduling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:57:06.254222+00:00
-- url     : https://prove2.me/theorems/d8c6f47b-39ff-4152-9c75-5517b044d649
-- title:
--   Scheduling with $\mathrm{Exp}(1)$ service demands, nonanticipating policies and the posterior allocation policy (4.1)
-- statement:
--   $m$ jobs with independent $\mathrm{Exp}(1)$ demands; rates $s(t)\in P$ on $[0,1]$; job $i$ completes when $x_i(t)=\int_0^t s_i$ reaches $Z_i$ and then gets rate $0$. A nonanticipating policy depends on the observed history (service provided, identities and times of completions) and an independent seed; it is encoded as a jointly measurable rate map of the seed, the completion history and the time. The process (completion times, work $x(t)$, rates $s(t)$) is computed phase by phase.
--
--   - Expected total work $\mathbb E[\sum_i x_i(1)]$, expected completions $\mathbb E[\sum_i 1\{x_i(1)=Z_i\}]$, $\mathbb E[x_i(1)]$.
--   - Equality in law of the match record of a matching policy and the completion record of a scheduling policy.
--   - A measurable offline allocation $Y$: $Y(z)\in P$, $0\le Y(z)\le z$ on $\mathbb R^m_+$; the rates (4.1) $s_i=\mathbb E[Y_i(\tilde Z)]$ for unfinished $i$ ($\tilde Z_j=x_j$ if completed, $x_j+E_j$ otherwise, $E_j\sim\mathrm{Exp}(1)$), $0$ for completed $i$; a policy following (4.1).
--   - $\mathcal F_t$: the σ-algebra of the observed service and completion history up to $t$.
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), §2.2, pp. 6–7 (PDF 7–8); §2.3, p. 8 (PDF 9); §4, pp. 13–14 (PDF 14–15)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Algorithms

/-!
Dütting, Feldman, Molina, *Optimal Online Stochastic Matching*, arXiv:2610.19866
(sha256 0458ce2e…), §2.2 pp. 6–7 (PDF 7–8), §2.3 p. 8 (PDF 9), §4.1 p. 14 (PDF 15).

**Scheduling with exponential service demands.** `m` jobs with independent demands
`Z_i ∼ Exp(1)`; a scheduler chooses service rates `s(t) ∈ P` on `[0,1]`; job `i` completes when
its accumulated work `x_i(t) = ∫_0^t s_i` reaches `Z_i`, after which its rate is zero. "The
scheduler observes the service provided and the identities and times of completed jobs, but
not the service demands of unfinished jobs. A policy is nonanticipating if its decisions depend
only on this observed history and independent internal randomization."

**Encoding of nonanticipating policies.** Between two completions the observed history only
grows by the elapsed time and the policy's own service, so a nonanticipating policy is a rate
map `rate u h t`: the rate vector at time `t` given the internal seed `u ∼ Uniform[0,1]` and the
completion history `h` (a list of `(completion time, job)`, newest first). Rates lie in `P`,
vanish on completed jobs, and are jointly measurable in the seed, the completion times and `t`.

**The process.** For a seed `u` and demands `z`: the work after history `h` is
`x(t) = x(τ_h) + ∫_{τ_h}^t rate u h v dv` (`τ_h` the latest completion time); the next completion
is the first `t ∈ [τ_h, 1]` at which some unfinished job has `x_i(t) ≥ z_i` (ties, a null event,
are broken by the smallest index, the other job completing at the same instant). There are at
most `m` completions.
-/

namespace OptStochMatch.Tight

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

/-- A nonanticipating online scheduling policy with feasible-rate region `P` (phase form). -/
structure SchedPolicy (m : ℕ) (P : Set (Fin m → ℝ)) where
  rate : ℝ → List (ℝ × Fin m) → ℝ → Fin m → ℝ
  feasible : ∀ u h t, rate u h t ∈ P
  stops : ∀ u h t i, i ∈ h.map Prod.snd → rate u h t i = 0
  measurable_rate : ∀ (j : ℕ) (c : Fin j → Fin m) (i : Fin m),
    Measurable fun p : ℝ × (Fin j → ℝ) × ℝ =>
      rate p.1 (List.ofFn fun r => (p.2.1 r, c r)) p.2.2 i

variable {m : ℕ} {P : Set (Fin m → ℝ)}

/-- Accumulated work at time `t` (for `t` at or after the latest completion in `h`), given the
seed `u` and the completion history `h`. -/
noncomputable def workAt (σ : SchedPolicy m P) (u : ℝ) : List (ℝ × Fin m) → ℝ → Fin m → ℝ
  | [], t => fun i => ∫ v in (0 : ℝ)..t, σ.rate u [] v i
  | (τ, j) :: h, t => fun i =>
      workAt σ u h τ i + ∫ v in τ..t, σ.rate u ((τ, j) :: h) v i

open Classical in
/-- The next completion `(time, job)` after history `h`, if one occurs by time `1`. -/
noncomputable def nextCompletion (σ : SchedPolicy m P) (u : ℝ) (z : Fin m → ℝ)
    (h : List (ℝ × Fin m)) : Option (ℝ × Fin m) :=
  let T : Set ℝ := {t | t ∈ Set.Icc (lastTime h) 1 ∧
    ∃ i, i ∉ h.map Prod.snd ∧ z i ≤ workAt σ u h t i}
  if T.Nonempty then
    let τ := sInf T
    let J := Finset.univ.filter fun i => i ∉ h.map Prod.snd ∧ z i ≤ workAt σ u h τ i
    if hJ : J.Nonempty then some (τ, J.min' hJ) else none
  else none

/-- The completion history after `k` completion steps. -/
noncomputable def schedHist (σ : SchedPolicy m P) (u : ℝ) (z : Fin m → ℝ) : ℕ → List (ℝ × Fin m)
  | 0 => []
  | k + 1 =>
    match nextCompletion σ u z (schedHist σ u z k) with
    | some e => e :: schedHist σ u z k
    | none => schedHist σ u z k

/-- The full completion history on `[0,1]` (at most `m` completions). -/
noncomputable def finalHist (σ : SchedPolicy m P) (u : ℝ) (z : Fin m → ℝ) : List (ℝ × Fin m) :=
  schedHist σ u z m

/-- The completion history observed up to time `t`. -/
noncomputable def histUpTo (σ : SchedPolicy m P) (u : ℝ) (z : Fin m → ℝ) (t : ℝ) :
    List (ℝ × Fin m) :=
  (finalHist σ u z).filter fun e => decide (e.1 ≤ t)

/-- The accumulated work `x(t)`, `0 ≤ t ≤ 1`. -/
noncomputable def workProc (σ : SchedPolicy m P) (u : ℝ) (z : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  workAt σ u (histUpTo σ u z t) t

/-- The service-rate vector `s(t)` in use at time `t`. -/
noncomputable def rateProc (σ : SchedPolicy m P) (u : ℝ) (z : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  σ.rate u (histUpTo σ u z t) t

/-- Expectation over the seed `U ∼ Uniform[0,1]` and independent demands `Z_i ∼ Exp(1)`. -/
noncomputable def schedExpect (F : ℝ → (Fin m → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ u, ∫⁻ z, F u z ∂(demandLaw m) ∂seedLaw

/-- Expected total work processed by the deadline, `E[∑_i x_i(1)]`. -/
noncomputable def expTotalWork (σ : SchedPolicy m P) : ℝ≥0∞ :=
  schedExpect fun u z => ENNReal.ofReal (∑ i, workProc σ u z 1 i)

/-- Expected number of completed jobs, `E[∑_i 1{x_i(1) = Z_i}]`. -/
noncomputable def expCompletions (σ : SchedPolicy m P) : ℝ≥0∞ :=
  schedExpect fun u z => ∑ i, if workProc σ u z 1 i = z i then (1 : ℝ≥0∞) else 0

/-- Expected work processed for job `i` by the deadline, `E[x_i(1)]`. -/
noncomputable def expWorkJob (σ : SchedPolicy m P) (i : Fin m) : ℝ≥0∞ :=
  schedExpect fun u z => ENNReal.ofReal (workProc σ u z 1 i)

/-! ### Laws of the match and completion processes -/

/-- A record (list, newest first) of length `j`, read as a vector indexed by `Fin j`, lies in
`B`. -/
def recordIn {j : ℕ} (rec : List (ℝ × Fin m)) (B : Set (Fin j → ℝ × Fin m)) : Prop :=
  ∃ hl : rec.length = j, (fun r : Fin j => rec.get (r.cast hl.symm)) ∈ B

open Classical in
/-- `P(the completion record has exactly j entries and lies in B)`. -/
noncomputable def schedRecordProb (σ : SchedPolicy m P) (j : ℕ) (B : Set (Fin j → ℝ × Fin m)) :
    ℝ≥0∞ :=
  schedExpect fun u z => if recordIn (finalHist σ u z) B then 1 else 0

open Classical in
/-- `P(the match record (time, vertex) has exactly j entries and lies in B)`, Poisson model. -/
noncomputable def matchRecordProb (lam : Ty m → ℝ≥0) (π : PoissonPolicy m) (j : ℕ)
    (B : Set (Fin j → ℝ × Fin m)) : ℝ≥0∞ :=
  ∫⁻ u, poissonExpect lam (fun n t s => if recordIn (poissonRun π u t s n) B then 1 else 0)
    ∂seedLaw

/-- The process of matched vertices of `π` (with match times) and the process of completed
jobs of `σ` (with completion times) have the same law: the records of `(time, identity)`
pairs have the same law. -/
def SameRecordLaw (lam : Ty m → ℝ≥0) (π : PoissonPolicy m) (σ : SchedPolicy m P) : Prop :=
  ∀ (j : ℕ) (B : Set (Fin j → ℝ × Fin m)), MeasurableSet B →
    matchRecordProb lam π j B = schedRecordProb σ j B

/-! ### The posterior allocation policy (4.1) -/

/-- A measurable offline allocation (§4, p. 13, PDF 14): `Y(z) ∈ P` and `0 ≤ Y(z) ≤ z` for every
`z ∈ ℝ^m_+`. -/
def IsOfflineAllocation (P : Set (Fin m → ℝ)) (Y : (Fin m → ℝ) → (Fin m → ℝ)) : Prop :=
  Measurable Y ∧ ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) → Y z ∈ P ∧ ∀ i, 0 ≤ Y z i ∧ Y z i ≤ z i

/-- The rates (4.1) at work `x` with completed set `C`: `s_i = E[Y_i(Z̃)]` for unfinished `i`,
where `Z̃_j = x_j` for completed `j` and `Z̃_j = x_j + E_j` for unfinished `j`, with independent
`E_j ∼ Exp(1)`; `s_i = 0` for completed `i`. -/
noncomputable def postRate (Y : (Fin m → ℝ) → (Fin m → ℝ)) (x : Fin m → ℝ) (C : Finset (Fin m)) :
    Fin m → ℝ :=
  fun i => if i ∈ C then 0 else
    ∫ e, Y (fun j => if j ∈ C then x j else x j + e j) i ∂(demandLaw m)

/-- `σ` is the posterior allocation policy (4.1) for `Y`: at every time `t ∈ [τ_h, 1]` after
every completion history `h` (whenever the current work is nonnegative), its rate is the rate
(4.1) at the current work and completed set. -/
def FollowsPosterior (Y : (Fin m → ℝ) → (Fin m → ℝ)) (σ : SchedPolicy m P) : Prop :=
  ∀ (u : ℝ) (h : List (ℝ × Fin m)) (t : ℝ), t ∈ Set.Icc (lastTime h) 1 →
    (∀ i, 0 ≤ workAt σ u h t i) → σ.rate u h t = postRate Y (workAt σ u h t) (matchedSet h)

/-- The observed service and completion history up to time `t` (for the seed `u`) as a
σ-algebra on the demand space: generated by `x_i(v)` and `1{job i completed by v}` for
`0 ≤ v ≤ t`, `i ∈ [m]`. -/
noncomputable def obsAlgebra (σ : SchedPolicy m P) (u : ℝ) (t : ℝ) : MeasurableSpace (Fin m → ℝ) :=
  ⨆ (v : ℝ) (_ : v ∈ Set.Icc (0 : ℝ) t) (i : Fin m),
    MeasurableSpace.comap
      (fun z => (workProc σ u z v i, if i ∈ matchedSet (histUpTo σ u z v) then (1 : ℝ) else 0))
      inferInstance

end OptStochMatch.Tight


