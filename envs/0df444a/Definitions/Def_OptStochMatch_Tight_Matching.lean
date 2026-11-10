-- Prove2me | Definitions.Def_OptStochMatch_Tight_Matching
-- name    : OptStochMatch_Tight_Matching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:54:25.060583+00:00
-- url     : https://prove2.me/theorems/75c5eac4-5b05-4204-a6f3-64b7d8500a78
-- title:
--   Online matching policies, $\mathrm{ALG}$, $\mathrm{OPT}$, $\mathrm{CR}$, $\mathrm{CR}_{\mathrm{iid}}$ and routing rules
-- statement:
--   An online policy rejects each arrival or irrevocably matches it to an unmatched neighbour; it may use the current arrival, all previous arrivals (times and types) and internal randomness independent of the arrivals. It is encoded by a seed $u\sim\mathrm{Uniform}[0,1]$ and a decision map of the seed and the arrivals so far, measurable in the seed and the arrival times; a decision that is not an unmatched neighbour is a rejection.
--
--   - $\mathrm{ALG}$: expected size of the policy's matching; $\mathrm{OPT}=\mathbb E[\mathrm{OPT}^{\mathrm{Pois}}(N)]$ (Poisson) and $\mathrm{OPT}_n$ (i.i.d., $n$ arrivals).
--   - $\mathrm{CR}=\inf_{m,(\lambda_S)}\sup_{\mathrm{ALG}}\mathrm{ALG}/\mathrm{OPT}$ and $\mathrm{CR}_{\mathrm{iid}}=\inf_{n\ge1}\inf_{m,(\mu_S)}\sup_{\mathrm{ALG}}\mathrm{ALG}/\mathrm{OPT}_n$: infimum over finite instances with $\mathrm{OPT}>0$ of the supremum over policies for that (known) instance, as real `sInf`/`sSup`; $\mu$ is a probability vector on all subsets (the empty set allowed).
--   - A routing rule matches a type-$S$ arrival at time $t$ after match history $h$ to $i$ with a given probability $\rho(t,h,S,i)$ (fresh randomness), rejecting otherwise; its expected matching size in both models; the i.i.d. version runs on virtual uniform timestamps. $\lambda_S=n\mu_S$ for an i.i.d. instance.
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), §1, p. 1 (PDF 2); §2.1, pp. 5–6 (PDF 6–7); §5, pp. 18–19 (PDF 19–20); §6.1, pp. 26–27 (PDF 27–28)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws

/-!
Dütting, Feldman, Molina, *Optimal Online Stochastic Matching*, arXiv:2610.19866
(sha256 0458ce2e…), §1 p. 1 (PDF 2), §2.1 pp. 5–6 (PDF 6–7), §5 p. 18 (PDF 19),
§6.1 pp. 26–27 (PDF 27–28).

Online matching in the two arrival models, the expected online and offline values `ALG`
and `OPT`, the optimal competitive ratios `CR` and `CRiid`, and *routing rules* (online
algorithms that route an arriving vertex at random according to explicit probabilities).

**Online policies.** "Upon each arrival, an online policy either rejects the arriving vertex
or irrevocably matches it to an unmatched neighbor. Its decision may depend on the current
arrival, the history of previous arrivals and decisions, and internal randomization
independent of the arrival processes" (p. 6, PDF 7). A policy is encoded by one internal seed
`u ∼ Uniform[0,1]`, drawn independently of the arrivals, and a decision map of the seed, the
times and types of all arrivals so far, the current one last. Past decisions are functions of
these data, so they need not be supplied separately. A decision `some i` is carried out only
if `i` is an unmatched neighbour of the arrival; any other decision is a rejection. The
decision map is measurable in `(seed, arrival times)` for each fixed type sequence (types are
discrete). A single uniform seed generates any family of independent internal random
variables, so this class contains every policy of the paper.

Histories (lists of matches) are stored newest first.
-/

namespace OptStochMatch.Tight

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

/-- The first `k + 1` entries of a length-`n` sequence, `k < n`. -/
def prefixOf {α : Type} {n : ℕ} (f : Fin n → α) (k : ℕ) (hk : k < n) : Fin (k + 1) → α :=
  fun j => f ⟨j.val, by omega⟩

/-- The offline vertices matched in a history (list of `(time, vertex)`, newest first). -/
def matchedSet {m : ℕ} (h : List (ℝ × Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun i => i ∈ h.map Prod.snd

/-- The unmatched offline vertices after a history. -/
def unmatchedSet {m : ℕ} (h : List (ℝ × Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun i => i ∉ h.map Prod.snd

/-! ### Poisson arrival model -/

/-- A randomized, history-dependent, non-anticipating online matching policy for the Poisson
model. `decide k u t s` is the decision on the arrival with 0-based index `k`, given the seed
`u`, the arrival times `t 0 < ⋯ < t k` and the types `s 0, …, s k` of the arrivals so far
(the current arrival is index `k`). -/
structure PoissonPolicy (m : ℕ) where
  decide : (k : ℕ) → ℝ → (Fin (k + 1) → ℝ) → (Fin (k + 1) → Ty m) → Option (Fin m)
  measurable_decide : ∀ (k : ℕ) (s : Fin (k + 1) → Ty m) (o : Option (Fin m)),
    MeasurableSet {p : ℝ × (Fin (k + 1) → ℝ) | decide k p.1 p.2 s = o}

/-- The match record (newest first) of policy `π` with seed `u` after the first `k` arrivals of
the stream `(t, s)`. -/
def poissonRun {m : ℕ} (π : PoissonPolicy m) (u : ℝ) {n : ℕ} (t : Fin n → ℝ)
    (s : Fin n → Ty m) : ℕ → List (ℝ × Fin m)
  | 0 => []
  | k + 1 =>
    let h := poissonRun π u t s k
    if hk : k < n then
      match π.decide k u (prefixOf t k hk) (prefixOf s k hk) with
      | some i => if i ∈ s ⟨k, hk⟩ ∧ i ∉ h.map Prod.snd then (t ⟨k, hk⟩, i) :: h else h
      | none => h
    else h

/-- `ALG`: the expected size of the matching built by `π` in the Poisson model with
intensities `lam` (expectation over the arrivals and the seed). -/
noncomputable def algPois {m : ℕ} (lam : Ty m → ℝ≥0) (π : PoissonPolicy m) : ℝ :=
  (∫⁻ u, poissonExpect lam (fun n t s => ((poissonRun π u t s n).length : ℝ≥0∞)) ∂seedLaw).toReal

/-- `OPT := E[OPT^Pois(N)]`: the expected offline optimum in the Poisson model (p. 6, PDF 7). -/
noncomputable def optPoisModel {m : ℕ} (lam : Ty m → ℝ≥0) : ℝ :=
  (poissonExpect lam (fun _ _ s => ENNReal.ofReal (optPois (typeCounts s)))).toReal

/-- The optimal competitive ratio for Poisson arrivals (p. 1, PDF 2):
`CR := inf_{m, (λ_S)} sup_ALG ALG/OPT`, the infimum over finite instances with `OPT > 0`, the
supremum over online policies for the given (known) instance. -/
noncomputable def CR : ℝ :=
  sInf {r : ℝ | ∃ (m : ℕ) (lam : Ty m → ℝ≥0), 0 < optPoisModel lam ∧
    r = sSup {q : ℝ | ∃ π : PoissonPolicy m, q = algPois lam π / optPoisModel lam}}

/-! ### i.i.d. arrival model -/

/-- A randomized, history-dependent online matching policy for the i.i.d. model:
`decide k u s` is the decision on the arrival with 0-based index `k`, given the seed `u` and
the neighbourhoods `s 0, …, s k` of the arrivals so far. -/
structure IIDPolicy (m : ℕ) where
  decide : (k : ℕ) → ℝ → (Fin (k + 1) → Ty m) → Option (Fin m)
  measurable_decide : ∀ (k : ℕ) (s : Fin (k + 1) → Ty m) (o : Option (Fin m)),
    MeasurableSet {u : ℝ | decide k u s = o}

/-- The matched vertices (newest first) of an i.i.d. policy after the first `k` arrivals. -/
def iidRun {m : ℕ} (π : IIDPolicy m) (u : ℝ) {n : ℕ} (s : Fin n → Ty m) : ℕ → List (Fin m)
  | 0 => []
  | k + 1 =>
    let h := iidRun π u s k
    if hk : k < n then
      match π.decide k u (prefixOf s k hk) with
      | some i => if i ∈ s ⟨k, hk⟩ ∧ i ∉ h then i :: h else h
      | none => h
    else h

/-- `ALG` in the i.i.d. model with `n` arrivals and neighbourhood law `mu`. -/
noncomputable def algIID {m : ℕ} (n : ℕ) (mu : Ty m → ℝ≥0) (π : IIDPolicy m) : ℝ :=
  (∫⁻ u, iidExpect n mu (fun s => ((iidRun π u s n).length : ℝ≥0∞)) ∂seedLaw).toReal

/-- `OPT_n`: the expected maximum matching size with `n` i.i.d. arrivals (p. 18, PDF 19). -/
noncomputable def optIID {m : ℕ} (n : ℕ) (mu : Ty m → ℝ≥0) : ℝ :=
  (iidExpect n mu (fun s => ENNReal.ofReal (optPois (typeCounts s)))).toReal

/-- The optimal competitive ratio for i.i.d. arrivals (p. 1, PDF 2):
`CRiid := inf_n inf_{m, (µ_S)} sup_ALG ALG/OPT`, over `n ≥ 1`, probability vectors `µ` on all
subsets of `[m]` (the empty neighbourhood allowed), instances with `OPT_n > 0`, and online
policies for the given (known) `n` and `µ`. -/
noncomputable def CRiid : ℝ :=
  sInf {r : ℝ | ∃ (n m : ℕ) (mu : Ty m → ℝ≥0), 1 ≤ n ∧ ∑ S, mu S = 1 ∧ 0 < optIID n mu ∧
    r = sSup {q : ℝ | ∃ π : IIDPolicy m, q = algIID n mu π / optIID n mu}}

/-! ### Routing rules -/

/-- A routing rule: when a vertex of type `S` arrives at time `t` after the match history
`h` (newest first), it is matched to the unmatched neighbour `i ∈ S` with probability
`prob t h S i`, using fresh independent randomness, and rejected with the remaining
probability. Mass on a vertex outside `S ∩ unmatched` is a rejection. -/
structure RoutingRule (m : ℕ) where
  prob : ℝ → List (ℝ × Fin m) → Ty m → Fin m → ℝ

/-- A routing rule is valid if its probabilities are nonnegative, sum to at most one over the
available neighbours, and are measurable in the current time and the past match times (for
fixed matched vertices, type and target). -/
def RoutingRule.Valid {m : ℕ} (ρ : RoutingRule m) : Prop :=
  (∀ t h S i, 0 ≤ ρ.prob t h S i) ∧
  (∀ t h S, ∑ i ∈ S ∩ unmatchedSet h, ρ.prob t h S i ≤ 1) ∧
  (∀ (j : ℕ) (v : Fin j → Fin m) (S : Ty m) (i : Fin m),
    Measurable fun p : ℝ × (Fin j → ℝ) => ρ.prob p.1 (List.ofFn fun r => (p.2 r, v r)) S i)

/-- Expected final matching size of the routing rule `ρ` on the arrival stream `(t, s)`,
started at arrival index `k` with history `h`, with `r` arrivals of fuel (call with
`r = n`, `k = 0`, `h = []`). The expectation is over the independent routing choices. -/
noncomputable def routeValue {m : ℕ} (ρ : RoutingRule m) {n : ℕ} (t : Fin n → ℝ)
    (s : Fin n → Ty m) : ℕ → ℕ → List (ℝ × Fin m) → ℝ
  | 0, _, h => h.length
  | r + 1, k, h =>
    if hk : k < n then
      (∑ i ∈ s ⟨k, hk⟩ ∩ unmatchedSet h,
          ρ.prob (t ⟨k, hk⟩) h (s ⟨k, hk⟩) i * routeValue ρ t s r (k + 1) ((t ⟨k, hk⟩, i) :: h)) +
        (1 - ∑ i ∈ s ⟨k, hk⟩ ∩ unmatchedSet h, ρ.prob (t ⟨k, hk⟩) h (s ⟨k, hk⟩) i) *
          routeValue ρ t s r (k + 1) h
    else h.length

/-- Expected matching size of a routing rule in the Poisson model. -/
noncomputable def algRoutePois {m : ℕ} (lam : Ty m → ℝ≥0) (ρ : RoutingRule m) : ℝ :=
  (poissonExpect lam (fun n t s => ENNReal.ofReal (routeValue ρ t s n 0 []))).toReal

/-- Expected matching size of a routing rule in the i.i.d. model with `n` arrivals and law
`mu`; the rule is run on virtual independent `Uniform[0,1]` timestamps, processed in
increasing order (§5.1, p. 18, PDF 19). -/
noncomputable def algRouteIID {m : ℕ} (n : ℕ) (mu : Ty m → ℝ≥0) (ρ : RoutingRule m) : ℝ :=
  (iidTimedExpect n mu (fun t s => ENNReal.ofReal (routeValue ρ t s n 0 []))).toReal

/-- The arrival rates `λ_S = n µ_S` attached to an i.i.d. instance (5.1), p. 18 (PDF 19). -/
def iidRates {m : ℕ} (n : ℕ) (mu : Ty m → ℝ≥0) : Ty m → ℝ≥0 := fun S => (n : ℝ≥0) * mu S

end OptStochMatch.Tight


