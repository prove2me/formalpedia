-- Prove2me | Definitions.Def_OptStochMatch_Tight_Algorithms
-- name    : OptStochMatch_Tight_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:55:43.57041+00:00
-- url     : https://prove2.me/theorems/5e4c4be4-48c0-4c65-a644-cc948ed1d08d
-- title:
--   The balanced allocation rule (6.1) and the matching policy associated with the rule (5.8)
-- statement:
--   - Balanced rule: for the unmatched set $A$, $s$ minimises $\sum_{i\in A}s_i^2$ subject to $s\in\mathcal P_\lambda$, $s_i=0$ ($i\notin A$), $\sum_{i\in A}s_i=\Lambda(A)$; a supporting type flow $(s_{i,S})$ (Lemma 2.3); a type-$S$ arrival is matched to $i\in S\cap A$ with probability $s_{i,S}/\lambda_S$ (exact sampling). Any choice of supporting flow is allowed.
--   - Rule (5.8): with $N=n-\#\text{completions}$ and $R=n-\sum_i x_i$, increase the unfinished coordinates of $x$ in index order within $\mathcal P_\lambda$, each capped at $x_i+R/N$; the result $y$ gives $s_i=y_i$ on unfinished jobs, $0$ otherwise.
--   - The matching policy associated with (5.8): an internal work trajectory follows the rates (5.8) between matches (a match is a completion), and a type-$S$ arrival is matched to $i\in S$ with probability $s_{i,S}(t)/(n\mu_S)$ for a type flow of the current rates; the routing probabilities are measurable.
--
--   The internal service trajectory has interval-integrable rates, as in the continuous ODE construction on PDF p. 26.
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), §5.1, pp. 18–19 (PDF 19–20); §5.3, p. 24 (PDF 25); §6.1, pp. 26–27 (PDF 27–28)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
import Definitions.Def_OptStochMatch_Tight_Matching

/-!
Dütting, Feldman, Molina, *Optimal Online Stochastic Matching*, arXiv:2610.19866
(sha256 0458ce2e…), §5.1 pp. 18–19 (PDF 19–20), §5.3 p. 24 (PDF 25), §6.1 pp. 26–27
(PDF 27–28).

The two explicit online algorithms of the paper, as routing rules.

* The **balanced allocation rule** (6.1): for the unmatched set `A`, the rates minimizing
  `∑_{i∈A} s_i²` subject to `s ∈ P_λ`, `s_i = 0` off `A`, `∑_{i∈A} s_i = Λ(A)`, a supporting type
  flow `(s_{i,S})` (Lemma 2.3), and routing of a type-`S` arrival to `i ∈ S ∩ A` with probability
  `s_{i,S}/λ_S` ("exact sampling").
* The **greedy capped rule** (5.8) of the i.i.d. analysis and *the matching policy associated
  with it* (§5.1): the policy keeps the accumulated service `x(t)` as an internal variable,
  which follows the rule's rates between matches, and routes a type-`S` arrival to `i ∈ S` with
  probability `s_{i,S}(t)/(nµ_S)` for a flow decomposition of the rates immediately before the
  arrival. A match is a job completion.
-/

namespace OptStochMatch.Tight

open MeasureTheory
open scoped NNReal ENNReal BigOperators

/-! ### The balanced allocation rule (6.1) -/

/-- The constraints of (6.1): `s ∈ P_λ`, `s_i = 0` for `i ∉ A`, `∑_{i∈A} s_i = Λ(A)`. -/
def BalancedFeasible {m : ℕ} (lam : Ty m → ℝ≥0) (A : Finset (Fin m)) (s : Fin m → ℝ) : Prop :=
  s ∈ Plam lam ∧ (∀ i, i ∉ A → s i = 0) ∧ ∑ i ∈ A, s i = coverRate lam A

/-- `s` is given by (6.1): it satisfies the constraints and minimizes `∑_{i∈A} s_i²` among
all vectors satisfying them. -/
def IsBalanced {m : ℕ} (lam : Ty m → ℝ≥0) (A : Finset (Fin m)) (s : Fin m → ℝ) : Prop :=
  BalancedFeasible lam A s ∧
    ∀ s' : Fin m → ℝ, BalancedFeasible lam A s' → ∑ i ∈ A, s i ^ 2 ≤ ∑ i ∈ A, s' i ^ 2

/-- A supporting type flow of the rate vector `s` (Lemma 2.3): nonnegative `F i S` with
`∑_{i∈S} F i S ≤ λ_S` for every `S` and `∑_{S∋i} F i S = s_i` for every `i`. -/
def IsTypeFlow {m : ℕ} (lam : Ty m → ℝ≥0) (s : Fin m → ℝ) (F : Fin m → Ty m → ℝ) : Prop :=
  (∀ i S, 0 ≤ F i S) ∧ (∀ S : Ty m, ∑ i ∈ S, F i S ≤ (lam S : ℝ)) ∧
    ∀ i, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), F i S = s i

/-- `ρ` is the balanced allocation rule with exact sampling for the rates `lam` (§6.1): for
every unmatched set `A` there are balanced rates `s^A` (6.1) with a supporting type flow
`F A`, and a type-`S` arrival (`λ_S > 0`) is matched to `i ∈ S ∩ A` with probability
`F A i S / λ_S`. The rule depends only on the unmatched set (it is recomputed after each
match and ignores rejected arrivals and times). Any choice of supporting flow is allowed. -/
def IsBalancedRouting {m : ℕ} (lam : Ty m → ℝ≥0) (ρ : RoutingRule m) : Prop :=
  ∃ F : Finset (Fin m) → Fin m → Ty m → ℝ,
    (∀ A : Finset (Fin m), ∃ s : Fin m → ℝ, IsBalanced lam A s ∧ IsTypeFlow lam s (F A)) ∧
    ∀ (t : ℝ) (h : List (ℝ × Fin m)) (S : Ty m) (i : Fin m),
      0 < lam S → i ∈ S ∩ unmatchedSet h →
        ρ.prob t h S i = F (unmatchedSet h) i S / (lam S : ℝ)

/-! ### The greedy capped rule (5.8) and its associated matching policy -/

/-- Largest feasible increase of coordinate `i` from `y` within `P_λ`:
`min_{B ∋ i} (Λ(B) − y(B))`. -/
noncomputable def polySlack {m : ℕ} (lam : Ty m → ℝ≥0) (y : Fin m → ℝ) (i : Fin m) : ℝ :=
  (Finset.univ.filter fun B : Finset (Fin m) => i ∈ B).inf' ⟨{i}, by simp⟩
    (fun B => coverRate lam B - ∑ j ∈ B, y j)

/-- One greedy step: increase coordinate `i` (if `i ∈ A`) as far as the cap `cap i` and the
constraints of `P_λ` allow. -/
noncomputable def greedyStep {m : ℕ} (lam : Ty m → ℝ≥0) (cap : Fin m → ℝ) (A : Finset (Fin m))
    (y : Fin m → ℝ) (i : Fin m) : Fin m → ℝ :=
  if i ∈ A then Function.update y i (y i + max 0 (min (cap i - y i) (polySlack lam y i))) else y

/-- Starting from `x`, increase the coordinates in `A` in index order, each until it reaches
its cap or a constraint of `P_λ` prevents further increase (§5.3, p. 24, PDF 25). -/
noncomputable def greedyCapped {m : ℕ} (lam : Ty m → ℝ≥0) (cap : Fin m → ℝ)
    (A : Finset (Fin m)) (x : Fin m → ℝ) : Fin m → ℝ :=
  (List.finRange m).foldl (greedyStep lam cap A) x

/-- The service rates (5.8) in the i.i.d. analysis with `n` arrivals and rates `lam = nµ`, at
accumulated work `x` and unfinished set `A`: with `N = n − #completions = n − (m − |A|)` and
`R = n − ∑_i x_i`, the greedy allocation `y` from `x` with caps `x_i + R/N`, and
`s_i = y_i` on `A`, `s_i = 0` off `A`. -/
noncomputable def rate58 {m : ℕ} (n : ℕ) (lam : Ty m → ℝ≥0) (x : Fin m → ℝ)
    (A : Finset (Fin m)) : Fin m → ℝ :=
  let N : ℝ := (n : ℝ) - ((m : ℝ) - (A.card : ℝ))
  let R : ℝ := (n : ℝ) - ∑ i, x i
  fun i => if i ∈ A then greedyCapped lam (fun j => x j + R / N) A x i else 0

/-- Time of the latest match in a history (newest first), `0` for the empty history. -/
def lastTime {m : ℕ} : List (ℝ × Fin m) → ℝ
  | [] => 0
  | e :: _ => e.1

/-- `ρ` is the matching policy associated with the rule (5.8) for the i.i.d. instance
`(n, µ)` (§5.1, p. 18–19, PDF 19–20): there are an internal work trajectory `X h t` (the
accumulated service at time `t` after the match history `h`) and type flows `F h t` such that

* `X [] 0 = 0`, and a match at time `τ` leaves the work unchanged at `τ`;
* between matches the work follows the rates (5.8):
  `X h t = X h τ_h + ∫_{τ_h}^t s(X h v, A_h) dv` for `τ_h ≤ t ≤ 1`, with interval-integrable
  rates (the ODE trajectories of §5.3) and `A_h` the unmatched
  set and `τ_h` the time of the latest match;
* `F h t` is a type flow (Lemma 2.3) of the rates `s(X h t, A_h)` for the rates `nµ` whenever
  these rates lie in `P_λ` (they do on every reachable state, Lemma 5.3; on unreachable
  histories no flow need exist and none is required);
* a type-`S` arrival (`µ_S > 0`) at time `t` is routed to `i ∈ S` with probability
  `F h t i S / (n µ_S)`, using the rates immediately before the arrival;
* `ρ` is a valid (in particular measurable) routing rule. -/
def IsAssoc58 {m : ℕ} (n : ℕ) (mu : Ty m → ℝ≥0) (ρ : RoutingRule m) : Prop :=
  ∃ (X : List (ℝ × Fin m) → ℝ → Fin m → ℝ) (F : List (ℝ × Fin m) → ℝ → Fin m → Ty m → ℝ),
    X [] 0 = 0 ∧
    (∀ (τ : ℝ) (i : Fin m) (h : List (ℝ × Fin m)), X ((τ, i) :: h) τ = X h τ) ∧
    (∀ (h : List (ℝ × Fin m)) (t : ℝ), t ∈ Set.Icc (lastTime h) 1 → ∀ i,
      IntervalIntegrable
        (fun v => rate58 n (iidRates n mu) (X h v) (unmatchedSet h) i)
        volume (lastTime h) t ∧
      X h t i = X h (lastTime h) i +
        ∫ v in (lastTime h)..t, rate58 n (iidRates n mu) (X h v) (unmatchedSet h) i) ∧
    (∀ (h : List (ℝ × Fin m)) (t : ℝ),
      rate58 n (iidRates n mu) (X h t) (unmatchedSet h) ∈ Plam (iidRates n mu) →
      IsTypeFlow (iidRates n mu) (rate58 n (iidRates n mu) (X h t) (unmatchedSet h)) (F h t)) ∧
    (∀ (t : ℝ) (h : List (ℝ × Fin m)) (S : Ty m) (i : Fin m), 0 < mu S → i ∈ S →
      ρ.prob t h S i = F h t i S / ((iidRates n mu S : ℝ))) ∧
    ρ.Valid

end OptStochMatch.Tight


