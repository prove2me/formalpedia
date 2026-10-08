-- Prove2me | Definitions.Def_KelsoCrawford_Process_Process
-- name    : KelsoCrawford_Process_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:29:50.454286+00:00
-- url     : https://prove2.me/theorems/d6530914-64b7-44b3-8246-c1026f03549b
-- title:
--   Section 3, pp. 1488–1489 — runs of the salary-adjustment process R1–R5
-- statement:
--   The **salary-adjustment process** (rules R1–R5) runs in rounds $t = 0, 1, 2, \dots$. A run records, for each round $t$, the permitted salaries $s_{ij}(t)$, the set of workers to whom firm $j$ makes offers, and the firm whose offer each worker tentatively accepts. A run with salary unit $\delta$ obeys:
--
--   1. **R1**: $s_{ij}(0) = \sigma_{ij}$, and in round $0$ every firm makes offers to all workers;
--   2. **R2**: in every later round $t$, each firm $j$ makes offers to a set of workers maximizing $\pi^j[C; s^j(t)]$, and this set contains every offer firm $j$ made in round $t-1$ that was not rejected;
--   3. **R3**: every worker with at least one offer tentatively accepts an offer that is a favorite one, comparing $u^i(k; s_{ik}(t))$ over the offering firms $k$, and rejects the others; ties are broken arbitrarily;
--   4. **R4**: if worker $i$ rejected firm $j$'s offer in round $t-1$, then $s_{ij}(t) = s_{ij}(t-1) + \delta$; otherwise $s_{ij}(t) = s_{ij}(t-1)$;
--   5. **R5**: the process stops at a round in which no rejections are issued; each worker then accepts the offer he or she holds, at that firm's current permitted salary.
--
--   A run is any sequence satisfying these rules, so every tie-breaking by firms and workers gives a run. The definitions also allow the process to be started from other salaries and offers (`IsRunFrom`), which later missions of the series use.
--
--   **Formalization Note** Rejection in round $t$ means: $i$ received $j$'s offer in round $t$ and tentatively accepted a different firm's offer. Rule R4 is written as $s_{ij}(t+1)$ from round $t$. The paper's unit is $1$; here it is a parameter $\delta$. A worker without offers has an unconstrained (meaningless) `choice`. "Stopped at $t$" and "the outcome at $t$" are defined for every round $t$; theorems say which rounds they concern. Runs are not computed by a fixed tie-breaking rule: theorems quantify over all runs.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1488–1489, Section 3, rules R1–R5

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model

namespace KelsoCrawford.Process

/-- A run of the salary-adjustment process (§3, pp. 1488–1489), recorded round by round:
`sal t i j` is the permitted salary `s_ij(t)`, `offers t j` the set of workers firm `j` makes
offers to in round `t`, and `choice t i` the firm whose offer worker `i` tentatively accepts in
round `t` (meaningful only when `i` has an offer). -/
structure Run (W F : Type) where
  sal : ℕ → W → F → ℝ
  offers : ℕ → F → Finset W
  choice : ℕ → W → F

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

/-- R3: in round `t` worker `i` rejects firm `j`'s offer: `j` made `i` an offer and `i` did not
tentatively accept it. -/
def Run.Rejects (ρ : Run W F) (t : ℕ) (i : W) (j : F) : Prop :=
  i ∈ ρ.offers t j ∧ ρ.choice t i ≠ j

instance (ρ : Run W F) (t : ℕ) (i : W) (j : F) : Decidable (ρ.Rejects t i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `ρ` follows rules R2–R4 with salary unit `δ`, starting from permitted salaries `sal₀` and
round-0 offers `offers₀`:
1. round 0 is `(sal₀, offers₀)`;
2. R2: in every round `t + 1` each firm offers to a profit-maximizing set at its current permitted
   salaries, and this set contains every offer it made in round `t` that was not rejected;
3. R3: in every round, a worker with at least one offer tentatively accepts an offer that is a
   favorite among the offers received (ties broken arbitrarily);
4. R4: `s_ij` rises by `δ` after `i` rejects `j`, and is otherwise unchanged. -/
def Market.IsRunFrom (M : Market W F) (δ : ℝ) (sal₀ : W → F → ℝ)
    (offers₀ : F → Finset W) (ρ : Run W F) : Prop :=
  (ρ.sal 0 = sal₀ ∧ ρ.offers 0 = offers₀) ∧
  (∀ t j, IsDemanded (M.y j) (fun i => ρ.sal (t + 1) i j) (ρ.offers (t + 1) j) ∧
    (ρ.offers t j).filter (fun i => ¬ ρ.Rejects t i j) ⊆ ρ.offers (t + 1) j) ∧
  (∀ t i, (∃ j, i ∈ ρ.offers t j) →
    i ∈ ρ.offers t (ρ.choice t i) ∧
    ∀ k, i ∈ ρ.offers t k →
      M.u i k (ρ.sal t i k) ≤ M.u i (ρ.choice t i) (ρ.sal t i (ρ.choice t i))) ∧
  (∀ t i j, ρ.sal (t + 1) i j = if ρ.Rejects t i j then ρ.sal t i j + δ else ρ.sal t i j)

/-- A run of the salary-adjustment process R1–R5 with unit `δ`: R1 starts at `s_ij(0) = σ_ij`
with every firm making offers to all workers in round 0. -/
def Market.IsRun (M : Market W F) (δ : ℝ) (ρ : Run W F) : Prop :=
  M.IsRunFrom δ M.σ (fun _ => Finset.univ) ρ

/-- R5: no rejections are issued in round `t`. -/
def Run.Stopped (ρ : Run W F) (t : ℕ) : Prop :=
  ∀ i j, ¬ ρ.Rejects t i j

/-- R5: the allocation read off at round `t`: each worker goes to the firm whose offer he or she
holds, at that firm's permitted salary. -/
def Run.outcome (ρ : Run W F) (t : ℕ) : Allocation W F :=
  ⟨ρ.choice t, fun i => ρ.sal t i (ρ.choice t i)⟩

end KelsoCrawford.Process


