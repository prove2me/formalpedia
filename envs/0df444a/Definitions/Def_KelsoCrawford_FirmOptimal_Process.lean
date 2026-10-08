-- Prove2me | Definitions.Def_KelsoCrawford_FirmOptimal_Process
-- name    : KelsoCrawford_FirmOptimal_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:29.132753+00:00
-- url     : https://prove2.me/theorems/5cb94457-6c0a-42b0-bcb4-550bd3fd98ee
-- title:
--   Section 3, pp. 1488–1489 — the salary-adjustment process R1–R5
-- statement:
--   This file encodes the salary-adjustment process R1–R5 of Kelso and Crawford for a discrete market with salary unit $\delta$.
--
--   A **run** records, for every round $t = 0, 1, 2, \dots$, the permitted salaries $s_{ij}(t)$, the set of workers to whom each firm $j$ makes offers, and the firm whose offer each worker tentatively accepts. Worker $i$ **rejects** firm $j$ in round $t$ if $j$ makes $i$ an offer in round $t$ and $i$ tentatively accepts another firm's offer. A run obeys the rules:
--
--   1. **R1.** $s_{ij}(0) = \sigma_{ij}$, and in round $0$ every firm makes offers to all workers.
--   2. **R2.** In every later round each firm makes offers to the members of one of its profit-maximizing sets of workers at its current permitted salaries; any offer of the previous round that was not rejected is repeated.
--   3. **R3.** Every worker who receives at least one offer tentatively accepts one of his or her favorite offers (ties broken arbitrarily) and rejects the rest.
--   4. **R4.** If worker $i$ rejected firm $j$ in round $t$, then $s_{ij}(t+1) = s_{ij}(t) + \delta$; otherwise $s_{ij}(t+1) = s_{ij}(t)$.
--   5. **R5.** The process stops in a round in which no rejections are issued; the resulting allocation assigns each worker to the firm whose offer he or she holds, at that firm's permitted salary.
--
--   Every way of breaking ties allowed by R2 and R3 gives a run, so a statement about all runs is a statement about every tie-breaking rule.
--
--   **Formalization Note** The paper's unit is $1$ (R4: $s_{ij}(t) = s_{ij}(t-1) + 1$); a general unit $\delta$ is used. The process is also defined from an arbitrary starting state (`IsRunFrom`); the paper's process is the one starting at R1. The decidability instance for "rejects" is a structural helper.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1488–1489, Section 3, R1–R5

import Mathlib
import Definitions.Def_KelsoCrawford_FirmOptimal_Model

namespace KelsoCrawford.FirmOptimal

/-- A run of the salary-adjustment process: permitted salaries `sal t i j = s_ij(t)`, the set
`offers t j` of workers firm `j` makes offers to in round `t`, and the firm `choice t i` whose
offer worker `i` tentatively accepts in round `t`. -/
structure Run (W F : Type) where
  sal : ℕ → W → F → ℝ
  offers : ℕ → F → Finset W
  choice : ℕ → W → F

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

/-- R3: in round `t` worker `i` rejects firm `j`'s offer. -/
def Run.Rejects (ρ : Run W F) (t : ℕ) (i : W) (j : F) : Prop :=
  i ∈ ρ.offers t j ∧ ρ.choice t i ≠ j

instance Run.decidableRejects (ρ : Run W F) (t : ℕ) (i : W) (j : F) :
    Decidable (ρ.Rejects t i j) :=
  inferInstanceAs (Decidable (i ∈ ρ.offers t j ∧ ρ.choice t i ≠ j))

/-- `ρ` follows R2–R4 from the round-0 state `(sal₀, offers₀)`, with salary unit `δ`. -/
def Market.IsRunFrom (M : Market W F) (δ : ℝ) (sal₀ : W → F → ℝ) (offers₀ : F → Finset W)
    (ρ : Run W F) : Prop :=
  (ρ.sal 0 = sal₀ ∧ ρ.offers 0 = offers₀) ∧
  (∀ t j, KelsoCrawford.Process.IsDemanded (M.y j) (fun i => ρ.sal (t+1) i j) (ρ.offers (t+1) j) ∧
    (ρ.offers t j).filter (fun i => ¬ ρ.Rejects t i j) ⊆ ρ.offers (t+1) j) ∧
  (∀ t i, (∃ j, i ∈ ρ.offers t j) → i ∈ ρ.offers t (ρ.choice t i) ∧
    ∀ k, i ∈ ρ.offers t k → M.u i k (ρ.sal t i k) ≤ M.u i (ρ.choice t i) (ρ.sal t i (ρ.choice t i))) ∧
  (∀ t i j, ρ.sal (t+1) i j = if ρ.Rejects t i j then ρ.sal t i j + δ else ρ.sal t i j)

/-- R1–R4: a run of the salary-adjustment process, starting from `s_ij(0) = σ_ij` with every
firm making offers to all workers in round zero. -/
def Market.IsRun (M : Market W F) (δ : ℝ) (ρ : Run W F) : Prop :=
  M.IsRunFrom δ M.σ (fun _ => Finset.univ) ρ

/-- R5: no rejections are issued in round `t`. -/
def Run.Stopped (ρ : Run W F) (t : ℕ) : Prop := ∀ i j, ¬ ρ.Rejects t i j

/-- R5: the allocation in which workers accept the offers in force in round `t`. -/
def Run.outcome (ρ : Run W F) (t : ℕ) : Allocation W F :=
  ⟨ρ.choice t, fun i => ρ.sal t i (ρ.choice t i)⟩

end KelsoCrawford.FirmOptimal


