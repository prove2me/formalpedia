-- Prove2me | Definitions.Def_HSOSetCover_FullCover_Instance
-- name    : HSOSetCover_FullCover_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:07.68976+00:00
-- url     : https://prove2.me/theorems/e358ceee-e74f-4e7a-8384-a0e77be9a231
-- title:
--   Parameters, batches and the finite schedule family $\mathcal B$
-- statement:
--   The data are $k$ labeled call opportunities, each usable once; for each $i\in[k]$ a cutoff $\ell_i>0$, a success probability $p_i\in(0,1)$ and an expected token cost $c_i>0$; a deadline $D>0$; and a positive integer turn bound $u$.
--
--   For a batch $A\subseteq[k]$,
--   $$c_A=\sum_{i\in A}c_i,\qquad f_A=\prod_{i\in A}(1-p_i),\qquad \ell_A=\max_{i\in A}\ell_i,$$
--   with $c_\emptyset=\ell_\emptyset=0$ and $f_\emptyset=1$.
--
--   The set $\mathcal B$ consists of the sequences $B=(B_1,\dots,B_t)$ with $0\le t\le u$, the $B_j$ pairwise disjoint nonempty subsets of $[k]$, and $\sum_{j}\ell_{B_j}\le D$. It is finite and contains the empty schedule. For $B\in\mathcal B$,
--   $$P_B=1-\prod_{j=1}^t f_{B_j},\qquad c(B)=\sum_{j=1}^t c_{B_j}\prod_{s<j}f_{B_s}.$$
--
--   These are schedule formulas. Operational policy success and cost are defined separately from the execution.
--
--   **Formalization Note** Opportunities are `Fin k`; schedules are lists of finsets, packaged as the finite type `Schedule P`. The bundled inequalities on the parameters are exactly the ranges stated on PDF pp. 5–6.
-- source:
--   Jie Wang, Computing Weighted Set Covers with Heterogeneous Stochastic Oracles: Deadline-Constrained Token Complexity, STOC 2027 submission #191 (October 2026), SHA-256 d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf, §3, PDF p. 5 / printed p. 4; §4, PDF p. 6 / printed p. 5

import Mathlib

namespace HSOSetCover.FullCover

/-- The numerical data of §3–§4 (PDF pp. 5–6, printed pp. 4–5): `k` labeled call opportunities, each
with a cutoff `ℓᵢ > 0`, a success probability `pᵢ ∈ (0,1)` and an expected token cost `cᵢ > 0`; a
response deadline `D > 0` and a positive integer turn bound `u`. All parameters are real. -/
structure Instance (k : ℕ) where
  /-- The cutoff `ℓᵢ` of opportunity `i`. -/
  cutoff : Fin k → ℝ
  /-- The probability `pᵢ` that opportunity `i` returns an accepted cover by `ℓᵢ`. -/
  prob : Fin k → ℝ
  /-- The expected token cost `cᵢ` of opportunity `i` through response or cancellation at `ℓᵢ`. -/
  cost : Fin k → ℝ
  /-- The response deadline `D`. -/
  deadline : ℝ
  /-- The turn bound `u`. -/
  turns : ℕ
  cutoff_pos : ∀ i, 0 < cutoff i
  prob_pos : ∀ i, 0 < prob i
  prob_lt_one : ∀ i, prob i < 1
  cost_pos : ∀ i, 0 < cost i
  deadline_pos : 0 < deadline
  turns_pos : 0 < turns

variable {k : ℕ} (P : Instance k)

/-- `c_A = ∑_{i ∈ A} cᵢ`, with `c_∅ = 0` (PDF p. 6). -/
noncomputable def batchCost (A : Finset (Fin k)) : ℝ := ∑ i ∈ A, P.cost i

/-- `f_A = ∏_{i ∈ A} (1 - pᵢ)`, with `f_∅ = 1` (PDF p. 6). -/
noncomputable def batchFail (A : Finset (Fin k)) : ℝ := ∏ i ∈ A, (1 - P.prob i)

/-- `ℓ_A = max_{i ∈ A} ℓᵢ`, with `ℓ_∅ = 0` (PDF pp. 5–6). -/
noncomputable def batchCutoff (A : Finset (Fin k)) : ℝ :=
  if h : A.Nonempty then A.sup' h P.cutoff else 0

/-- Membership in the set `𝓑` of schedules (PDF p. 6): a sequence `B = (B₁, …, B_t)` with
`0 ≤ t ≤ u`, the `B_j` pairwise disjoint nonempty subsets of `[k]`, and `∑_j ℓ_{B_j} ≤ D`. -/
def IsSchedule (B : List (Finset (Fin k))) : Prop :=
  B.length ≤ P.turns ∧ (∀ A ∈ B, A.Nonempty) ∧ B.Pairwise Disjoint ∧
    (B.map (batchCutoff P)).sum ≤ P.deadline

/-- The set `𝓑` of schedules, as a type. -/
def Schedule : Type := {B : List (Finset (Fin k)) // IsSchedule P B}

/-- `𝓑` is finite. -/
instance : Finite (Schedule P) := by
  have h : {B : List (Finset (Fin k)) | B.length ≤ P.turns}.Finite := List.finite_length_le _ _
  exact (h.subset (fun _ hB => hB.1)).to_subtype

noncomputable instance : Fintype (Schedule P) := Fintype.ofFinite _

/-- The empty schedule (`t = 0`) belongs to `𝓑`. -/
def emptySchedule : Schedule P :=
  ⟨[], by simp [IsSchedule, P.deadline_pos.le]⟩

instance : Nonempty (Schedule P) := ⟨emptySchedule P⟩

/-- `P_B = 1 - ∏_{j=1}^t f_{B_j}` (PDF p. 6). For the empty schedule this is `0`. -/
noncomputable def scheduleSuccess (B : List (Finset (Fin k))) : ℝ :=
  1 - (B.map (batchFail P)).prod

/-- `c(B) = ∑_{j=1}^t c_{B_j} ∏_{s<j} f_{B_s}` (PDF p. 6). For the empty schedule this is `0`. -/
noncomputable def scheduleCost (B : List (Finset (Fin k))) : ℝ :=
  ∑ j : Fin B.length, batchCost P (B.get j) * ((B.take j).map (batchFail P)).prod

/-- `max_{B ∈ 𝓑} P_B`, the maximum over the finite nonempty set `𝓑` (Theorem 1(3), PDF p. 6). -/
noncomputable def maxScheduleSuccess : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun B : Schedule P => scheduleSuccess P B.1)

end HSOSetCover.FullCover


