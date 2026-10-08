-- Prove2me | Definitions.Def_SkutellaCQP_RelDates_Setting
-- name    : SkutellaCQP_RelDates_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:28.044987+00:00
-- url     : https://prove2.me/theorems/5fb87b46-3a2d-4c31-be73-d564d8d51562
-- title:
--   §3, pp. 2, 7, 15–19 — R | rᵢⱼ | Σ wⱼCⱼ: schedules, Smith orders ≺ᵢ, time slots, (14)–(22), (CQP), pairwise independent rounding
-- statement:
--   **The scheduling problem $R \mid r_{ij} \mid \sum w_jC_j$.** There are $n$ jobs $J$ and $m$ unrelated parallel machines. Job $j$ has a weight $w_j \ge 0$; on machine $i$ it has a processing time $p_{ij} > 0$ and a release date $r_{ij} \ge 0$. A *nonpreemptive schedule* $S$ assigns each job $j$ a machine $i = S.\mathrm{mach}(j)$ and a start time $S_j$; its completion time is $C_j = S_j + p_{ij}$. It is *feasible* if $S_j \ge r_{ij}$ for every job and two distinct jobs on the same machine do not overlap ($C_j \le S_k$ or $C_k \le S_j$). Its value is $\sum_j w_jC_j$.
--
--   **Smith's order (p. 7).** On machine $i$, $j \prec_i k$ if $w_j/p_{ij} > w_k/p_{ik}$, or the two ratios are equal and $j < k$. This order is the one defined in the §2 setting (`SkutellaCQP.NoRel.prec`), which this file imports; §3 uses the same $\prec_i$.
--
--   **Time slots (§3.1, p. 15).** Let $\rho_{i_1} \le \dots \le \rho_{i_n}$ be the release dates $r_{ij}$, $j \in J$, sorted, and $\rho_{i_{n+1}} := \infty$. The $k$-th time slot $i_k$ of machine $i$ contains the jobs started in $[\rho_{i_k}, \rho_{i_{k+1}})$ on machine $i$. A schedule is *slot-sequenced* if, within every slot, the jobs are started in $\prec_i$ order and each job starts exactly when its $\prec_i$-predecessor in the slot completes. An assignment $\tau$ of jobs to slots is *feasible* (p. 16) if job $j$ goes to a slot $i_k$ with $\rho_{i_k} \ge r_{ij}$.
--
--   **Slot starts and completion times (15)–(17).** For an assignment vector $a = (a_{i_kj})$,
--   $$s_{i_1} = \rho_{i_1},\qquad s_{i_{k+1}} = \max\Big\{\rho_{i_{k+1}},\ s_{i_k} + \sum_j a_{i_kj}p_{ij}\Big\}.$$
--   For a slot assignment $\tau$ with $\tau(j) = i_k$ and $a$ its 0/1 vector,
--   $$C_j(\tau) = s_{i_k} + p_{ij} + \sum_{j' \prec_i j,\ \tau(j') = i_k} p_{ij'} \qquad (17),$$
--   and the schedule built from $\tau$ (p. 16) runs $j$ on machine $i$ from $C_j(\tau) - p_{ij}$.
--
--   **The relaxations (pp. 17–19).** The quadratic programming relaxation has constraints (14) $\sum_{i,k} a_{i_kj} = 1$, (18) $a_{i_kj} = 0$ if $\rho_{i_k} < r_{ij}$, (20) $a_{i_kj} \ge 0$, slot starts (15)–(16) and objective $\sum_j w_jC_j$ with
--   $$C_j = \sum_{i,k} a_{i_kj}\Big(s_{i_k} + \frac{1 + a_{i_kj}}{2}\,p_{ij} + \sum_{j' \prec_i j} a_{i_kj'}p_{ij'}\Big) \qquad (19).$$
--   The convex program (CQP) replaces $s_{i_k}$ by $\rho_{i_k}$ in (19), keeps (14), (18), (20) and adds the capacity constraints (21) $\sum_j a_{i_kj}p_{ij} \le \rho_{i_{k+1}} - \rho_{i_k}$. Its objective is $Z_{CQP}(a) = \sum_j w_j \bar C_j(a)$, with $\bar C_j(a)$ the right-hand side of (19) at $s = \rho$; this equals $b^Ta + \tfrac12c^Ta + \tfrac12a^T(D + \mathrm{diag}(c))a$ of (22).
--
--   **Randomized rounding (§3.3, p. 19).** A rounding of $a$ is a probability weight $\mu$ on slot assignments under which job $j$ lands in slot $i_k$ with probability $a_{i_kj}$, and the choices for two distinct jobs are independent: $\Pr[j \mapsto x,\ j' \mapsto y] = a_{xj}a_{yj'}$ for $j \ne j'$. $E_\mu[f] = \sum_\tau \mu(\tau) f(\tau)$.
--
--   These are the objects of every statement of §3.
--
--   **Formalization Note.** Jobs are `Fin n`, machines `Fin m`, slots `Fin m × Fin n`, all 0-based: slot `(i, k)` is the page's $i_{k+1}$. $\prec_i$ is `SkutellaCQP.NoRel.prec` from the §2 setting, cross-multiplied ($w_jp_{ik} > w_kp_{ij}$, or equality and $j<k$), equal to the page's order because $p > 0$. $\rho$ is `Tuple.sort` of the release dates; $\rho_{i_{n+1}} = \infty$ is never formed: (21) is imposed only for slots $k$ with $k+1 < n$, and the slot of a job is the largest $k$ with $\rho_{i_k} \le S_j$ (ties $\rho_{i_k} = \rho_{i_{k+1}}$ go to the later, nonempty interval). For an infeasible schedule `slotOf` has a junk value (slot 0); every statement using it assumes feasibility. Rounding is encoded by a weight function with marginals and pairwise products, not by a measure; it asks for pairwise independence only, as the page does.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 2 (§1, problem), p. 7 (≺_i), pp. 15–19 (§3.1–§3.3), displays (14)–(22)

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.RelDates

open Finset

variable {m n : ℕ}

/-! Instance data, used throughout: `p : Fin m → Fin n → ℝ` (processing times `p_ij > 0`),
`w : Fin n → ℝ` (weights `w_j ≥ 0`), `r : Fin m → Fin n → ℝ` (release dates `r_ij ≥ 0`).
Jobs are `Fin n`, machines `Fin m`, both 0-based. Time slot `(i, k)` with `k : Fin n` is the
page's slot `i_{k+1}`. -/

/-- `rho r i k = ρ_{i_{k+1}}`: the `k`-th smallest (0-based) of the release dates `r_ij`, `j ∈ J`,
on machine `i` (§3.1, p. 15). `ρ_{i_{n+1}} = ∞` is not a real number and is never formed: every
statement treats the last slot separately. -/
noncomputable def rho (r : Fin m → Fin n → ℝ) (i : Fin m) (k : Fin n) : ℝ :=
  r i (Tuple.sort (r i) k)

/-- A nonpreemptive schedule: each job `j` runs on machine `mach j` from time `start j`, without
interruption. -/
structure Sched (m n : ℕ) where
  mach : Fin n → Fin m
  start : Fin n → ℝ

/-- Completion time `C_j = S_j + p_{mach(j), j}`. -/
def compl (p : Fin m → Fin n → ℝ) (S : Sched m n) (j : Fin n) : ℝ :=
  S.start j + p (S.mach j) j

/-- Feasibility of a nonpreemptive schedule for `R | r_ij | ∑ w_j C_j` (p. 2): no job starts
before its release date on its machine, and two distinct jobs on the same machine do not
overlap. -/
def SFeasible (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n) : Prop :=
  (∀ j, r (S.mach j) j ≤ S.start j) ∧
    ∀ j k, j ≠ k → S.mach j = S.mach k → compl p S j ≤ S.start k ∨ compl p S k ≤ S.start j

/-- The objective value `∑_j w_j C_j` of a schedule. -/
def sval (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (S : Sched m n) : ℝ :=
  ∑ j, w j * compl p S j

/-- The time slot containing job `j` in schedule `S` (§3.1, p. 15): on machine `i = S.mach j`,
the largest `k` with `ρ_{i_k} ≤ S_j`, i.e. the slot `[ρ_{i_k}, ρ_{i_{k+1}})` in which `j` is
started (ties `ρ_{i_k} = ρ_{i_{k+1}}` resolved upward, so that the interval is nonempty). If no
such `k` exists (impossible for a feasible schedule, since `ρ_{i_1} ≤ r_ij ≤ S_j`), the junk
value is slot `0`; every statement using `slotOf` assumes `SFeasible`. -/
noncomputable def slotOf (r : Fin m → Fin n → ℝ) (S : Sched m n) (j : Fin n) : Fin m × Fin n :=
  (S.mach j,
    if h : (univ.filter (fun k : Fin n => rho r (S.mach j) k ≤ S.start j)).Nonempty then
      (univ.filter (fun k : Fin n => rho r (S.mach j) k ≤ S.start j)).max' h
    else ⟨0, Nat.zero_lt_of_lt j.isLt⟩)

/-- The schedule `S` sequences each time slot by `≺_i` without interruption (Lemma 3.1, p. 15):
if `j ≠ j'` lie in the same slot of machine `i` and `j ≺_i j'`, then `j` starts before `j'`;
and if moreover no job `j''` of that slot satisfies `j ≺_i j'' ≺_i j'`, then `j'` starts exactly
when `j` completes. -/
def SlotSequenced (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (S : Sched m n) : Prop :=
  ∀ j j', j ≠ j' → slotOf r S j = slotOf r S j' → SkutellaCQP.NoRel.prec p w (S.mach j) j j' →
    S.start j < S.start j' ∧
      ((∀ j'', slotOf r S j'' = slotOf r S j →
          ¬ (SkutellaCQP.NoRel.prec p w (S.mach j) j j'' ∧ SkutellaCQP.NoRel.prec p w (S.mach j) j'' j')) →
        S.start j' = compl p S j)

/-- A feasible assignment of jobs to time slots (p. 16): job `j` goes to slot `τ j = (i, k)` with
`ρ_{i_k} ≥ r_ij`. -/
def SlotFeasible (r : Fin m → Fin n → ℝ) (τ : Fin n → Fin m × Fin n) : Prop :=
  ∀ j, r (τ j).1 j ≤ rho r (τ j).1 (τ j).2

/-- Slot start times (15)–(16) for a (possibly fractional) assignment `a` (`a i k j = a_{i_k j}`),
indexed by `ℕ`: `s_{i_1} = ρ_{i_1}` and `s_{i_{k+1}} = max{ρ_{i_{k+1}}, s_{i_k} + ∑_j a_{i_k j} p_ij}`.
Indices `≥ n` are junk (`0`) and never used. -/
noncomputable def sStartN (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (i : Fin m) : ℕ → ℝ
  | 0 => if h : 0 < n then rho r i ⟨0, h⟩ else 0
  | k + 1 =>
    if h : k + 1 < n then
      max (rho r i ⟨k + 1, h⟩)
        (sStartN p r a i k + ∑ j, a i ⟨k, Nat.lt_of_succ_lt h⟩ j * p i j)
    else 0

/-- The starting time `s_{i_k}` of slot `(i, k)` under the assignment `a`, by (15)–(16). -/
noncomputable def sStart (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (i : Fin m) (k : Fin n) : ℝ :=
  sStartN p r a i k.val

/-- The 0/1 vector `a_{i_k j} = 1` iff `τ j = (i, k)` of a slot assignment `τ`. -/
def slotInd (τ : Fin n → Fin m × Fin n) : Fin m → Fin n → Fin n → ℝ :=
  fun i k j => if τ j = (i, k) then 1 else 0

/-- Completion time (17) of job `j` under the slot assignment `τ`, with `τ j = (i, k)`:
the slot start `s_{i_k}` plus `p_ij` plus the processing times of the jobs `j' ≺_i j` in the same
slot. -/
noncomputable def Cslot (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (τ : Fin n → Fin m × Fin n) (j : Fin n) : ℝ :=
  sStart p r (slotInd τ) (τ j).1 (τ j).2 + p (τ j).1 j +
    ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w (τ j).1 j' j ∧ τ j' = τ j), p (τ j).1 j'

/-- The schedule constructed from a slot assignment `τ` (p. 16): each slot is sequenced by `≺_i`
and started at `s_{i_k}`; job `j` starts at `C_j − p_ij` with `C_j` from (17). -/
noncomputable def schedOf (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (τ : Fin n → Fin m × Fin n) : Sched m n :=
  ⟨fun j => (τ j).1, fun j => Cslot p w r τ j - p (τ j).1 j⟩

/-- Feasibility for the quadratic programming relaxation (p. 17): (14) `∑_{i,k} a_{i_k j} = 1`,
(18) `a_{i_k j} = 0` if `ρ_{i_k} < r_ij`, and (20) `a_{i_k j} ≥ 0`. Constraints (15)–(16) and (19)
define `s` and `C` and are built into `sStart` and `ZQPrel`. -/
def QPFeasible (r : Fin m → Fin n → ℝ) (a : Fin m → Fin n → Fin n → ℝ) : Prop :=
  (∀ j, ∑ i, ∑ k, a i k j = 1) ∧ (∀ i k j, rho r i k < r i j → a i k j = 0) ∧
    ∀ i k j, 0 ≤ a i k j

/-- Objective value `∑_j w_j C_j` of the quadratic programming relaxation (p. 17), with `C_j`
given by (19) and `s_{i_k}` by (15)–(16):
`C_j = ∑_{i,k} a_{i_k j} (s_{i_k} + (1 + a_{i_k j})/2 · p_ij + ∑_{j' ≺_i j} a_{i_k j'} p_ij')`. -/
noncomputable def ZQPrel (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) : ℝ :=
  ∑ j, w j * ∑ i, ∑ k, a i k j *
    (sStart p r a i k + (1 + a i k j) / 2 * p i j +
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), a i k j' * p i j')

/-- Feasibility for (CQP) (pp. 18–19): (14), (18), (20) and the capacity constraints (21)
`∑_j a_{i_k j} p_ij ≤ ρ_{i_{k+1}} − ρ_{i_k}`. For the last slot `ρ_{i_{n+1}} = ∞` and (21) is no
constraint. -/
def CQPFeasible (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) : Prop :=
  QPFeasible r a ∧
    ∀ i (k : Fin n) (h : k.val + 1 < n), ∑ j, a i k j * p i j ≤ rho r i ⟨k.val + 1, h⟩ - rho r i k

/-- The value (19) with `s_{i_k}` replaced by `ρ_{i_k}`:
`C̄_j(a) = ∑_{i,k} a_{i_k j} (ρ_{i_k} + (1 + a_{i_k j})/2 · p_ij + ∑_{j' ≺_i j} a_{i_k j'} p_ij')`. -/
noncomputable def Cbar (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, ∑ k, a i k j *
    (rho r i k + (1 + a i k j) / 2 * p i j +
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), a i k j' * p i j')

/-- The objective (22) of (CQP), `b^T a + ½ c^T a + ½ a^T (D + diag(c)) a`, written as
`∑_j w_j C̄_j(a)`, the form in which the page derives it. -/
noncomputable def ZCQP (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) : ℝ :=
  ∑ j, w j * Cbar p w r a j

/-- Randomized rounding with pairwise independent choices (§3.3, p. 19), as a probability weight
`μ` on slot assignments: `μ ≥ 0`, total mass `1`, job `j` goes to slot `(i, k)` with probability
`a_{i_k j}`, and for distinct jobs `j ≠ j'` the joint probabilities are the products. -/
def IsPairwiseRounding (a : Fin m → Fin n → Fin n → ℝ)
    (μ : (Fin n → Fin m × Fin n) → ℝ) : Prop :=
  (∀ τ, 0 ≤ μ τ) ∧ ∑ τ, μ τ = 1 ∧
    (∀ j i k, ∑ τ ∈ univ.filter (fun τ : Fin n → Fin m × Fin n => τ j = (i, k)), μ τ = a i k j) ∧
    ∀ j j', j ≠ j' → ∀ x y : Fin m × Fin n,
      ∑ τ ∈ univ.filter (fun τ : Fin n → Fin m × Fin n => τ j = x ∧ τ j' = y), μ τ =
        a x.1 x.2 j * a y.1 y.2 j'

/-- Expectation `E_μ[f] = ∑_τ μ(τ) f(τ)` under a probability weight on slot assignments. -/
def E (μ : (Fin n → Fin m × Fin n) → ℝ) (f : (Fin n → Fin m × Fin n) → ℝ) : ℝ :=
  ∑ τ, μ τ * f τ

end SkutellaCQP.RelDates


