-- Prove2me | Definitions.Def_SkutellaCQP_Preempt_Setting
-- name    : SkutellaCQP_Preempt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:15.691513+00:00
-- url     : https://prove2.me/theorems/9659d256-6301-4336-ad8c-44ca8c289a83
-- title:
--   §§2–4, pp. 2–22 — preemptive schedules on unrelated machines with release dates, ≺ᵢ, time slots, fractions a_{i_k j}, (CQP′_p), slot schedules (15)–(17), pairwise rounding
-- statement:
--   This file fixes the model of §4 of Skutella's paper: preemptive scheduling of $n$ jobs on $m$ unrelated parallel machines with machine-dependent release dates, the problem $R\mid r_{ij},\,pmtn\mid\sum w_jC_j$, together with the objects of §3 that §4 reuses.
--
--   **Instance.** Jobs are $j\in J=\{1,\dots,n\}$ and machines $i\in\{1,\dots,m\}$. Job $j$ has weight $w_j\ge 0$, processing time $p_{ij}>0$ on machine $i$, and release date $r_{ij}\ge 0$ on machine $i$ (the standing assumptions of p. 2).
--
--   **Smith's order** (p. 7). For each machine $i$, $j\prec_i k$ if $w_j/p_{ij}>w_k/p_{ik}$, or the two ratios are equal and $j<k$.
--
--   **Time slots** (p. 15). Let $\rho_{i_1}\le\rho_{i_2}\le\dots\le\rho_{i_n}$ be the release dates $r_{ij}$, $j\in J$, on machine $i$ in nondecreasing order, and $\rho_{i_{n+1}}:=\infty$. The $k$-th time slot $i_k$ of machine $i$ is the interval $[\rho_{i_k},\rho_{i_{k+1}})$.
--
--   **Preemptive schedules** (pp. 2, 21). A preemptive schedule is a finite list of *pieces*; a piece says that job $j$ is processed on machine $i$ during a time interval $[s,e]$. Processing job $j$ on machine $i$ for $\ell$ time units completes the fraction $\ell/p_{ij}$ of it. A schedule is **feasible** when
--   1. every piece of job $j$ on machine $i$ starts no earlier than $r_{ij}$ and has $s\le e$;
--   2. two different pieces on the same machine do not overlap in time (one ends no later than the other starts);
--   3. two different pieces of the same job do not overlap in time;
--   4. for every job $j$ the fractions of its pieces add up to exactly $1$.
--
--   The **completion time** $C_j$ is the largest end time of a piece of $j$, and the objective is $\sum_j w_jC_j$. A schedule is **nonpreemptive** if every job consists of exactly one piece; a feasible nonpreemptive schedule is a schedule of $R\mid r_{ij}\mid\sum w_jC_j$. The order $\prec$ of the proof of Lemma 4.2 sorts jobs by nondecreasing completion time in a given preemptive schedule, ties broken by index.
--
--   **The fractional assignment of a preemptive schedule** (p. 21). $a_{i_kj}$ is the fraction of job $j$ processed on machine $i$ within $[\rho_{i_k},\rho_{i_{k+1}})$, i.e. the total length of the intersections of $j$'s pieces on $i$ with that interval, divided by $p_{ij}$.
--
--   **The relaxation $(CQP'_p)$** (p. 22). With $b_{i_kj}=w_j\rho_{i_k}$, $c_{i_kj}=w_jp_{ij}$ and the slot-block matrix $D$ of p. 19, a pair $(a,Z)$ is feasible when
--   $$
--   \begin{aligned}
--   &\textstyle\sum_{i,k}a_{i_kj}=1\ \ \forall j, \qquad \sum_j a_{i_kj}p_{ij}\le\rho_{i_{k+1}}-\rho_{i_k}\ \ \forall i,k,\qquad a_{i_kj}=0 \text{ if } \rho_{i_k}<r_{ij},\qquad a\ge 0,\\
--   &Z\ \ge\ b^Ta+\tfrac12a^T(D+\mathrm{diag}(c))a=\sum_j w_j\sum_{i,k}a_{i_kj}\Bigl(\rho_{i_k}+\frac{a_{i_kj}}{2}p_{ij}+\sum_{j'\prec_i j}a_{i_kj'}p_{ij'}\Bigr)\quad(26),\\
--   &Z\ \ge\ c^Ta=\sum_j w_j\sum_{i,k}a_{i_kj}p_{ij}\quad(27).
--   \end{aligned}
--   $$
--   The constraint $a_{i_kj}=0$ if $\rho_{i_k}<r_{ij}$ is (18) of §3. The display of $(CQP'_p)$ on p. 22 does not list it; it is added here because Lemma 4.3 needs it (without it the rounding may start a job before its release date), and the fractions of every feasible preemptive schedule satisfy it, so the program stays a relaxation.
--
--   **Slot assignments and their schedule** (p. 16, (15)–(17)). An assignment $\tau$ of each job to a slot $i_k$ is feasible if $\rho_{i_k}\ge r_{ij}$. Its schedule sequences the jobs of slot $i_k$ by $\prec_i$, starting the slot at $s_{i_1}=\rho_{i_1}$, $s_{i_{k+1}}=\max\{\rho_{i_{k+1}},\,s_{i_k}+\sum_{j\in i_k}p_{ij}\}$, so that
--   $$
--   C_j=s_{i_k}+p_{ij}+\sum_{j'\in i_k,\ j'\prec_i j}p_{ij'}\qquad(j\in i_k).
--   $$
--   The file also records this schedule as a list of pieces (one per job, ending at $C_j$).
--
--   **Randomized rounding** (pp. 8, 19). Algorithm RANDOMIZED ROUNDING assigns each job $j$ to slot $i_k$ with probability $a_{i_kj}$, the choices being pairwise independent for the jobs. It is encoded as a probability weight $\mu$ on slot assignments: $\mu\ge0$, $\sum_\tau\mu(\tau)=1$, $\Pr[\tau(j)=i_k]=a_{i_kj}$, and $\Pr[\tau(j)=x,\ \tau(j')=y]=a_{x,j}\,a_{y,j'}$ for $j\ne j'$. $\mathbb E_\mu[f]=\sum_\tau\mu(\tau)f(\tau)$.
--
--   **Formalization Note** Jobs, machines and slots are 0-based (`Fin n`, `Fin m`, `Fin n`): `rho r i k` is $\rho_{i_{k+1}}$ of the page, obtained by sorting `r i` with `Tuple.sort`. The last slot has no right end (`slotEnd = none`), so $\rho_{i_{n+1}}=\infty$ is never a real number; constraint (21) is imposed only for slots that have a successor. $\prec_i$ is cross-multiplied ($w_jp_{ik}>w_kp_{ij}$), which equals the page's ratio definition because $p>0$. The completion time of a job without pieces is $0$; feasibility forbids that case. Pieces of length $0$ are allowed and harmless. The quadratic form of (26) is written as the explicit double sum it equals (the matrix $D$ has $w_{j'}p_{ij}$ at $(i_kj,i_kj')$ for $j\prec_i j'$, $w_jp_{ij'}$ for $j'\prec_i j$, and $0$ otherwise). Communication delays (p. 21) are not modelled: every feasible schedule under any delay model is feasible here, so bounds against this preemptive optimum imply the bounds for every delay model. Rounding is a weight on the finite set of slot assignments, not a measure; pairwise independence is required, full independence is not.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 2 (standing assumptions), p. 7 (≺ᵢ), p. 15 (time slots), p. 16 ((15)–(17)), p. 19 (b, c, D; randomized rounding), pp. 21–22 (§4: preemptive schedules, a_{i_k j}, (CQP′_p))

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.Preempt

open Finset

variable {m n : ℕ}

/-- The right end of slot `(i, k)`: `some ρ_{i_{k+2}}` (0-based `k+1`) if it exists, and `none`
for the last slot, whose interval `[ρ_{i_n}, ∞)` is unbounded (`ρ_{i_{n+1}} := ∞`). -/
noncomputable def slotEnd (r : Fin m → Fin n → ℝ) (i : Fin m) (k : Fin n) : Option ℝ :=
  if h : k.val + 1 < n then some (SkutellaCQP.RelDates.rho r i ⟨k.val + 1, h⟩) else none

/-- Length of the intersection of `[s, e]` with `[lo, hi)` (with `hi = ∞` for `none`). -/
def overlapLen (s e lo : ℝ) : Option ℝ → ℝ
  | some hi => max 0 (min e hi - max s lo)
  | none => max 0 (e - max s lo)

/-! ### Preemptive schedules -/

/-- One piece of a preemptive schedule: job `job` is processed on machine `mach` during
`[start, stop]`. -/
structure Piece (m n : ℕ) where
  job : Fin n
  mach : Fin m
  start : ℝ
  stop : ℝ

/-- A preemptive schedule is a finite list of pieces. -/
abbrev PSched (m n : ℕ) := List (Piece m n)

/-- Feasibility of a preemptive schedule for `R | r_ij, pmtn | ∑ w_j C_j` (pp. 2, 21):
pieces respect release dates; a machine processes one piece at a time; a job is processed by one
machine at a time; every job receives exactly its full processing requirement, where a time span
of length `ℓ` on machine `i` processes the fraction `ℓ / p_ij` of job `j`. -/
def PFeasible (p r : Fin m → Fin n → ℝ) (P : PSched m n) : Prop :=
  (∀ q ∈ P, r q.mach q.job ≤ q.start ∧ q.start ≤ q.stop) ∧
  (∀ x y : Fin P.length, x ≠ y → (P.get x).mach = (P.get y).mach →
      (P.get x).stop ≤ (P.get y).start ∨ (P.get y).stop ≤ (P.get x).start) ∧
  (∀ x y : Fin P.length, x ≠ y → (P.get x).job = (P.get y).job →
      (P.get x).stop ≤ (P.get y).start ∨ (P.get y).stop ≤ (P.get x).start) ∧
  (∀ j : Fin n, ((P.filter (fun q => q.job = j)).map
      (fun q => (q.stop - q.start) / p q.mach j)).sum = 1)

/-- Completion time `C_j` of job `j`: the largest stop time of its pieces (`0` if it has none,
which never happens in a feasible schedule). -/
def pcompl (P : PSched m n) (j : Fin n) : ℝ :=
  ((P.filter (fun q => q.job = j)).map Piece.stop).foldr max 0

/-- Objective `∑_j w_j C_j` of a preemptive schedule. -/
def pval (w : Fin n → ℝ) (P : PSched m n) : ℝ :=
  ∑ j, w j * pcompl P j

/-- A schedule is nonpreemptive if every job consists of exactly one piece. -/
def Nonpreemptive (P : PSched m n) : Prop :=
  ∀ j : Fin n, (P.filter (fun q => q.job = j)).length = 1

/-- The order `≺` of the proof of Lemma 4.2 (p. 21): nondecreasing completion times in `P`,
ties broken by index. -/
def cprec (P : PSched m n) (j' j : Fin n) : Prop :=
  pcompl P j' < pcompl P j ∨ (pcompl P j' = pcompl P j ∧ j' < j)

noncomputable instance (P : PSched m n) (j' j : Fin n) : Decidable (cprec P j' j) := by
  unfold cprec; infer_instance

/-- The fractional assignment of a preemptive schedule (p. 21): `frac p r P i k j` is
`a_{i_k j}`, the fraction of job `j` processed on machine `i` within `[ρ_{i_k}, ρ_{i_{k+1}})`. -/
noncomputable def frac (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (i : Fin m) (k : Fin n) (j : Fin n) : ℝ :=
  ((P.filter (fun q => q.job = j ∧ q.mach = i)).map
      (fun q => overlapLen q.start q.stop (SkutellaCQP.RelDates.rho r i k) (slotEnd r i k))).sum / p i j

/-! ### The relaxation (CQP′_p) -/

/-- Right hand side of (23) / (26): `b^T a + ½ a^T (D + diag(c)) a`, written as sums. -/
noncomputable def rhs23 (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) : ℝ :=
  ∑ j, w j * ∑ i, ∑ k, a i k j * (SkutellaCQP.RelDates.rho r i k + a i k j / 2 * p i j +
    ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), a i k j' * p i j')

/-- Right hand side of (24) / (27): `c^T a`, written as sums. -/
def rhs24 (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (a : Fin m → Fin n → Fin n → ℝ) : ℝ :=
  ∑ j, w j * ∑ i, ∑ k, a i k j * p i j

/-- Feasibility of `(a, Z)` for (CQP′_p) (p. 22): constraints (14), (21), (26), (27), `a ≥ 0`,
and in addition (18) (`a_{i_k j} = 0` if `ρ_{i_k} < r_ij`), which the page omits from the
display (see the natural-language statement). (21) is absent for the last slot of each machine,
since `ρ_{i_{n+1}} = ∞`. -/
def CQPpFeasible (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (Z : ℝ) : Prop :=
  (∀ j, ∑ i, ∑ k, a i k j = 1) ∧
  (∀ i k (h : k.val + 1 < n), ∑ j, a i k j * p i j ≤ SkutellaCQP.RelDates.rho r i ⟨k.val + 1, h⟩ - SkutellaCQP.RelDates.rho r i k) ∧
  (∀ i k j, SkutellaCQP.RelDates.rho r i k < r i j → a i k j = 0) ∧
  rhs23 p w r a ≤ Z ∧
  rhs24 p w a ≤ Z ∧
  (∀ i k j, 0 ≤ a i k j)

/-! ### Slot assignments, the schedule (15)–(17), and randomized rounding -/

/-- Value `∑_j w_j C_j` of the nonpreemptive schedule built from `τ`. -/
noncomputable def roundVal (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (τ : Fin n → Fin m × Fin n) : ℝ :=
  ∑ j, w j * SkutellaCQP.RelDates.Cslot p w r τ j

/-- The schedule built from `τ`, as a preemptive schedule with one piece per job:
job `j` runs on machine `(τ j).1` during `[C_j − p_ij, C_j]`. -/
noncomputable def toPSched (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (τ : Fin n → Fin m × Fin n) : PSched m n :=
  List.ofFn fun j : Fin n =>
    { job := j, mach := (τ j).1,
      start := SkutellaCQP.RelDates.Cslot p w r τ j - p (τ j).1 j, stop := SkutellaCQP.RelDates.Cslot p w r τ j }

end SkutellaCQP.Preempt


