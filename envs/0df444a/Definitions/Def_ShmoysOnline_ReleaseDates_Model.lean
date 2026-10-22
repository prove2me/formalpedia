-- Prove2me | Definitions.Def_ShmoysOnline_ReleaseDates_Model
-- name    : ShmoysOnline_ReleaseDates_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:38.335847+00:00
-- url     : https://prove2.me/theorems/51788880-21ba-4699-9a1a-d2574e9f435e
-- title:
--   Static resource schedules, releases, and the makespan comparator
-- statement:
--   Let $R$ be a finite set of exclusive resources and $D$ a type of job data. A job profile is a finite list of intervals $[a,b)$, with $0\le a<b$, a nonempty subset of $R$, and an operation or attempt tag. Its duration is the maximum right endpoint, taking the empty maximum to be zero. An environment supplies a job-local legality condition on these profiles and the set of completed internal operations observable from a profile. A datum is admissible when at least one well-formed legal profile exists.
--
--   A finite instance $I$ specifies distinct natural-number job identities $J$, job data $d_j$, and nonnegative real release dates $r_j$. A placement consists of a nonnegative start offset $s_j$ and a profile. A feasible schedule gives every job a well-formed legal profile, satisfies $s_j\ge r_j$, and forbids overlapping use of any shared resource by different jobs. Its completion times and makespan are
--   $$C_j=s_j+\max_{a\in p_j} a_{\rm end},\qquad C_{\max}=\max(\{0\}\cup\{C_j:j\in J\}).$$
--   Restriction retains whole jobs; zero-release restriction resets their releases; translation adds a common offset; inverse translation subtracts an offset and is used only when all affected starts are at least that offset. Joining schedules selects one schedule on a specified set of jobs and the other on its complement. The predicate $\operatorname{Approx}(E,I,\rho,S)$ requires feasibility and $C_{\max}(S)\le\rho C_{\max}(U)$ for every feasible schedule $U$ of the same released instance.
--
--   Concrete parallel environments have $m$ machines, positive sizes $p_j$ and positive speeds $s_{ij}$. Profiles run a job on at most one machine at a time. In the nonpreemptive case there is one successful uninterrupted interval. With restarts, every canceled interval does strictly less than the required work and only the last uninterrupted attempt completes the job. With preemption, work $(b-a)s_{ij}$ accumulates across intervals and migrations and totals $p_j$. Identical and uniformly related machines are the specializations $s_{ij}=1$ and $s_{ij}=s_i$.
--
--   This provides schedule semantics independent of the algorithm. Concrete shop jobs have positive-duration operations on specified machines, no within-job overlap, and a given precedence relation; open shops use no precedence pairs, while flow and job shops encode their operation order. A mesh job occupies one of its allowed processor subsets uninterrupted for its required duration. Cross-job resource exclusion remains fixed.
--
--   **Formalization Note** Time is nonnegative real, intervals are half open, real jobs have positive work, and empty instances have makespan zero. Unused entries of total job-indexed functions are ignored. Admissibility excludes a nonempty input with no usable resources. The comparator formulation avoids total real-infimum defaults; for the nonempty, lower-bounded set of feasible makespans it is equivalent to the optimum formulation.
-- source:
--   Shmoys, Wein and Williamson, Scheduling Parallel Machines On-Line, SIAM J. Comput. 24(6) (1995), DOI https://doi.org/10.1137/S0097539793248317; §1 p. 1314 (PDF 2), §2 pp. 1316–1317 (PDF 4–5).

import Mathlib

set_option autoImplicit false
open scoped NNReal
noncomputable section

namespace ShmoysOnline.ReleaseDates

/-- A finite piece of a job's local execution; resources may be a whole submesh.
The tag distinguishes operations or attempts within a job. -/
structure Slice where
  lo : ℝ≥0
  hi : ℝ≥0
  resources : Finset ℕ
  tag : ℕ
  deriving DecidableEq

abbrev Profile := List Slice

def span (p : Profile) : ℝ≥0 := (p.map Slice.hi).foldr max 0

def WellFormed (resources : Finset ℕ) (p : Profile) : Prop :=
  p ≠ [] ∧ ∀ s ∈ p, s.lo < s.hi ∧ s.resources.Nonempty ∧ s.resources ⊆ resources

/-- Static, job-local constraints. There are no constraints between different jobs
except exclusive use of the fixed resources. Operations within a shop job, mesh
requirements and restart/preemption rules belong to `legal`. -/
structure Environment (D : Type) where
  resources : Finset ℕ
  legal : D → Profile → Prop
  /-- Completed internal operations observable from actual processing. -/
  progress : D → Profile → Finset ℕ

def Admissible {D : Type} (E : Environment D) (d : D) : Prop :=
  ∃ p, WellFormed E.resources p ∧ E.legal d p

structure Instance (D : Type) where
  jobs : Finset ℕ
  data : ℕ → D
  release : ℕ → ℝ≥0

def Valid {D : Type} (E : Environment D) (I : Instance D) : Prop :=
  ∀ j ∈ I.jobs, Admissible E (I.data j)

structure Placement where
  start : ℝ≥0
  profile : Profile
  deriving Inhabited

abbrev Schedule := ℕ → Placement

def completion (s : Schedule) (j : ℕ) : ℝ≥0 := (s j).start + span (s j).profile

noncomputable def makespan (J : Finset ℕ) (s : Schedule) : ℝ≥0 :=
  J.sup (completion s)

def Feasible {D : Type} (E : Environment D) (I : Instance D) (s : Schedule) : Prop :=
  (∀ j ∈ I.jobs, I.release j ≤ (s j).start ∧
    WellFormed E.resources (s j).profile ∧ E.legal (I.data j) (s j).profile) ∧
  (∀ j ∈ I.jobs, ∀ k ∈ I.jobs, j ≠ k →
    ∀ a ∈ (s j).profile, ∀ b ∈ (s k).profile,
      ¬ Disjoint a.resources b.resources →
      (s j).start + a.hi ≤ (s k).start + b.lo ∨
      (s k).start + b.hi ≤ (s j).start + a.lo)

def zeroInstance {D : Type} (I : Instance D) (J : Finset ℕ) : Instance D :=
  ⟨J, I.data, fun _ => 0⟩

def restrictInstance {D : Type} (I : Instance D) (J : Finset ℕ) : Instance D :=
  { I with jobs := I.jobs ∩ J }

def translate (t : ℝ≥0) (s : Schedule) : Schedule :=
  fun j => { s j with start := t + (s j).start }

/-- Used only when every selected placement starts at or after `t`. -/
def untranslate (t : ℝ≥0) (s : Schedule) : Schedule :=
  fun j => { s j with start := (s j).start - t }

noncomputable def join (J : Finset ℕ) (s u : Schedule) : Schedule :=
  fun j => if j ∈ J then s j else u j

/-- Comparator formulation of the pure multiplicative guarantee. No arbitrary OPT
parameter, no infimum of an empty set, and no additive constant. -/
def Approx {D : Type} (E : Environment D) (I : Instance D)
    (ρ : ℝ≥0) (s : Schedule) : Prop :=
  Feasible E I s ∧ ∀ u, Feasible E I u → makespan I.jobs s ≤ ρ * makespan I.jobs u

inductive Mode where
  | nonpreemptive | restart | preemptive
  deriving DecidableEq

structure ParallelJob (m : ℕ) where
  size : ℝ≥0
  speed : Fin m → ℝ≥0

/-- No job runs on two machines at once, including canceled attempts. -/
def SerialProfile (p : Profile) : Prop :=
  p.Pairwise (fun a b => a.hi ≤ b.lo)

noncomputable def work {m : ℕ} (d : ParallelJob m) (p : Profile) : ℝ≥0 :=
  (p.map fun a => (a.hi - a.lo) * ∑ i : Fin m,
    if a.resources = {i.val} then d.speed i else 0).sum

/-- An uninterrupted successful final attempt. Earlier restart attempts are charged
resource time but contribute no surviving work. -/
def successfulAttempt {m : ℕ} (d : ParallelJob m) (a : Slice) : Prop :=
  ∃ i : Fin m, a.resources = {i.val} ∧
    (a.hi - a.lo) * d.speed i = d.size

noncomputable def parallel (m : ℕ) (mode : Mode) : Environment (ParallelJob m) where
  resources := Finset.range m
  progress _ _ := ∅
  legal d p := 0 < d.size ∧ (∀ i, 0 < d.speed i) ∧ SerialProfile p ∧
    (∀ a ∈ p, ∃ i : Fin m, a.resources = {i.val}) ∧
    match mode with
    | .nonpreemptive => ∃ a, p = [a] ∧ successfulAttempt d a
    | .restart => ∃ canceled a, p = canceled ++ [a] ∧ successfulAttempt d a ∧
        ∀ b ∈ canceled, ∃ i : Fin m, b.resources = {i.val} ∧
          (b.hi - b.lo) * d.speed i < d.size
    | .preemptive => work d p = d.size

def identicalJob {m : ℕ} (p : ℝ≥0) : ParallelJob m := ⟨p, fun _ => 1⟩
def uniformJob {m : ℕ} (p : ℝ≥0) (speed : Fin m → ℝ≥0) : ParallelJob m := ⟨p, speed⟩

structure ShopOperation where
  machine : ℕ
  duration : ℝ≥0

structure ShopJob where
  operations : List ShopOperation
  precedes : ℕ → ℕ → Prop

def finishedOperations (d : ShopJob) (p : Profile) : Finset ℕ := by
  classical
  exact ((p.filter fun a => ∃ o, d.operations[a.tag]? = some o ∧
    a.resources = {o.machine} ∧ a.hi - a.lo = o.duration).map Slice.tag).toFinset

/-- Open shops use no precedence pairs; flow/job shops encode their fixed
within-job operation order. The same finite resource interface handles all three. -/
def shop (m : ℕ) : Environment ShopJob where
  resources := Finset.range m
  progress := finishedOperations
  legal d p := d.operations ≠ [] ∧
    (∀ o ∈ d.operations, o.machine < m ∧ 0 < o.duration) ∧
    SerialProfile p ∧ p.length = d.operations.length ∧
    (∀ k < d.operations.length, ∃ a ∈ p, a.tag = k ∧
      ∃ o, d.operations[k]? = some o ∧ a.resources = {o.machine} ∧
        a.hi - a.lo = o.duration) ∧
    (∀ a ∈ p, ∀ b ∈ p, d.precedes a.tag b.tag → a.hi ≤ b.lo)

structure MeshJob where
  size : ℝ≥0
  allowed : Finset (Finset ℕ)

/-- Permitted submeshes (or other static processor subsets) are part of job data. -/
def mesh (resources : Finset ℕ) : Environment MeshJob where
  resources := resources
  progress _ _ := ∅
  legal d p := 0 < d.size ∧ ∃ a, p = [a] ∧
    a.resources ∈ d.allowed ∧ a.hi - a.lo = d.size

end ShmoysOnline.ReleaseDates


