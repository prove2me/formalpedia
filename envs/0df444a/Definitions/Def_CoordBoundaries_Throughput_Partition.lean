-- Prove2me | Definitions.Def_CoordBoundaries_Throughput_Partition
-- name    : CoordBoundaries_Throughput_Partition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:34:56.029301+00:00
-- url     : https://prove2.me/theorems/e079b4f4-791a-490f-b84f-0e95737f49f2
-- title:
--   Blocks, superblocks, eligibility, configurations, crossing boundary edges and the reference schedule of Lemma 2.1
-- statement:
--   Fix an internal loss parameter $\eta=1/q$ with $q\in\mathbb N$.
--
--   A **block partition** $\mathcal B$ of $[0,T)$ is given by integer breakpoints $0=t_0<t_1<\dots<t_\ell=T$; block $B_k=[t_k,t_{k+1})$. A **superblock partition** $\mathcal S$ groups consecutive blocks; it is recorded by a monotone label on blocks, two blocks lying in the same superblock exactly when they carry the same label, and $|\mathcal S|$ is the number of labels. A schedule is **aligned** if each execution lies entirely in one block.
--
--   For a job $j$, its **release block** $B_L(j)$ contains $r_j$, and its **deadline block** $B_R(j)=[s,t)$ satisfies $s<d_j\le t$. A job is **local** if $B_L(j)=B_R(j)$ and **global** otherwise. A local job is **eligible** only in its block; a global job is eligible in its two boundary blocks and in every block of a superblock whose union lies inside $[r_j,d_j)$.
--
--   A **configuration** in block $B$ is a set of at most $K$ jobs eligible in $B$ that has a feasible schedule on the $m$ machines with every execution inside $B$; $\mathcal C(B)$ is the family of configurations (it contains $\emptyset$).
--
--   Two global jobs' **boundary edges cross** when, after possibly exchanging the jobs, their boundary pairs are $(B_u,B_v)$ and $(B_s,B_t)$ with $u<s<v<t$; a family is **noncrossing** if no two of its edges cross.
--
--   A candidate $(\mathcal B,\mathcal S,K)$ is **certified** by a schedule $O'$ if $O'$ is feasible and aligned and
--   1. $|O'|\ge(1-2\eta)\mathrm{OPT}$;
--   2. every execution lies in an eligible block;
--   3. each block contains at most $K$ executions across all machines;
--   4. $|O'|\ge m\Delta|\mathcal B|/\eta$ and $|O'|\ge K|\mathcal S|/\eta^8$.
--
--   Candidates are output by algorithms as the list of breakpoints, labels and $K$.
--
--   **Formalization Note** Block indices are natural numbers: $B_L(j)$ is the number of blocks ending at or before $r_j$, and $B_R(j)$ the number of blocks ending strictly before $d_j$.
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), pp. 8–10, §2.1 (blocks, superblocks, alignment, eligibility), §2.2 (configurations); p. 11 (crossing, noncrossing); p. 9, Lemma 2.1 (a)–(d)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Problem

open Classical

namespace CoordBoundaries.Throughput

/-! # Blocks, superblocks, eligibility and configurations (Tong–Xu, §2.1–§2.2, pp. 8–10)

A partition of `[0, T)` into blocks is given by strictly increasing integer breakpoints
`0 = pt 0 < pt 1 < … < pt len = T`; block `k` is `[pt k, pt (k+1))`. Superblocks are unions of
consecutive blocks, encoded by a monotone label `sb` on blocks (two blocks lie in the same
superblock iff they carry the same label); `|S|` is the number of labels. -/

/-- The internal loss parameter `η = 1/q` (p. 8). -/
noncomputable def eta (q : ℕ) : ℝ := 1 / (q : ℝ)

/-- A block partition `ℬ` of `[0, T)` with a superblock partition `𝒮` (§2.1, p. 8). -/
structure Partition (T : ℕ) where
  len : ℕ
  pt : Fin (len + 1) → ℕ
  pt_mono : StrictMono pt
  pt_zero : pt 0 = 0
  pt_last : pt (Fin.last len) = T
  sb : Fin len → ℕ
  sb_mono : Monotone sb

namespace Partition

variable {I : Instance} (P : Partition I.T)

/-- Left endpoint of block `k`. -/
def lo (k : Fin P.len) : ℕ := P.pt k.castSucc

/-- Right endpoint of block `k`. -/
def hi (k : Fin P.len) : ℕ := P.pt k.succ

/-- The number `|𝒮|` of superblocks. -/
noncomputable def numSuper : ℕ := (Finset.univ.image P.sb).card

/-- Index of the release block `B_L(j)`, the block containing `r_j` (p. 8). -/
noncomputable def BL (j : Fin I.n) : ℕ :=
  (Finset.univ.filter fun k : Fin P.len => P.hi k ≤ I.r j).card

/-- Index of the deadline block `B_R(j) = [s, t)` with `s < d_j ≤ t` (p. 8). -/
noncomputable def BR (j : Fin I.n) : ℕ :=
  (Finset.univ.filter fun k : Fin P.len => P.hi k < I.d j).card

/-- A job is local when its window lies in one block, i.e. `B_L(j) = B_R(j)` (p. 8). -/
def IsLocal (j : Fin I.n) : Prop := P.BL j = P.BR j

/-- A job is global otherwise. -/
def IsGlobal (j : Fin I.n) : Prop := P.BL j ≠ P.BR j

/-- Block `k` lies inside the window `[r_j, d_j)`. -/
def BlockInWindow (j : Fin I.n) (k : Fin P.len) : Prop := I.r j ≤ P.lo k ∧ P.hi k ≤ I.d j

/-- Job `j` spans the superblock containing block `k`. -/
def SpansSuperOf (j : Fin I.n) (k : Fin P.len) : Prop :=
  ∀ k' : Fin P.len, P.sb k' = P.sb k → P.BlockInWindow j k'

/-- Eligibility (p. 8): a local job only in the block containing its window; a global job in its two
boundary blocks and in every block of a superblock it spans. -/
def Eligible (j : Fin I.n) (k : Fin P.len) : Prop :=
  (P.IsLocal j ∧ (k : ℕ) = P.BL j) ∨
  (P.IsGlobal j ∧ ((k : ℕ) = P.BL j ∨ (k : ℕ) = P.BR j ∨ P.SpansSuperOf j k))

/-- An execution of `j` from `S` lies entirely in block `k`. -/
def ExecIn (k : Fin P.len) (j : Fin I.n) (S : ℝ) : Prop :=
  (P.lo k : ℝ) ≤ S ∧ S + I.p j ≤ P.hi k

/-- A schedule is aligned with `ℬ` if each execution lies entirely in one block (p. 8). -/
def Aligned (σ : Sched I) : Prop :=
  ∀ (j : Fin I.n) (i : Fin I.m) (S : ℝ), σ j = some (i, S) → ∃ k, P.ExecIn k j S

/-- `w` is a feasible schedule of exactly the jobs `C`, all executed inside block `k`. -/
def WitnessIn (k : Fin P.len) (C : Finset (Fin I.n)) (w : Sched I) : Prop :=
  Feasible I w ∧ scheduled w = C ∧
    ∀ (j : Fin I.n) (i : Fin I.m) (S : ℝ), w j = some (i, S) → P.ExecIn k j S

/-- A configuration in block `k` (p. 10): a set of at most `K` jobs eligible in `k` that admits a
feasible schedule on the `m` machines entirely inside the block. -/
def IsConfig (K : ℕ) (k : Fin P.len) (C : Finset (Fin I.n)) : Prop :=
  C.card ≤ K ∧ (∀ j ∈ C, P.Eligible j k) ∧ ∃ w, P.WitnessIn k C w

/-- The family `𝒞(B)` of configurations of block `k` (it contains `∅`). -/
noncomputable def configs (K : ℕ) (k : Fin P.len) : Finset (Finset (Fin I.n)) :=
  Finset.univ.filter (P.IsConfig K k)

/-- Two global jobs' boundary edges cross: their boundary pairs strictly interleave (p. 11). -/
def Cross (j k : Fin I.n) : Prop :=
  (P.BL j < P.BL k ∧ P.BL k < P.BR j ∧ P.BR j < P.BR k) ∨
  (P.BL k < P.BL j ∧ P.BL j < P.BR k ∧ P.BR k < P.BR j)

/-- A family of jobs is noncrossing if no two of its boundary edges cross (p. 11). -/
def Noncrossing (J : Finset (Fin I.n)) : Prop := ∀ j ∈ J, ∀ k ∈ J, ¬ P.Cross j k

/-- The reference schedule of Lemma 2.1 (p. 9) for the candidate `(ℬ, 𝒮, K)`: a feasible aligned
schedule `O′` with (a) `|O′| ≥ (1 − 2η) OPT`; (b) every execution in an eligible block; (c) at most
`K` executions per block over all machines; (d) `|O′| ≥ m∆|ℬ|/η` and `|O′| ≥ K|𝒮|/η⁸`. -/
def Certifies (q Δ K : ℕ) (O : Sched I) : Prop :=
  Feasible I O ∧ P.Aligned O ∧
  (1 - 2 * eta q) * (OPT I : ℝ) ≤ ((scheduled O).card : ℝ) ∧
  (∀ (j : Fin I.n) (i : Fin I.m) (S : ℝ), O j = some (i, S) →
      ∃ k, P.ExecIn k j S ∧ P.Eligible j k) ∧
  (∀ k : Fin P.len,
      ((scheduled O).filter fun j => ∃ (i : Fin I.m) (S : ℝ), O j = some (i, S) ∧ P.ExecIn k j S).card
        ≤ K) ∧
  ((I.m : ℝ) * Δ * P.len / eta q ≤ ((scheduled O).card : ℝ) ∧
    (K : ℝ) * P.numSuper / eta q ^ 8 ≤ ((scheduled O).card : ℝ))

end Partition

/-- Encoding of a partition: `[len, pt 0, …, pt len, sb 0, …, sb (len-1)]`. -/
def encPartition {T : ℕ} (P : Partition T) : List ℤ :=
  [(P.len : ℤ)] ++ List.ofFn (fun i => (P.pt i : ℤ)) ++ List.ofFn (fun k => (P.sb k : ℤ))

/-- Encoding of a list of candidates `(ℬ, 𝒮, K)`: the count, then each partition followed by `K`. -/
def encCands {T : ℕ} (cs : List (Partition T × ℕ)) : List ℤ :=
  [(cs.length : ℤ)] ++ cs.flatMap fun c => encPartition c.1 ++ [(c.2 : ℤ)]

end CoordBoundaries.Throughput


