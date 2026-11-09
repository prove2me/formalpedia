-- Prove2me | Definitions.Def_BatchedFacilityLocation_Nonuniform_Model
-- name    : BatchedFacilityLocation_Nonuniform_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:09:34.547225+00:00
-- url     : https://prove2.me/theorems/298561d7-707f-4d14-aace-505fb6e0fa75
-- title:
--   Batched facility-location instances, comparison solutions, rounded costs and levels
-- statement:
--   This file fixes the setting of §1, §2 and §4.1.
--
--   **Sites and costs.** The permitted facility sites form a finite metric space $(S,d)$, known in advance together with opening costs $f:S\to\mathbb R$; every theorem assumes $f(y)>0$ for all $y$. For a finite set $A\subseteq S$, $d(x,A)=\min_{y\in A}d(x,y)$, with the convention $d(x,\emptyset)=\infty$; it is valued in $[0,\infty]$.
--
--   **Instances.** An instance consists of $n$ client occurrences, client $i$ located at the permitted site $\mathrm{loc}(i)\in S$ (distinct clients may share a site, so clients form a multiset), and a partition into $B$ batches given by $\mathrm{batch}:\{1,\dots,n\}\to\{1,\dots,B\}$. An instance is *valid* when $B\ge 1$ and every batch is nonempty ($\mathrm{batch}$ is surjective); then $1\le B\le n$.
--
--   **Comparison solutions.** A comparison solution assigns each client $i$ to a site $a(i)$. Its connection cost is $\mathrm{conn}(a)=\sum_i d(\mathrm{loc}(i),a(i))$, its opening cost is $\mathrm{open}(a)=\sum_{c\in a(\{1,\dots,n\})}f(c)$, and $\mathrm{OPT}=\min_a(\mathrm{conn}(a)+\mathrm{open}(a))$. For a center $c$ and a set $C$ of clients, $\mathrm{conn}(C)=\sum_{v\in C}d(c,v)$.
--
--   **Rounding and levels.** $\hat f(y)=2^{\lceil\log_2 f(y)\rceil}$ is the least integer power of two with $f(y)\le\hat f(y)$, so $f(y)\le\hat f(y)<2f(y)$. The distinct values $f_1<\dots<f_m$ of $\hat f$ are the levels; a level is identified with its rounded cost $f_j$. For each level, $M_j=\{y:\hat f(y)\le f_j\}$ and $M_{j-1}=\{y:\hat f(y)<f_j\}$, which is empty for $j=1$, so that $d_v^{(j)}=d(v,M_j)$ and $d_v^{(0)}=\infty$.
--
--   **Lotteries.** Each client carries one lottery value $U_v^{(j)}$ per level; all lottery values are i.i.d. uniform on $[0,1]$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Distances to sets are `Metric.infEDist` in $[0,\infty]$; the uniform law is Lebesgue measure restricted to $[0,1]$.
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), §1 p. 1–2 (model), §2 p. 7 (notation, batches, comparison solutions), §4.1 p. 13 (rounding, levels, M_j, d_v^(j))

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

noncomputable section

open Classical

/-! # The instance, comparison solutions, rounded costs and levels

Grandoni–Leonardi–Russo, *Metric Facility Location under Batched Random Order*,
STOC 2027 submission #212, §1 (p. 1–2), §2 (p. 7), §4.1 (p. 13).

The permitted facility sites form a finite metric space `S` (known in advance, together with
the opening costs `f : S → ℝ`, assumed positive). Clients are a multiset of `n` occurrences,
each located at a permitted site; an oblivious adversary partitions them into `B` nonempty
batches. -/

/-- A batched instance over the site space `S`: `n` client occurrences, client `i` located at
the permitted site `loc i` (not necessarily injective: clients form a multiset), and the
adversary's partition into `B` batches, client `i` belonging to batch `batch i`. -/
structure Instance (S : Type*) where
  n : ℕ
  B : ℕ
  loc : Fin n → S
  batch : Fin n → Fin B

/-- The paper's standing assumptions on the batches (§2, p. 7): `1 ≤ B` and every batch is
nonempty. These imply `n ≥ 1` and `B ≤ n`. -/
structure Instance.Valid {S : Type*} (I : Instance S) : Prop where
  one_le_B : 1 ≤ I.B
  batch_surjective : Function.Surjective I.batch

variable {S : Type*} [Fintype S] [MetricSpace S]

/-! ## Distances to sets, with `d(x, ∅) = ∞` (§2, p. 7) -/

/-- `d(x, A) = min_{y ∈ A} d(x, y)`, with `d(x, ∅) = ∞`, as an extended nonnegative real. -/
def dset (x : S) (A : Finset S) : ℝ≥0∞ := Metric.infEDist x (A : Set S)

/-! ## Comparison solutions (§2, p. 7) -/

/-- Connection cost `Σ_i d(loc i, a i)` of a comparison solution `a` assigning every client
to a site. -/
def connCost {n : ℕ} (loc : Fin n → S) (a : Fin n → S) : ℝ :=
  ∑ i, dist (loc i) (a i)

/-- Opening cost `Σ_{c ∈ a(clients)} f(c)` of a comparison solution `a` (each used site is
opened once). -/
def openCost (f : S → ℝ) {n : ℕ} (a : Fin n → S) : ℝ :=
  ∑ c ∈ Finset.univ.image a, f c

/-- The offline optimum `OPT = min_a (conn(a) + open(a))` over all comparison solutions. -/
def OPT (f : S → ℝ) {n : ℕ} (loc : Fin n → S) : ℝ≥0∞ :=
  ⨅ a : Fin n → S, ENNReal.ofReal (connCost loc a + openCost f a)

/-- `conn(C) = Σ_{v ∈ C} d(c, v)` for a set `C` of clients and a center `c` (§2, p. 7). -/
def connC {n : ℕ} (loc : Fin n → S) (c : S) (C : Finset (Fin n)) : ℝ :=
  ∑ i ∈ C, dist c (loc i)

/-! ## Rounded costs and levels (§4.1, p. 13) -/

/-- `f̂(y)`: the least power of two (integer exponent, possibly negative) that is at least
`f(y)`; for `f(y) > 0` it satisfies `f(y) ≤ f̂(y) < 2 f(y)`. -/
def fhat (f : S → ℝ) (y : S) : ℝ := (2 : ℝ) ^ (⌈Real.logb 2 (f y)⌉)

/-- The distinct rounded costs `f_1 < ⋯ < f_m`, as a finite set of reals. A level is
identified with its rounded cost. -/
def levels (f : S → ℝ) : Finset ℝ := Finset.univ.image (fhat f)

/-- The type of levels `j ∈ {1, …, m}`, each identified with its rounded cost `f_j`. -/
abbrev Lev (f : S → ℝ) := {t : ℝ // t ∈ levels f}

/-- `M_j = {y : f̂(y) ≤ f_j}` for the level of rounded cost `t = f_j`. -/
def Mset (f : S → ℝ) (t : ℝ) : Finset S := Finset.univ.filter (fun y => fhat f y ≤ t)

/-- `M_{j-1} = {y : f̂(y) < f_j}` (the sites of strictly cheaper levels); it is empty at the
first level, so `d(v, M_{j-1}) = d_v^{(0)} = ∞` there. -/
def MsetLt (f : S → ℝ) (t : ℝ) : Finset S := Finset.univ.filter (fun y => fhat f y < t)

/-! ## The lottery variables -/

/-- Uniform law on `[0,1]`. -/
def unif01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Law of one client's lottery vector `(U^{(j)})_j`: i.i.d. uniform on `[0,1]`, one per level. -/
def stepLaw (f : S → ℝ) : Measure (Lev f → ℝ) :=
  Measure.pi fun _ : Lev f => unif01

/-- Law of the lottery array `(U_v^{(j)})_{v ∈ ι, j}`: i.i.d. uniform on `[0,1]`. -/
def lotteryLaw (f : S → ℝ) (ι : Type*) [Fintype ι] : Measure (ι → Lev f → ℝ) :=
  Measure.pi fun _ : ι => stepLaw f

end

end BatchedFacilityLocation.Nonuniform


