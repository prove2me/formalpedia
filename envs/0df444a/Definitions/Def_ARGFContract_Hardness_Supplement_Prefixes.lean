-- Prove2me | Definitions.Def_ARGFContract_Hardness_Supplement_Prefixes
-- name    : ARGFContract_Hardness_Supplement_Prefixes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:54.873522+00:00
-- url     : https://prove2.me/theorems/aa1d37cd-a995-40c6-919d-11b78d7dc853
-- title:
--   Cost buckets, competency classes, profiles, prefix committees and the factor $\alpha(\Gamma)$
-- statement:
--   Fix agents $E=\{1,\dots,N\}$ with real costs $c_i$ and competencies $p_i$.
--
--   1. **Sorted prefixes.** For a key $k:E\to\mathbb R$, agent $j$ precedes agent $i$ when $k_j<k_i$, or $k_j=k_i$ and $j<i$. The first $x$ agents of $A\subseteq E$ in this order form the prefix of length $x$ (all of $A$ when $x\ge|A|$). With key $c$ this is the set of the $x$ cheapest agents of $A$; with key $-p$ it is the set of the $x$ most competent agents of $A$.
--   2. **Blocks and profiles.** A labelling $\mathrm{lab}:E\to\{1,\dots,m\}$ has blocks $B_a=\{i:\mathrm{lab}(i)=a\}$ (cost buckets, competency classes or clusters). A **profile** is a vector $x=(x_1,\dots,x_m)$ of integers with $0\le x_a\le|B_a|$; the zero profile is included. The profile of a set $S$ is $x(S)=(|S\cap B_1|,\dots,|S\cap B_m|)$ (Definition 3.5).
--   3. **Prefix committees.** $Q_C(x)=\bigcup_t\{\text{the }x_t\text{ most competent experts of }B_t\}$ (§3.1.2) and $S(x)=\bigcup_a\{\text{the }x_a\text{ cheapest agents of }C_a\}$ (Algorithm 7, line 6).
--   4. **Bucket conditions** (Assumption 3.1). The blocks form an $\epsilon$-cost-bucket partition if $|c_i-c_j|\le\epsilon$ whenever $i,j$ share a bucket, and are $\delta$-separated if $|c_i-c_j|\ge\delta$ whenever they do not.
--   5. **Cluster gaps and Assumption B.1.** Clusters $C_a$ have gaps $\epsilon_a$ if $|p_i-p_j|\le\epsilon_a$ for $i,j\in C_a$. Assumption B.1 holds with constant $L$ if $L\ge0$ and $|f(B\cup\{i\})-f(B\cup\{j\})|\le L|p_i-p_j|$ for all distinct $i,j$ and all $B\subseteq E\setminus\{i,j\}$.
--   6. **The factor of Theorem 4.** For $1\le n\le N$ let $S_c^n=\mathrm{Bottom}_n(c)$ be the $n$ cheapest agents and $\mathrm{Top}_n(p)$ the $n$ most competent ones. Then
--
--   $$D=\max_{1\le n\le N}\mu(S_c^n),\qquad U=\max_{1\le n\le N}\Big(f(\mathrm{Top}_n(p))-\sum_{i\in \mathrm{Bottom}_n(c)}c_i\Big),\qquad \alpha(\Gamma)=\frac UD ,$$
--
--   which is (3.12); it is used only when $D>0$.
--
--   These objects describe exactly what Algorithms 2, 3 and 7 enumerate and return.
--
--   **Formalization Note** Ties in the sorted orders are broken by agent index, a deterministic order as the algorithms' sorting steps require. The maxima in $D$ and $U$ are finite maxima over $\{1,\dots,N\}$ and need $N\ge1$, which is an explicit argument. Lean's total division $x/0=0$ is never used: Theorem 4 assumes $D>0$.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, STOC 2027 submission #348 (October 2026), Assumption 3.1 and Definition 3.5 (p. 14), (3.7), (3.9), (3.12) (pp. 20–21), Algorithm 7 (p. 39), gap bound and Assumption B.1 (pp. 40–41)

import Mathlib
import Definitions.Def_ARGFContract_Hardness_Supplement_RealNetUtility

open Finset

namespace ARGFContract.Hardness.Supplement

/-- The deterministic sorted order used by every prefix below: `j` comes strictly before
`i` when its key is smaller, ties broken by the smaller agent index. -/
def precedes {n : ℕ} (key : Fin n → ℝ) (j i : Fin n) : Prop :=
  key j < key i ∨ (key j = key i ∧ j < i)

/-- The first `x` agents of `A` in the order `precedes key`: an agent of `A` is kept when
fewer than `x` agents of `A` precede it. For `x ≤ |A|` this is the set of the `x`
smallest-key agents of `A` (ties by index); for `x ≥ |A|` it is `A`. -/
noncomputable def keyPrefix {n : ℕ} (key : Fin n → ℝ) (A : Finset (Fin n)) (x : ℕ) :
    Finset (Fin n) := by
  classical
  exact A.filter (fun i => (A.filter (fun j => precedes key j i)).card < x)

/-- The `x` cheapest agents of `A` (nondecreasing cost, ties by index). -/
noncomputable def cheapestPrefix {n : ℕ} (c : Fin n → ℝ) (A : Finset (Fin n)) (x : ℕ) :
    Finset (Fin n) :=
  keyPrefix c A x

/-- The `x` most competent agents of `A` (nonincreasing competency, ties by index). -/
noncomputable def competentPrefix {n : ℕ} (p : Fin n → ℝ) (A : Finset (Fin n)) (x : ℕ) :
    Finset (Fin n) :=
  keyPrefix (fun i => -p i) A x

/-- The block `B_t` (cost bucket, competency class or cluster) of a labelling
`lab : E → Fin m` of the agents. -/
def block {n m : ℕ} (lab : Fin n → Fin m) (a : Fin m) : Finset (Fin n) :=
  univ.filter (fun i => lab i = a)

/-- All profiles `x = (x_1,…,x_m)` with integers `0 ≤ x_a ≤ |B_a|` (Algorithm 2, line 4;
Algorithm 7, line 5). The zero profile is included. -/
def profiles {n m : ℕ} (lab : Fin n → Fin m) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun a => range ((block lab a).card + 1))

/-- The cost-bucket profile `x(S) = (|S ∩ B_1|, …, |S ∩ B_m|)` of a set `S`
(Definition 3.5; the cluster profile of Appendix B.3). -/
def blockProfile {n m : ℕ} (lab : Fin n → Fin m) (S : Finset (Fin n)) : Fin m → ℕ :=
  fun a => (S ∩ block lab a).card

/-- The competency prefix `Q_C(x)` of §3.1.2, p. 14: the `x_t` most competent experts of
every bucket `B_t`. -/
noncomputable def competencyPrefixSet {n m : ℕ} (p : Fin n → ℝ) (lab : Fin n → Fin m)
    (x : Fin m → ℕ) : Finset (Fin n) :=
  univ.biUnion (fun t => competentPrefix p (block lab t) (x t))

/-- The set `S(x) = ⋃_a {i_{a,1},…,i_{a,x_a}}` of Algorithm 7, line 6, p. 39: the first
`x_a` agents of every class/cluster `C_a` sorted by nondecreasing cost. -/
noncomputable def cheapestProfileSet {n m : ℕ} (c : Fin n → ℝ) (lab : Fin n → Fin m)
    (x : Fin m → ℕ) : Finset (Fin n) :=
  univ.biUnion (fun a => cheapestPrefix c (block lab a) (x a))

/-- Assumption 3.1, p. 14: the buckets of `lab` form an `ε`-cost-bucket partition,
`max_t max_{i,j∈B_t} |c_i − c_j| ≤ ε`. -/
def IsCostBucketPartition {n m : ℕ} (c : Fin n → ℝ) (lab : Fin n → Fin m) (ε : ℝ) : Prop :=
  ∀ i j, lab i = lab j → |c i - c j| ≤ ε

/-- Assumption 3.1, p. 14: the partition is `δ`-separated,
`min_{i∈B_s, j∈B_t} |c_i − c_j| ≥ δ` for distinct buckets. -/
def IsSeparated {n m : ℕ} (c : Fin n → ℝ) (lab : Fin n → Fin m) (δ : ℝ) : Prop :=
  ∀ i j, lab i ≠ lab j → δ ≤ |c i - c j|

/-- The gap bound of Appendix B.3, pp. 40–41: `|p_i − p_j| ≤ ε_a` for all `i, j ∈ C_a`. -/
def HasCompetencyGaps {n K : ℕ} (p : Fin n → ℝ) (cl : Fin n → Fin K) (ε : Fin K → ℝ) : Prop :=
  ∀ i j, cl i = cl j → |p i - p j| ≤ ε (cl i)

/-- Assumption B.1 (Lipschitz competency), p. 41: `L ≥ 0` and for all distinct `i, j` and
all `B ⊆ E ∖ {i, j}`, `|f(B ∪ {i}) − f(B ∪ {j})| ≤ L |p_i − p_j|`. -/
def LipschitzCompetency {n : ℕ} (L : ℝ) (p : Fin n → ℝ) (f : Finset (Fin n) → ℝ) : Prop :=
  0 ≤ L ∧ ∀ i j : Fin n, i ≠ j → ∀ B : Finset (Fin n), i ∉ B → j ∉ B →
    |f (insert i B) - f (insert j B)| ≤ L * |p i - p j|

/-- `Bottom_c(k) = S_c^k` of (3.7), p. 20: a cheapest `k`-set, read off the cost-sorted list. -/
noncomputable def bottomSet {n : ℕ} (c : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  cheapestPrefix c univ k

/-- `Top_k(p)` of (3.9), p. 21: the `k` agents of highest competency. -/
noncomputable def topSet {n : ℕ} (p : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  competentPrefix p univ k

theorem Icc_one_nonempty {n : ℕ} (hn : 0 < n) : (Icc 1 n).Nonempty :=
  ⟨1, mem_Icc.mpr ⟨le_rfl, hn⟩⟩

/-- The denominator of (3.12), p. 21: `D = max_{1≤k≤N} µ(S_c^k)`. -/
noncomputable def minCostCandidateValue {n : ℕ} (hn : 0 < n) (f : Finset (Fin n) → ℝ)
    (c : Fin n → ℝ) : ℝ :=
  (Icc 1 n).sup' (Icc_one_nonempty hn) (fun k => netUtilityReal f c (bottomSet c k))

/-- The numerator of (3.12), p. 21:
`U = max_{1≤k≤N} ( f(Top_k(p)) − ∑_{i ∈ Bottom_k(c)} c_i )`. -/
noncomputable def topBottomBound {n : ℕ} (hn : 0 < n) (f : Finset (Fin n) → ℝ)
    (p c : Fin n → ℝ) : ℝ :=
  (Icc 1 n).sup' (Icc_one_nonempty hn)
    (fun k => f (topSet p k) - ∑ i ∈ bottomSet c k, c i)

/-- The factor `α(Γ) = U / D` of (3.12), p. 21. It is used only in the regime `D > 0` of the
proof of Theorem 4; Lean's `x / 0 = 0` is never relied upon. -/
noncomputable def alphaGamma {n : ℕ} (hn : 0 < n) (f : Finset (Fin n) → ℝ)
    (p c : Fin n → ℝ) : ℝ :=
  topBottomBound hn f p c / minCostCandidateValue hn f c

end ARGFContract.Hardness.Supplement


