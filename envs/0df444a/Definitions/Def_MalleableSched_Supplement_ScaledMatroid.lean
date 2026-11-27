-- Prove2me | Definitions.Def_MalleableSched_Supplement_ScaledMatroid
-- name    : MalleableSched_Supplement_ScaledMatroid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:40:08.375369+00:00
-- url     : https://prove2.me/theorems/9ba0d7fe-d508-445d-851a-bca70600b098
-- title:
--   Scaled matroid-rank speeds $g_j=r_j/q_j$, $t_j=\lceil q_j/C\rceil$, and the outputs of Steps 1, 2, 3a and 3b of the §3 algorithm
-- statement:
--   These are the objects of §3 of the paper, where every job's speed is a scaled matroid rank. Jobs form a finite set $J$ and machines a finite set $M$; processing times $f_j=1/g_j$, assignments, the maximum load $L(\mathbf S)$ and well-structured assignments are those of the published base model.
--
--   1. A **matroid** on $M$ is a non-empty family $\mathcal F\subseteq 2^M$ such that (i) $T\in\mathcal F$ and $S\subseteq T$ imply $S\in\mathcal F$, and (ii) for $S,T\in\mathcal F$ with $|S|<|T|$ there is $i\in T\setminus S$ with $S\cup\{i\}\in\mathcal F$. Its **rank** is $r(S)=\max\{|T|:T\subseteq S,\ T\in\mathcal F\}$.
--   2. Job $j$ has a matroid $\mathcal F_j$ with rank $r_j$ and a quota $q_j$; its **speed** is $g_j(S)=r_j(S)/q_j$, so $f_j(S)=q_j/r_j(S)$, which is $\infty$ when $r_j(S)=0$.
--   3. For a target load $C>0$ put $t_j=\lceil q_j/C\rceil$, $J_1=\{j:t_j=1\}$ and $J_2=J\setminus J_1$.
--   4. **Step 1's output** $\mathbf S^1$: each $j\in J_1$ on one machine $i^1_j$, with $\sum_{j\in J_1:\,i^1_j=i}f_j(\{i\})\le 2C$ for every machine $i$.
--   5. **Step 2's output** $B\subseteq M\times J_2$: for every $j\in J_2$ the set $\{i:(i,j)\in B\}$ lies in $\mathcal F_j$ and has at most $t_j$ elements ($B\in\mathcal F'$), every machine occurs in at most two pairs ($B\in\mathcal F''$), and
--   $$|B|=\sum_{j\in J_2}t_j.$$
--   6. **Step 3a** returns $S_j=\{i^1_j\}$ for $j\in J_1$ and $S^2_j=\{i:(i,j)\in B\}$ for $j\in J_2$.
--   7. **Step 3b** forms, for each machine $i$, the edge $e_i=\{j:(i,j)\in B\}$ (a loop when $|e_i|=1$) on the node set $J_2$, chooses a head $j_i\in e_i$ for each non-empty $e_i$ so that every $j\in J_2$ is the head of at least $\lfloor t_j/2\rfloor$ edges, and returns $\{i^1_j\}$ for $j\in J_1$ and $\bar S^2_j=\{i:e_i\ne\emptyset,\ j_i=j\}$ for $j\in J_2$.
--
--   These definitions state Theorems 13 and 14, the analysis of the paper's 4-approximation for Assignment and 5-approximation for Scheduling with scaled matroid-rank speeds.
--
--   **Formalization Note** Jobs are `Fin n`, machines `Fin m`, a matroid is a finite set of finite subsets of `Fin m`, and $t_j$ is a natural number. The rank formula on p.4 is printed as $\max_{S\subseteq T:\,S\in\mathcal F}|S|$ with the letters swapped; the definition uses the intended $\max\{|T|:T\subseteq S,\ T\in\mathcal F\}$. Step 1's output is any $\mathbf S^1$ with the stated load bound, not only the one from the rounding of (LP2). A maximum common independent set $B$ for which the algorithm does not stop is exactly a $B\in\mathcal F'\cap\mathcal F''$ with $|B|=\sum_{j\in J_2}t_j$, because every member of $\mathcal F'$ has at most that many elements. An orientation is encoded by an optional head map $h:M\to J\cup\{\mathrm{none}\}$ that is `some j_i` on every non-empty edge; its values on machines with $e_i=\emptyset$ are ignored. This partial-map encoding includes the empty job set.
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, §1.2 p.4 (matroids, rank, scaled matroid rank); §3 p.10 (gⱼ = rⱼ/qⱼ, tⱼ, J1, J2); §3.1 p.11 (Steps 1, 2, 3a, F′, F″); §3.1 p.12 (Step 3b)

import Mathlib
import Definitions.Def_MalleableSched_Model

open scoped ENNReal

namespace MalleableSched.Supplement

/-- **Matroid on the machine set.**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs under
Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, §1.2, p.4: "A matroid on the
ground set M is a non-empty set family F ⊆ 2^M such that (i) T ∈ F implies S ∈ F for all S ⊆ T and
(ii) for every S, T ∈ F with |S| < |T| there is an i ∈ T \ S such that S ∪ {i} ∈ F."

**Formalization Note.** The ground set `M` is `Fin m`; the family `F` is a finite set of subsets
of `Fin m` (so `F ⊆ 2^M` is automatic). The three clauses are exactly the paper's: `F` non-empty,
(i) closure under subsets, (ii) the augmentation property. -/
def IsMatroid {m : ℕ} (F : Finset (Finset (Fin m))) : Prop :=
  F.Nonempty ∧
    (∀ T ∈ F, ∀ S : Finset (Fin m), S ⊆ T → S ∈ F) ∧
    (∀ S ∈ F, ∀ T ∈ F, S.card < T.card → ∃ i ∈ T \ S, insert i S ∈ F)

/-- **Rank function `r(S)` of a set family.**
arXiv:2111.06225v2, §1.2, p.4: "The rank function of a matroid F is defined by
r(S) := max_{S⊆T:S∈F} |S| for S ⊆ M." The quantifier letters are swapped in print; the rank of `S`
is the largest size of a member of `F` contained in `S`: `r(S) = max {|T| : T ⊆ S, T ∈ F}`.

**Formalization Note.** Computed as the `Finset.sup` of the cardinalities of the members of `F`
inside `S` (a natural number). For a matroid `∅ ∈ F`, so the maximum is over a non-empty set; the
`sup` would be `0` if no member of `F` were inside `S`. -/
def rank {m : ℕ} (F : Finset (Finset (Fin m))) (S : Finset (Fin m)) : ℕ :=
  (S.powerset.filter (fun T => T ∈ F)).sup Finset.card

/-- **Scaled matroid-rank speeds `g_j(S) = r_j(S)/q_j`.**
arXiv:2111.06225v2, §3, p.10: "each job j ∈ J is associated with a matroid F_j on M and a quota
q_j ∈ R≥0. The processing speed function for job j ∈ J is defined by g_j(S) := r_j(S)/q_j, where
r_j is the rank function of F_j."

**Formalization Note.** Jobs are `Fin n`, machines `Fin m`. The value is a real number; the
theorems that use it assume `q_j > 0`, so the processing time of the base model,
`procTime (matroidSpeed F q) j S = (ENNReal.ofReal (r_j(S)/q_j))⁻¹`, is `q_j / r_j(S)` and is `∞`
when `r_j(S) = 0`. -/
noncomputable def matroidSpeed {n m : ℕ} (F : Fin n → Finset (Finset (Fin m))) (q : Fin n → ℝ) :
    Fin n → Finset (Fin m) → ℝ :=
  fun j S => (rank (F j) S : ℝ) / q j

/-- **The numbers `t_j = ⌈q_j/C⌉`.** arXiv:2111.06225v2, §3.1, p.10: "define tj := ⌈qj/C⌉ for all
j ∈ J as well as J1 := {j ∈ J : tj = 1} and J2 := J \ J1."

**Formalization Note.** `t_j` is the natural number `⌈q_j/C⌉₊`. The job classes are not separate
definitions: `j ∈ J1` is written `t j = 1` and `j ∈ J2` is written `t j ≠ 1`. -/
noncomputable def quotaCount {n : ℕ} (q : Fin n → ℝ) (C : ℝ) (j : Fin n) : ℕ :=
  ⌈q j / C⌉₊

/-- **The machines of job `j` in a set of machine–job pairs:** `{i ∈ M : (i, j) ∈ B}`
(arXiv:2111.06225v2, §3.1, p.11, in the definition of `F′` and `S²_j := {i ∈ M : (i, j) ∈ B}`). -/
def jobSlice {n m : ℕ} (B : Finset (Fin m × Fin n)) (j : Fin n) : Finset (Fin m) :=
  (B.filter (fun p => p.2 = j)).image Prod.fst

/-- **The jobs of machine `i` in a set of machine–job pairs:** `e_i := {j ∈ J2 : (i, j) ∈ B}`
(arXiv:2111.06225v2, §3.1, p.12; also the set counted in `F″`, p.11).

**Formalization Note.** For a `B ⊆ M × J2` (as in Step 2) this is the paper's `e_i`; the
restriction to `J2` is part of the Step 2 hypothesis `IsStep2Output`. -/
def machineEdge {n m : ℕ} (B : Finset (Fin m × Fin n)) (i : Fin m) : Finset (Fin n) :=
  (B.filter (fun p => p.1 = i)).image Prod.snd

/-- **Step 1's output `S¹`.** arXiv:2111.06225v2, §3.1, p.11: "If the LP is feasible, we obtain an
assignment S¹ for the jobs in J1 with maximum load at most 2C using the rounding algorithm of
Lenstra et al. (1990)".

`S¹` puts each job `j ∈ J1` (`t j = 1`) on the single machine `i1 j`, and every machine `i` carries
load `Σ_{j ∈ J1 : i1 j = i} f_j({i}) ≤ 2C`.

**Formalization Note.** `i1 : Fin n → Fin m`; its values on jobs outside `J1` are ignored. Loads are
measured with the processing times `f_j = procTime g j` of the base model (in `ℝ≥0∞`), so a job on
a machine of speed `0` contributes `∞` and violates the bound. Every `S¹` with this property is
admitted, not only the one produced by the rounding of (LP2). -/
def IsStep1Output {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ) (t : Fin n → ℕ)
    (i1 : Fin n → Fin m) (C : ℝ) : Prop :=
  ∀ i : Fin m,
    ∑ j ∈ Finset.univ.filter (fun j => t j = 1 ∧ i1 j = i), procTime g j {i} ≤ ENNReal.ofReal (2 * C)

/-- **Step 2's output `B`.** arXiv:2111.06225v2, §3.1, p.11:
"F′ := {S ⊆ M × J2 : {i ∈ M : (i, j) ∈ S} ∈ Fj and |{i ∈ M : (i, j) ∈ S}| ≤ tj for all j ∈ J2}",
"F′′ := {S ⊆ M × J2 : |{j ∈ J2 : (i, j) ∈ S}| ≤ 2 for all i ∈ M}", "Let B be a maximum
cardinality common independent set in F′ ∩ F′′ … If |B| < Σ_{j∈J2} tj, then … stop the algorithm."

`B` is a set of machine–job pairs with:
1. every pair `(i, j) ∈ B` has `j ∈ J2` (`B ⊆ M × J2`);
2. for every `j ∈ J2`, `{i : (i, j) ∈ B}` is independent in `F_j` and has at most `t_j` elements
   (`B ∈ F′`);
3. every machine lies in at most two pairs of `B` (`B ∈ F″`);
4. `|B| = Σ_{j ∈ J2} t_j`.

**Formalization Note.** Every member of `F′` has at most `Σ_{j∈J2} t_j` elements, so "B is a
maximum common independent set and the algorithm does not stop" (`|B| ≥ Σ_{j∈J2} t_j`) is the same
as "B ∈ F′ ∩ F″ and `|B| = Σ_{j∈J2} t_j`", which is what is stated. `J2` is `{j | t j ≠ 1}`. -/
def IsStep2Output {n m : ℕ} (F : Fin n → Finset (Finset (Fin m))) (t : Fin n → ℕ)
    (B : Finset (Fin m × Fin n)) : Prop :=
  (∀ p ∈ B, t p.2 ≠ 1) ∧
    (∀ j : Fin n, t j ≠ 1 → jobSlice B j ∈ F j ∧ (jobSlice B j).card ≤ t j) ∧
    (∀ i : Fin m, (machineEdge B i).card ≤ 2) ∧
    B.card = ∑ j ∈ Finset.univ.filter (fun j => t j ≠ 1), t j

/-- **Step 3a: the merged assignment.** arXiv:2111.06225v2, §3.1, p.11: "it combines the two
assignments S¹ and S² into an assignment for all jobs in J and returns this assignment", with
"S²_j := {i ∈ M : (i, j) ∈ B}".

Job `j ∈ J1` gets `{i1 j}`; job `j ∈ J2` gets `{i : (i, j) ∈ B}`. -/
def step3aAssignment {n m : ℕ} (t : Fin n → ℕ) (i1 : Fin n → Fin m)
    (B : Finset (Fin m × Fin n)) : Fin n → Finset (Fin m) :=
  fun j => if t j = 1 then {i1 j} else jobSlice B j

/-- **Step 3b: the orientation `D` of `G = (J2, E)`.** arXiv:2111.06225v2, §3.1, p.12: "the set
E := {e_i : i ∈ M, e_i ≠ ∅} can be interpreted as a set of edges on the node set J2, where we
interpret possible singletons e_i = {j} as self-loops of the node j. … we can compute an orientation
D of G in which every node has in-degree at least ⌊tj/2⌋. Let ji ∈ J2 be the head node of the
directed arc in the orientation D that corresponds to undirected edge ei ∈ E."

An orientation is given by an optional head map `h : Fin m → Option (Fin n)`: the edge `e_i` (one
edge per machine `i` with `e_i ≠ ∅`) is directed into `j_i ∈ e_i` with `h i = some j_i`. The
in-degree of `j` is the number of machines `i` with `e_i ≠ ∅` and `h i = some j`; it must be at
least `⌊t_j/2⌋` for every `j ∈ J2`.

**Formalization Note.** Distinct machines with the same `e_i` give parallel edges (each is its own
edge, indexed by `i`); a loop `e_i = {j}` has head `j`. Optional heads encode that the source only
chooses a head for a non-empty edge, and also cover the empty job set; the values of `h` on machines
with `e_i = ∅` are ignored. `⌊t_j/2⌋` is natural-number division `t j / 2`. -/
def IsStep3bOrientation {n m : ℕ} (t : Fin n → ℕ) (B : Finset (Fin m × Fin n))
    (h : Fin m → Option (Fin n)) : Prop :=
  (∀ i : Fin m, (machineEdge B i).Nonempty →
      ∃ j ∈ machineEdge B i, h i = some j) ∧
    ∀ j : Fin n, t j ≠ 1 →
      t j / 2 ≤ (Finset.univ.filter (fun i => (machineEdge B i).Nonempty ∧ h i = some j)).card

/-- **Step 3b: the returned assignment.** arXiv:2111.06225v2, §3.1, p.12: "Let B̄ := {(i, ji) :
i ∈ M, ei ≠ ∅}. … S̄² defined by S̄²_j := {i ∈ M : (i, j) ∈ B̄} … Because every job in J1 is assigned
to a single machine in S¹, combining S¹ and S² yields a well-structured assignment" (the combined
assignment is `S¹` on `J1` and `S̄²` on `J2`).

Job `j ∈ J1` gets `{i1 j}`; job `j ∈ J2` gets `S̄²_j = {i : e_i ≠ ∅ ∧ h i = some j}`. -/
def step3bAssignment {n m : ℕ} (t : Fin n → ℕ) (i1 : Fin n → Fin m)
    (B : Finset (Fin m × Fin n)) (h : Fin m → Option (Fin n)) : Fin n → Finset (Fin m) :=
  fun j => if t j = 1 then {i1 j} else
    Finset.univ.filter (fun i => (machineEdge B i).Nonempty ∧ h i = some j)

end MalleableSched.Supplement


