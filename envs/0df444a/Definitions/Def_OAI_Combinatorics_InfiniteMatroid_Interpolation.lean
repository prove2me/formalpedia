-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
-- name    : OAI_Combinatorics_InfiniteMatroid_Interpolation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:12.173359+00:00
-- url     : https://prove2.me/theorems/8f61a459-4697-4484-8652-9b5a433e18d8
-- title:
--   Interpolation for lower limits of set-function sequences on an interval of sets
-- statement:
--   This file develops an abstract intermediate-value principle for lower limits of a sequence of set functions. Throughout, $f=(f_n)_{n\in\mathbb N}$ is a sequence of real-valued functions on the subsets of a set $\Omega$. The continuity-based part takes $\Omega=\mathbb N$; the lower-limit notions and the finite-rounding results work for an arbitrary $\Omega$. For $I,Y\subseteq\Omega$ the *interval* $[I,Y]$ is the family of sets $X$ with $I\subseteq X\subseteq Y$.
--
--   1. **Agreement below $m$.** Sets $X,Z\subseteq\mathbb N$ agree below $m$ if $x\in X\iff x\in Z$ for every $x<m$.
--   2. **Cylinder continuity.** For $I,Y\subseteq\mathbb N$, $f$ is cylinder-continuous on $[I,Y]$ if for every $j\in\mathbb N$ and every $\varepsilon>0$ there is $m$ such that
--   $$X,Z\in[I,Y]\ \text{agree below}\ m\quad\Longrightarrow\quad |f_n(X)-f_n(Z)|<\varepsilon\ \text{ for all } n<j .$$
--   In other words, each $f_n$ is uniformly continuous on $[I,Y]$ for the product topology on the subsets of $\mathbb N$.
--   3. **Deletion sets.** For $I,X\subseteq\mathbb N$ and $m,k\in\mathbb N$,
--   $$\mathrm{Del}_{m,k}(X)=\{x\in X:\ x\in I\ \text{or}\ x<m\ \text{or}\ x\ge k\},\qquad \mathrm{Del}_{m}(X)=\{x\in X:\ x\in I\ \text{or}\ x<m\}$$
--   (both depend on $I$). Thus $\mathrm{Del}_{m,k}$ removes from $X$ the labels in $[m,k)$ that are not in $I$, and $\mathrm{Del}_m$ removes all labels $\ge m$ that are not in $I$. The file records that $\mathrm{Del}_{m,0}(X)=X$; that $\mathrm{Del}_{m,k}(X)\subseteq X$ is decreasing in $k$, contains $I$ when $I\subseteq X$, misses only finitely many elements of $X$, agrees with $X$ below $m$ and with $\mathrm{Del}_m(X)$ below $k$; that $\mathrm{Del}_{m,k}(X)\subseteq\mathrm{Del}_{m,k+1}(X)\cup\{k\}$; and that $I\subseteq\mathrm{Del}_m(X)\subseteq X$ for $I\subseteq X$, with $\mathrm{Del}_m(X)\setminus I$ finite.
--   4. **Lower limit.** $\underline f(X)=\liminf_{n\to\infty}f_n(X)$, taken in the extended reals $[-\infty,+\infty]$.
--   5. **Lower basis.** $X$ is a lower basis for $f$ if $-1<\underline f(X)\le0$.
--   6. **Finite shift property.** $f$ has the finite shift property on $[I,Y]$ if
--   $$\underline f(B)=\underline f(A)+|B\setminus A|\qquad\text{for all } A\subseteq B \text{ in } [I,Y] \text{ with } B\setminus A \text{ finite}.$$
--
--   For $I\subseteq Y\subseteq\mathbb N$ consider the conditions: (C) $f$ is cylinder-continuous on $[I,Y]$; (M) $f_n(A)\le f_n(B)$ for all $n$ and all $A\subseteq B$ in $[I,Y]$; (U) $f_n(B)\le f_n(A)+1$ for all $n$ and all $A\subseteq B$ in $[I,Y]$ such that $B\subseteq A\cup\{e\}$ for some $e$. The file proves:
--
--   - *Lower-limit calculus.* $\liminf_n(u_n+b)=\liminf_n u_n+b$ for every sequence $(u_n)$ in $[-\infty,+\infty]$ and every real $b$; hence, if $f_n(Y)=f_n(X)+b$ for all large $n$, then $\underline f(Y)=\underline f(X)+b$. If $f_n(X)\le0$ for infinitely many $n$, then $\underline f(X)\le0$; if for every $\varepsilon>0$ eventually $f_n(X)\ge-1-\varepsilon$, then $\underline f(X)\ge-1$.
--   - *Decreasing limits.* A decreasing sequence $X_0\supseteq X_1\supseteq\cdots$ of subsets of $\mathbb N$ eventually agrees below any fixed $m$ with $\bigcap_jX_j$. Consequently, under (C) and if every $X_j$ lies in $[I,Y]$, $f_n(X_j)\to f_n\bigl(\bigcap_jX_j\bigr)$ for every $n$.
--   - *Deletion stage.* Assume (C), (U), and that every $Z\in[I,Y]$ with $Z\setminus I$ finite has $f_n(Z)<0$ for infinitely many $n$. Then for every $X\in[I,Y]$, $j\in\mathbb N$ and $\varepsilon>0$ there is $Z$ with $I\subseteq Z\subseteq X$, $X\setminus Z$ finite, $f_n(Z)\le0$ for some $n\ge j$, $|f_n(X)-f_n(Z)|<\varepsilon$ for all $n<j$, and either $Z=X$ or $f_n(Z)\ge-1$ for all $n\ge j$.
--   - *Infinite-endpoint interpolation.* Assume $I\subseteq Y$, (C), (M), (U), the hypothesis of the deletion stage, and $f_n(Y)>0$ for all large $n$. Then some $Z\in[I,Y]$ has $f_n(Z)\le0$ for infinitely many $n$ and, for every $\varepsilon>0$, $f_n(Z)\ge-1-\varepsilon$ for all large $n$. In lower-limit form: if $I\subseteq Y$, (C), (M), (U) hold, $\underline f(Z)=-\infty$ for every $Z\in[I,Y]$ with $Z\setminus I$ finite, and $\underline f(Y)>0$, then some $Z\in[I,Y]$ has $-1\le\underline f(Z)\le0$.
--   - *Finite rounding* (arbitrary $\Omega$, $I\subseteq Y$, finite shift property on $[I,Y]$, $\underline f(Y)>0$). If $-\infty<\underline f(I)\le-1$, or if $\underline f(I)=-\infty$ and $\underline f(Y)<+\infty$, then $[I,Y]$ contains a lower basis for $f$.
--
--   The main result combines these cases.
--
--   **Local interpolation.** Let $I\subseteq Y\subseteq\mathbb N$, and suppose that $f$ satisfies (C), (M), (U) and the finite shift property on $[I,Y]$. If $\underline f(I)\le-1$ and $\underline f(Y)>0$, then there is a set $B$ with
--   $$I\subseteq B\subseteq Y\qquad\text{and}\qquad -1<\underline f(B)\le0 .$$
--
--   Applied to the block-density probes $\phi^T_n$ (transported to $\mathbb N$ through an enumeration of the countable ground set $E_0$), this is the intermediate-value step behind the lower local rule $\mathcal L_0(T)=\{X:\ X\triangle T\ \text{small},\ -1<\liminf_n\phi^T_n(X)\le0\}$: it shows that $\mathcal L_0(T)$ meets an interval $[I,Y]$ inside the class of $T$ as soon as the probe lower limit is at most $-1$ at $I$ and positive at $Y$.
--
--   **Formalization Note** The set functions are `f : ℕ → Set ℕ → ℝ` (or `ℕ → Set α → ℝ` for the lower-limit lemmas and for `finite_lower_interpolation` and `finite_upper_interpolation`), and `probeLiminf f X` is `Filter.liminf` of `(f n X : EReal)` along `atTop`. The definitions are `AgreeBelow`, `CylinderContinuous`, `deletePrefix I X m k` (the set $\mathrm{Del}_{m,k}(X)$), `deleteTail I X m` (the set $\mathrm{Del}_m(X)$), `probeLiminf`, `LowerBasis` and `IntervalFiniteShift` (with the cardinality `ncard` cast to `EReal`). The main lemmas are `deletion_stage`, `antitone_agree_iInter`, `CylinderContinuous.tendsto_iInter`, `infinite_endpoint_interpolation`, `infinite_endpoint_liminf_interpolation`, `finite_lower_interpolation`, `finite_upper_interpolation` and `local_interpolation`; the lower-limit calculus consists of `ereal_liminf_add_real`, `probeLiminf_finite_change`, `probeLiminf_le_zero` and `probeLiminf_ge_neg_one`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Interpolation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Interpolation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroid mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation

namespace OAI

section

open Set Filter
open scoped Topology

namespace InfiniteMatroidCounterexample

/-- Two subsets of ℕ agree on the first `m` labels. -/
def AgreeBelow (X Y : Set ℕ) (m : ℕ) : Prop :=
  ∀ x < m, (x ∈ X ↔ x ∈ Y)

def CylinderContinuous (f : ℕ → Set ℕ → ℝ) (I Y : Set ℕ) : Prop :=
  ∀ j ε, 0 < ε → ∃ m, ∀ X Z,
    I ⊆ X → X ⊆ Y → I ⊆ Z → Z ⊆ Y → AgreeBelow X Z m →
    ∀ n < j, |f n X - f n Z| < ε

/-- Delete, in the usual order of ℕ, the labels not reserved by the
lower endpoint or by the finite prefix. -/
def deletePrefix (I X : Set ℕ) (m k : ℕ) : Set ℕ :=
  {x | x ∈ X ∧ (x ∈ I ∨ x < m ∨ k ≤ x)}

lemma deletePrefix_zero (I X : Set ℕ) (m : ℕ) : deletePrefix I X m 0 = X := by
  ext x
  simp [deletePrefix]

lemma subset_deletePrefix {I X : Set ℕ} (hIX : I ⊆ X) (m k : ℕ) :
    I ⊆ deletePrefix I X m k := by
  intro x hx
  exact ⟨hIX hx, Or.inl hx⟩

lemma deletePrefix_subset (I X : Set ℕ) (m k : ℕ) :
    deletePrefix I X m k ⊆ X := fun _ h ↦ h.1

lemma deletePrefix_antitone (I X : Set ℕ) (m : ℕ) :
    Antitone (deletePrefix I X m) := by
  intro a b hab x hx
  rcases hx with ⟨hx, hi | hm | hb⟩
  · exact ⟨hx, Or.inl hi⟩
  · exact ⟨hx, Or.inr (Or.inl hm)⟩
  · exact ⟨hx, Or.inr (Or.inr (hab.trans hb))⟩

lemma deletePrefix_agree (I X : Set ℕ) (m k : ℕ) :
    AgreeBelow X (deletePrefix I X m k) m := by
  intro x hx
  exact ⟨fun h ↦ ⟨h, Or.inr (Or.inl hx)⟩, fun h ↦ h.1⟩

lemma deletePrefix_step (I X : Set ℕ) (m k : ℕ) :
    deletePrefix I X m k ⊆ insert k (deletePrefix I X m (k+1)) := by
  intro x hx
  by_cases h : x = k
  · exact Or.inl h
  · right
    refine ⟨hx.1, ?_⟩
    rcases hx.2 with hi | hm | hk
    · exact Or.inl hi
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (by omega))

lemma deletePrefix_finite (I X : Set ℕ) (m k : ℕ) :
    (X \ deletePrefix I X m k).Finite := by
  apply (finite_Iio k).subset
  intro x hx
  simp only [mem_Iio]
  by_contra hn
  exact hx.2 ⟨hx.1, Or.inr (Or.inr (by omega))⟩

/-- The limit after every eligible label has been deleted. -/
def deleteTail (I X : Set ℕ) (m : ℕ) : Set ℕ :=
  {x | x ∈ X ∧ (x ∈ I ∨ x < m)}

lemma subset_deleteTail {I X : Set ℕ} (hIX : I ⊆ X) (m : ℕ) :
    I ⊆ deleteTail I X m := fun _ hx ↦ ⟨hIX hx, Or.inl hx⟩

lemma deleteTail_subset (I X : Set ℕ) (m : ℕ) :
    deleteTail I X m ⊆ X := fun _ h ↦ h.1

lemma deleteTail_finite (I X : Set ℕ) (m : ℕ) :
    (deleteTail I X m \ I).Finite := by
  apply (finite_Iio m).subset
  intro x hx
  exact hx.1.2.resolve_left hx.2

lemma deletePrefix_agree_tail (I X : Set ℕ) (m k : ℕ) :
    AgreeBelow (deletePrefix I X m k) (deleteTail I X m) k := by
  intro x hx
  constructor
  · rintro ⟨hX, hi | hm | hk⟩
    · exact ⟨hX, Or.inl hi⟩
    · exact ⟨hX, Or.inr hm⟩
    · omega
  · rintro ⟨hX, hi | hm⟩
    · exact ⟨hX, Or.inl hi⟩
    · exact ⟨hX, Or.inr (Or.inl hm)⟩

/-- One stage of the infinite-endpoint interpolation: the stopping time
is finite, all late probes are reset above -1, and earlier probes lose
less than the prescribed tolerance. -/
lemma deletion_stage
    {f : ℕ → Set ℕ → ℝ} {I Y X : Set ℕ}
    (hcc : CylinderContinuous f I Y)
    (hone : ∀ n A B, I ⊆ A → A ⊆ B → B ⊆ Y →
      (∃ e, B ⊆ insert e A) → f n B ≤ f n A + 1)
    (hlow : ∀ Z, I ⊆ Z → Z ⊆ Y → (Z \ I).Finite →
      ∀ j, ∃ n ≥ j, f n Z < 0)
    (hIX : I ⊆ X) (hXY : X ⊆ Y) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Z, I ⊆ Z ∧ Z ⊆ X ∧ (X \ Z).Finite ∧
      (∃ n ≥ j, f n Z ≤ 0) ∧
      (∀ n < j, |f n X - f n Z| < ε) ∧
      (Z = X ∨ ∀ n ≥ j, -1 ≤ f n Z) := by
  classical
  by_cases hex : ∃ n ≥ j, f n X ≤ 0
  · refine ⟨X, hIX, Subset.rfl, ?_, hex, ?_, Or.inl rfl⟩
    · simp
    · intro n hn
      simpa using hε
  have hpos : ∀ n ≥ j, 0 < f n X := by
    intro n hn
    exact lt_of_not_ge (fun h ↦ hex ⟨n, hn, h⟩)
  obtain ⟨m, hm⟩ := hcc j ε hε
  let T := deleteTail I X m
  have hIT : I ⊆ T := subset_deleteTail hIX m
  have hTY : T ⊆ Y := (deleteTail_subset I X m).trans hXY
  obtain ⟨n, hnj, hn⟩ := hlow T hIT hTY (deleteTail_finite I X m) j
  obtain ⟨k, hk⟩ := hcc (n+1) (-f n T) (neg_pos.mpr hn)
  have happrox := hk (deletePrefix I X m k) T (subset_deletePrefix hIX m k)
    ((deletePrefix_subset I X m k).trans hXY) hIT hTY
    (deletePrefix_agree_tail I X m k) n (Nat.lt_succ_self n)
  have hstop : ∃ k, ∃ n ≥ j, f n (deletePrefix I X m k) ≤ 0 := by
    refine ⟨k, n, hnj, ?_⟩
    have := (abs_lt.mp happrox).2
    linarith
  let k := Nat.find hstop
  have hkstop : ∃ n ≥ j, f n (deletePrefix I X m k) ≤ 0 := Nat.find_spec hstop
  have hk0 : k ≠ 0 := by
    intro hk0
    obtain ⟨n, hnj, hn⟩ := hkstop
    rw [hk0, deletePrefix_zero] at hn
    exact (hpos n hnj).not_ge hn
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hprev : ∀ n ≥ j, 0 < f n (deletePrefix I X m r) := by
    intro n hnj
    apply lt_of_not_ge
    intro hn
    have hrk : r < k := by omega
    exact Nat.find_min hstop hrk ⟨n, hnj, hn⟩
  refine ⟨deletePrefix I X m k, subset_deletePrefix hIX m k,
    deletePrefix_subset I X m k, deletePrefix_finite I X m k, hkstop, ?_, Or.inr ?_⟩
  · exact hm X (deletePrefix I X m k) hIX hXY (subset_deletePrefix hIX m k)
      ((deletePrefix_subset I X m k).trans hXY) (deletePrefix_agree I X m k)
  · intro n hnj
    have h1 := hone n (deletePrefix I X m (r+1)) (deletePrefix I X m r)
      (subset_deletePrefix hIX m (r+1))
      (deletePrefix_antitone I X m (Nat.le_succ r))
      ((deletePrefix_subset I X m r).trans hXY)
      ⟨r, deletePrefix_step I X m r⟩
    rw [hr]
    have := hprev n hnj
    linarith

lemma antitone_agree_iInter {X : ℕ → Set ℕ} (hX : Antitone X) (m : ℕ) :
    ∃ k, ∀ l ≥ k, AgreeBelow (X l) (⋂ j, X j) m := by
  classical
  induction m with
  | zero => exact ⟨0, fun _ _ _ hx ↦ by omega⟩
  | succ m ih =>
    obtain ⟨k, hk⟩ := ih
    by_cases hm : m ∈ ⋂ j, X j
    · refine ⟨k, fun l hl x hx ↦ ?_⟩
      by_cases hxm : x < m
      · exact hk l hl x hxm
      · have hxm : x = m := by omega
        subst x
        exact ⟨fun _ ↦ hm, fun _ ↦ mem_iInter.mp hm l⟩
    · simp only [mem_iInter, not_forall] at hm
      obtain ⟨k', hk'⟩ := hm
      refine ⟨max k k', fun l hl x hx ↦ ?_⟩
      by_cases hxm : x < m
      · exact hk l ((le_max_left _ _).trans hl) x hxm
      · have hxm : x = m := by omega
        subst x
        have hml : m ∉ X l := fun h ↦ hk' (hX ((le_max_right _ _).trans hl) h)
        exact ⟨fun h ↦ (hml h).elim, fun h ↦ mem_iInter.mp h l⟩

lemma CylinderContinuous.tendsto_iInter {f : ℕ → Set ℕ → ℝ} {I Y : Set ℕ}
    (hcc : CylinderContinuous f I Y) {X : ℕ → Set ℕ}
    (hX : Antitone X) (hIX : ∀ j, I ⊆ X j) (hXY : ∀ j, X j ⊆ Y) (n : ℕ) :
    Tendsto (fun j ↦ f n (X j)) atTop (𝓝 (f n (⋂ j, X j))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := hcc (n+1) ε hε
  obtain ⟨k, hk⟩ := antitone_agree_iInter hX m
  refine ⟨k, fun j hj ↦ ?_⟩
  rw [Real.dist_eq]
  exact hm (X j) (⋂ l, X l) (hIX j) (hXY j)
    (subset_iInter hIX) ((iInter_subset X 0).trans (hXY 0)) (hk j hj)
    n (Nat.lt_succ_self n)

lemma infinite_endpoint_interpolation
    {f : ℕ → Set ℕ → ℝ} {I Y : Set ℕ} (hIY : I ⊆ Y)
    (hcc : CylinderContinuous f I Y)
    (hmono : ∀ n A B, I ⊆ A → A ⊆ B → B ⊆ Y → f n A ≤ f n B)
    (hone : ∀ n A B, I ⊆ A → A ⊆ B → B ⊆ Y →
      (∃ e, B ⊆ insert e A) → f n B ≤ f n A + 1)
    (hlow : ∀ Z, I ⊆ Z → Z ⊆ Y → (Z \ I).Finite →
      ∀ j, ∃ n ≥ j, f n Z < 0)
    (hhigh : ∃ j, ∀ n ≥ j, 0 < f n Y) :
    ∃ Z, I ⊆ Z ∧ Z ⊆ Y ∧
      (∀ j, ∃ n ≥ j, f n Z ≤ 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ j, ∀ n ≥ j, -1 - ε ≤ f n Z) := by
  classical
  let S := {X : Set ℕ // I ⊆ X ∧ X ⊆ Y}
  have hchoose : ∀ j (X : S), ∃ Z : S,
      Z.1 ⊆ X.1 ∧ (X.1 \ Z.1).Finite ∧
      (∃ n ≥ j, f n Z.1 ≤ 0) ∧
      (∀ n < j, |f n X.1 - f n Z.1| < (1/2:ℝ)^j) ∧
      (Z.1 = X.1 ∨ ∀ n ≥ j, -1 ≤ f n Z.1) := by
    intro j X
    obtain ⟨Z, hIZ, hZX, hfin, hneg, hclose, hreset⟩ :=
      deletion_stage hcc hone hlow X.2.1 X.2.2 j ((1/2:ℝ)^j) (by positivity)
    exact ⟨⟨Z, hIZ, hZX.trans X.2.2⟩, hZX, hfin, hneg, hclose, hreset⟩
  choose step hstep using hchoose
  let seq : ℕ → S := Nat.rec ⟨Y, hIY, Subset.rfl⟩ (fun j X ↦ step (j+1) X)
  let X : ℕ → Set ℕ := fun j ↦ (seq j).1
  have hX0 : X 0 = Y := rfl
  have hIX : ∀ j, I ⊆ X j := fun j ↦ (seq j).2.1
  have hXY : ∀ j, X j ⊆ Y := fun j ↦ (seq j).2.2
  have hstage : ∀ j,
      X (j+1) ⊆ X j ∧ (X j \ X (j+1)).Finite ∧
      (∃ n ≥ j+1, f n (X (j+1)) ≤ 0) ∧
      (∀ n < j+1, |f n (X j) - f n (X (j+1))| < (1/2:ℝ)^(j+1)) ∧
      (X (j+1) = X j ∨ ∀ n ≥ j+1, -1 ≤ f n (X (j+1))) := by
    intro j
    exact hstep (j+1) (seq j)
  have hanti : Antitone X := antitone_nat_of_succ_le fun j ↦ (hstage j).1
  let Z := ⋂ j, X j
  have hIZ : I ⊆ Z := subset_iInter hIX
  have hZY : Z ⊆ Y := (iInter_subset X 0).trans (hXY 0)
  have hneg : ∀ j, ∃ n ≥ j, f n Z ≤ 0 := by
    intro j
    obtain ⟨n, hn, hfn⟩ := (hstage j).2.2.1
    exact ⟨n, by omega,
      (hmono n Z (X (j+1)) hIZ (iInter_subset X (j+1)) (hXY (j+1))).trans hfn⟩
  have hreset : ∃ j, ∀ n ≥ j+1, -1 ≤ f n (X (j+1)) := by
    by_contra hn
    push Not at hn
    have heq : ∀ j, X (j+1) = X j := by
      intro j
      rcases (hstage j).2.2.2.2 with h | h
      · exact h
      · obtain ⟨n, hnj, hlt⟩ := hn j
        exact (hlt.not_ge (h n hnj)).elim
    have hconst : ∀ j, X j = Y := by
      intro j
      induction j with
      | zero => exact hX0
      | succ j ih => exact (heq j).trans ih
    obtain ⟨j, hj⟩ := hhigh
    obtain ⟨n, hn, hfn⟩ := (hstage j).2.2.1
    rw [hconst (j+1)] at hfn
    exact (hj n (by omega)).not_ge hfn
  obtain ⟨j₀, hj₀⟩ := hreset
  have hreset_range : ∀ k, j₀+1 ≤ k → ∀ n ≥ k, -1 ≤ f n (X k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hj₀
    | succ k hk ih =>
      intro n hn
      rcases (hstage k).2.2.2.2 with h | h
      · rw [h]
        exact ih n (by omega)
      · exact h n hn
  have hlower : ∀ n, j₀+1 ≤ n → ∀ k ≥ n,
      -1 - (1/2:ℝ)^n + (1/2:ℝ)^k ≤ f n (X k) := by
    intro n hn k hk
    induction k, hk using Nat.le_induction with
    | base => simpa using hreset_range n hn n le_rfl
    | succ k hk ih =>
      have hloss := (abs_lt.mp ((hstage k).2.2.2.1 n (by omega))).2
      have hpower : (1/2:ℝ)^(k+1) = (1/2:ℝ)^k / 2 := by rw [pow_succ]; ring
      rw [hpower] at hloss ⊢
      linarith
  have hlower_Z : ∀ n, j₀+1 ≤ n → -1 - (1/2:ℝ)^n ≤ f n Z := by
    intro n hn
    apply ge_of_tendsto (hcc.tendsto_iInter hanti hIX hXY n)
    filter_upwards [eventually_ge_atTop n] with k hk
    have hpow : 0 ≤ (1/2:ℝ)^k := by positivity
    exact (le_add_of_nonneg_right hpow).trans (hlower n hn k hk)
  refine ⟨Z, hIZ, hZY, hneg, ?_⟩
  intro ε hε
  have hpowlim : Tendsto (fun n : ℕ ↦ (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hpowlim).2 ε hε)
  refine ⟨max (j₀+1) N, fun n hn ↦ ?_⟩
  have h1 := hlower_Z n ((le_max_left _ _).trans hn)
  have h2 := hN n ((le_max_right _ _).trans hn)
  linarith

/-- Extended lower limiting value of the real probes. -/
noncomputable def probeLiminf {α : Type*} (f : ℕ → Set α → ℝ) (X : Set α) : EReal :=
  liminf (fun n ↦ (f n X : EReal)) atTop

lemma ereal_liminf_add_real (u : ℕ → EReal) (b : ℝ) :
    liminf (fun n ↦ u n + (b : EReal)) atTop = liminf u atTop + (b : EReal) := by
  apply le_antisymm
  · have h := EReal.liminf_add_le (u := fun _ : ℕ ↦ (b : EReal)) (v := u)
      (f := atTop) (Or.inl (by simp)) (Or.inl (by simp))
    simpa [Pi.add_def, add_comm] using h
  · simpa [Pi.add_def] using
      EReal.le_liminf_add (u := u) (v := fun _ : ℕ ↦ (b : EReal)) (f := atTop)

lemma probeLiminf_finite_change {α : Type*} {f : ℕ → Set α → ℝ}
    {X Y : Set α} {b : ℝ} (h : ∀ᶠ n in atTop, f n Y = f n X + b) :
    probeLiminf f Y = probeLiminf f X + (b : EReal) := by
  unfold probeLiminf
  rw [← ereal_liminf_add_real]
  exact liminf_congr (h.mono fun n hn ↦ by simp [hn, EReal.coe_add])

lemma probeLiminf_le_zero {α : Type*} {f : ℕ → Set α → ℝ} {X : Set α}
    (h : ∀ j, ∃ n ≥ j, f n X ≤ 0) : probeLiminf f X ≤ 0 := by
  apply liminf_le_of_frequently_le'
  rw [frequently_atTop]
  simpa using h

lemma probeLiminf_ge_neg_one {α : Type*} {f : ℕ → Set α → ℝ} {X : Set α}
    (h : ∀ ε : ℝ, 0 < ε → ∃ j, ∀ n ≥ j, -1 - ε ≤ f n X) :
    -1 ≤ probeLiminf f X := by
  by_contra hbad
  obtain ⟨r, hr1, hr2⟩ := EReal.exists_between_coe_real (lt_of_not_ge hbad)
  have hr : r < -1 := EReal.coe_lt_coe_iff.mp (by simpa using hr2)
  let ε : ℝ := (-1-r)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨j, hj⟩ := h ε hε
  have hbound : ((-1-ε : ℝ) : EReal) ≤ probeLiminf f X := by
    apply le_liminf_of_le (h := ?_)
    filter_upwards [eventually_ge_atTop j] with n hn
    exact EReal.coe_le_coe_iff.mpr (hj n hn)
  have hstrict : (r : EReal) < ((-1-ε : ℝ) : EReal) := by
    apply EReal.coe_lt_coe_iff.mpr
    dsimp [ε]
    linarith
  exact (hstrict.trans_le hbound).not_ge hr1.le

/-- The half-closed interval used by the lower-limit rule. -/
def LowerBasis {α : Type*} (f : ℕ → Set α → ℝ) (X : Set α) : Prop :=
  -1 < probeLiminf f X ∧ probeLiminf f X ≤ 0

lemma infinite_endpoint_liminf_interpolation
    {f : ℕ → Set ℕ → ℝ} {I Y : Set ℕ} (hIY : I ⊆ Y)
    (hcc : CylinderContinuous f I Y)
    (hmono : ∀ n A B, I ⊆ A → A ⊆ B → B ⊆ Y → f n A ≤ f n B)
    (hone : ∀ n A B, I ⊆ A → A ⊆ B → B ⊆ Y →
      (∃ e, B ⊆ insert e A) → f n B ≤ f n A + 1)
    (hlow : ∀ Z, I ⊆ Z → Z ⊆ Y → (Z \ I).Finite → probeLiminf f Z = ⊥)
    (hhigh : 0 < probeLiminf f Y) :
    ∃ Z, I ⊆ Z ∧ Z ⊆ Y ∧ -1 ≤ probeLiminf f Z ∧ probeLiminf f Z ≤ 0 := by
  have hlow' : ∀ Z, I ⊆ Z → Z ⊆ Y → (Z \ I).Finite →
      ∀ j, ∃ n ≥ j, f n Z < 0 := by
    intro Z hIZ hZY hfin
    have hlim : probeLiminf f Z < 0 := by rw [hlow Z hIZ hZY hfin]; exact EReal.bot_lt_coe 0
    have hh := frequently_lt_of_liminf_lt (u := fun n ↦ (f n Z : EReal)) (h := hlim)
    simpa [frequently_atTop] using hh
  have hhigh' : ∃ j, ∀ n ≥ j, 0 < f n Y := by
    have hh := eventually_lt_of_lt_liminf hhigh
    simpa [eventually_atTop] using hh
  obtain ⟨Z, hIZ, hZY, hneg, hbd⟩ :=
    infinite_endpoint_interpolation hIY hcc hmono hone hlow' hhigh'
  exact ⟨Z, hIZ, hZY, probeLiminf_ge_neg_one hbd, probeLiminf_le_zero hneg⟩

/-- Exact finite-cardinality translation on a fixed interval. -/
def IntervalFiniteShift {α : Type*} (f : ℕ → Set α → ℝ) (I Y : Set α) : Prop :=
  ∀ A B, I ⊆ A → A ⊆ B → B ⊆ Y → (B \ A).Finite →
    probeLiminf f B = probeLiminf f A + ((B \ A).ncard : EReal)

lemma finite_lower_interpolation {α : Type*} {f : ℕ → Set α → ℝ} {I Y : Set α}
    (hIY : I ⊆ Y) (hshift : IntervalFiniteShift f I Y)
    (hlow : probeLiminf f I ≤ -1) (hhigh : 0 < probeLiminf f Y)
    (hbot : probeLiminf f I ≠ ⊥) :
    ∃ B, I ⊆ B ∧ B ⊆ Y ∧ LowerBasis f B := by
  classical
  have htop : probeLiminf f I ≠ ⊤ := ne_top_of_le_ne_top (by simpa only [EReal.coe_neg, EReal.coe_one] using EReal.coe_ne_top (-1)) hlow
  let a := (probeLiminf f I).toReal
  have ha : (a : EReal) = probeLiminf f I := EReal.coe_toReal htop hbot
  have halow : a ≤ -1 := EReal.coe_le_coe_iff.mp (by simpa [ha] using hlow)
  let k : ℕ := ⌊-a⌋₊
  have hk_le : (k : ℝ) ≤ -a := Nat.floor_le (by linarith)
  have hk_gt : -a < (k : ℝ) + 1 := Nat.lt_floor_add_one (-a)
  have hk : -1 < a + k ∧ a + k ≤ 0 := by constructor <;> linarith
  have hchoose : ∃ H : Finset α, (H : Set α) ⊆ Y \ I ∧ H.card = k := by
    by_cases hfin : (Y \ I).Finite
    · have hgap : k ≤ (Y \ I).ncard := by
        by_contra hn
        have hn' : ((Y \ I).ncard : ℝ) < k := by exact_mod_cast lt_of_not_ge hn
        have hy := hshift I Y Subset.rfl hIY Subset.rfl hfin
        have hval : probeLiminf f Y = ((a + (Y \ I).ncard : ℝ) : EReal) := by
          rw [hy, ← ha, EReal.coe_add, EReal.coe_natCast]
        have hpos : 0 < a + (Y \ I).ncard := EReal.coe_lt_coe_iff.mp (by simpa [hval] using hhigh)
        linarith
      have hc : k ≤ hfin.toFinset.card := by simpa only [Set.ncard_eq_toFinset_card _ hfin] using hgap
      obtain ⟨H, hH, hcH⟩ := Finset.exists_subset_card_eq hc
      exact ⟨H, fun x hx ↦ by simpa using hH hx, hcH⟩
    · exact Set.Infinite.exists_subset_card_eq hfin k
  obtain ⟨H, hH, hcard⟩ := hchoose
  let B := I ∪ (H : Set α)
  have hIB : I ⊆ B := subset_union_left
  have hBY : B ⊆ Y := union_subset hIY (hH.trans sdiff_subset)
  have hdiff : B \ I = (H : Set α) := by
    ext x
    have hx := @hH x
    simp only [B, Set.mem_sdiff, mem_union] at hx ⊢
    tauto
  have hval := hshift I B Subset.rfl hIB hBY (by rw [hdiff]; exact H.finite_toSet)
  have hval' : probeLiminf f B = ((a+k : ℝ) : EReal) := by
    simpa [hdiff, hcard, ← ha, EReal.coe_add] using hval
  refine ⟨B, hIB, hBY, ?_⟩
  rw [LowerBasis, hval']
  constructor
  · exact EReal.coe_lt_coe_iff.mpr hk.1
  · exact EReal.coe_le_coe_iff.mpr hk.2

lemma finite_upper_interpolation {α : Type*} {f : ℕ → Set α → ℝ} {I Y : Set α}
    (hIY : I ⊆ Y) (hshift : IntervalFiniteShift f I Y)
    (hlow : probeLiminf f I = ⊥) (hhigh : 0 < probeLiminf f Y)
    (htop : probeLiminf f Y ≠ ⊤) :
    ∃ B, I ⊆ B ∧ B ⊆ Y ∧ LowerBasis f B := by
  classical
  have hbot : probeLiminf f Y ≠ ⊥ := ne_bot_of_gt hhigh
  let b := (probeLiminf f Y).toReal
  have hb : (b : EReal) = probeLiminf f Y := EReal.coe_toReal htop hbot
  have hbpos : 0 < b := EReal.coe_lt_coe_iff.mp (by simpa [hb] using hhigh)
  let k : ℕ := ⌈b⌉₊
  have hk_le : b ≤ (k : ℝ) := Nat.le_ceil b
  have hk_gt : (k : ℝ) < b + 1 := Nat.ceil_lt_add_one hbpos.le
  have hk : -1 < b - k ∧ b - k ≤ 0 := by constructor <;> linarith
  have hgap : (Y \ I).Infinite := by
    intro hfin
    have hh := hshift I Y Subset.rfl hIY Subset.rfl hfin
    rw [hlow, EReal.bot_add] at hh
    exact hbot hh
  obtain ⟨H, hH, hcard⟩ := hgap.exists_subset_card_eq k
  let B := Y \ (H : Set α)
  have hIB : I ⊆ B := by
    intro x hx
    exact ⟨hIY hx, fun h ↦ (hH h).2 hx⟩
  have hBY : B ⊆ Y := sdiff_subset
  have hdiff : Y \ B = (H : Set α) := by
    ext x
    have hx := @hH x
    simp only [B, Set.mem_sdiff] at hx ⊢
    tauto
  have hval := hshift B Y hIB hBY Subset.rfl (by rw [hdiff]; exact H.finite_toSet)
  have hval' : probeLiminf f B = ((b-k : ℝ) : EReal) := by
    have hh := congrArg (fun x : EReal ↦ x - ((k : ℝ) : EReal)) hval
    simpa [hdiff, hcard, ← hb, ← EReal.coe_natCast, EReal.add_sub_cancel_right,
      ← EReal.coe_sub] using hh.symm
  refine ⟨B, hIB, hBY, ?_⟩
  rw [LowerBasis, hval']
  exact ⟨EReal.coe_lt_coe_iff.mpr hk.1, EReal.coe_le_coe_iff.mpr hk.2⟩

/-- The complete local interpolation argument, including both finite
rounding cases and the opposite-infinite-endpoint case. -/
lemma local_interpolation
    {f : ℕ → Set ℕ → ℝ} {I Y : Set ℕ} (hIY : I ⊆ Y)
    (hcc : CylinderContinuous f I Y)
    (hmono : ∀ n A B, I ⊆ A → A ⊆ B → B ⊆ Y → f n A ≤ f n B)
    (hone : ∀ n A B, I ⊆ A → A ⊆ B → B ⊆ Y →
      (∃ e, B ⊆ insert e A) → f n B ≤ f n A + 1)
    (hshift : IntervalFiniteShift f I Y)
    (hlow : probeLiminf f I ≤ -1) (hhigh : 0 < probeLiminf f Y) :
    ∃ B, I ⊆ B ∧ B ⊆ Y ∧ LowerBasis f B := by
  classical
  by_cases hbot : probeLiminf f I = ⊥
  · by_cases htop : probeLiminf f Y = ⊤
    · have hlow' : ∀ Z, I ⊆ Z → Z ⊆ Y → (Z \ I).Finite → probeLiminf f Z = ⊥ := by
        intro Z hIZ hZY hfin
        rw [hshift I Z Subset.rfl hIZ hZY hfin, hbot, EReal.bot_add]
      obtain ⟨Z, hIZ, hZY, hZlo, hZhi⟩ :=
        infinite_endpoint_liminf_interpolation hIY hcc hmono hone hlow' hhigh
      rcases lt_or_eq_of_le hZlo with hZlo | hZeq
      · exact ⟨Z, hIZ, hZY, hZlo, hZhi⟩
      · have hgap : (Y \ Z).Nonempty := by
          by_contra hn
          have hyz : Y ⊆ Z := sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp hn)
          have hZYeq : Z = Y := Subset.antisymm hZY hyz
          rw [hZYeq, htop] at hZhi
          exact (EReal.coe_lt_top 0).not_ge hZhi
        obtain ⟨e, heY, heZ⟩ := hgap
        have hIBe : I ⊆ insert e Z := hIZ.trans (subset_insert _ _)
        have hBeY : insert e Z ⊆ Y := insert_subset heY hZY
        have hdiff : insert e Z \ Z = {e} := by ext x; simp [heZ]
        have hval := hshift Z (insert e Z) hIZ (subset_insert _ _) hBeY
          (by rw [hdiff]; exact finite_singleton e)
        have hzero : probeLiminf f (insert e Z) = 0 := by
          rw [hdiff, ncard_singleton, ← hZeq] at hval
          have hc : (-1 : EReal) + 1 = 0 := by
            have hh := congrArg (fun r : ℝ ↦ (r : EReal)) (show (-1 : ℝ) + 1 = 0 by ring)
            simpa only [EReal.coe_add, EReal.coe_neg, EReal.coe_one, EReal.coe_zero] using hh
          simpa only [Nat.cast_one, hc] using hval
        refine ⟨insert e Z, hIBe, hBeY, ?_⟩
        simp [LowerBasis, hzero]
    · exact finite_upper_interpolation hIY hshift hbot hhigh htop
  · exact finite_lower_interpolation hIY hshift hlow hhigh hbot

end InfiniteMatroidCounterexample
end

end OAI


