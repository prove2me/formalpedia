-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
-- name    : OAI_Combinatorics_InfiniteMatroid_BlockDensity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:47:15.404157+00:00
-- url     : https://prove2.me/theorems/83b772e1-3302-4dc6-8310-06fac19486cb
-- title:
--   Block densities, small sets, density classes and probe functionals on $E_0$
-- statement:
--   Let $D$ be the set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, and let $E_0=D\times\{0,1\}$; an element $((m,g),b)$ of $E_0$ has *block index* $m$, and complements $X^c$ are taken in $E_0$. This file sets up a notion of density on $E_0$ adapted to the very fast growth of the blocks, and the *probe* functionals that later define the local basis rules.
--
--   1. **Blocks.** $D_m=\{(m,g):\ g:\{0,1\}^m\to\{0,1\}\}\subseteq D$ and $W_m=D_m\times\{0,1\}\subseteq E_0$, so that
--   $$|D_m|=2^{2^m},\qquad |W_m|=2\cdot2^{2^m};$$
--   the blocks $W_m$ are pairwise disjoint and $W_m$ is the set of elements of block index $m$.
--   2. **Prefixes.** $P_n=W_0\cup\dots\cup W_{n-1}$ is the set of elements of block index $<n$. The prefixes increase with $n$, $|P_n|=\sum_{m<n}|W_m|$, and the blocks grow so fast that $2\sum_{j<m}2^{2^j}\le2^{2^m}$; hence $2|P_n|\le|W_k|$ whenever $n\le k$. Every finite subset of $E_0$ lies in some $P_n$.
--   3. **Finite densities.** For a finite set $s$ and any set $X$, $\operatorname{dens}_s(X)=|s\cap X|/|s|$. It lies in $[0,1]$, is monotone and subadditive in $X$, is additive on disjoint sets, satisfies $\operatorname{dens}_s(X^c)=1-\operatorname{dens}_s(X)$ for nonempty $s$, and $|\operatorname{dens}_s(X)-\operatorname{dens}_s(Z)|\le\operatorname{dens}_s(Y\setminus I)$ whenever $I\subseteq X\subseteq Y$ and $I\subseteq Z\subseteq Y$.
--   4. **Block density and small sets.** $\delta_m(X)=\operatorname{dens}_{W_m}(X)=|X\cap W_m|/|W_m|$ for $X\subseteq E_0$, and
--   $$X\ \text{is small}\quad\Longleftrightarrow\quad\lim_{m\to\infty}\delta_m(X)=0 .$$
--   Small sets form an ideal: $\emptyset$ is small, and subsets and finite unions of small sets are small.
--   5. **Density classes.** $X$ lies in the *class* of $T$ if $X\triangle T$ is small. This relation is reflexive and transitive; if $I$ and $Y$ lie in the class of $T$, then $Y\setminus I$ is small, and every $X$ with $I\subseteq X\subseteq Y$ lies in the class of $T$.
--   6. **Tail extrema.** For a real sequence $u$ let $\overline u_n=\sup_{m\ge n}u_m$ and $\underline u_n=\inf_{m\ge n}u_m$. For bounded sequences the file records the comparison rules and the Lipschitz rules (if $|u_m-v_m|\le\delta$ for all $m\ge n$, then $|\overline u_n-\overline v_n|\le\delta$ and $|\underline u_n-\underline v_n|\le\delta$) and, for every sequence, the negation rules $\overline{(-u)}_n=-\underline u_n$ and $\underline{(-u)}_n=-\overline u_n$.
--   7. **Probes.** For $T,X\subseteq E_0$ and $m,n\in\mathbb N$ put $d^T_m(X)=\delta_m(X)-\delta_m(T)\in[-1,1]$, $p^T_n(X)=|X\cap P_n|-|T\cap P_n|$, and
--   $$f^T_n(X)=p^T_n(X)+|P_n|\Bigl(\sup_{m\ge n}d^T_m(X)+\inf_{m\ge n}d^T_m(X)\Bigr).$$
--
--   The probe $f^T_n(X)$ compares $X$ with a reference set $T$ at scale $n$: an exact count of the difference on the first $n$ blocks plus a density correction from the later blocks, weighted by $|P_n|$. Its main properties, all proved in this file, are:
--   - *monotonicity:* $X\subseteq Y$ implies $f^T_n(X)\le f^T_n(Y)$;
--   - *one point costs at most one:* $f^T_n(X\cup\{e\})\le f^T_n(X)+1$ for every $n$ (this uses $2|P_n|\le|W_k|$ for $k\ge n$);
--   - *finite changes:* if $X\subseteq Y$ and $Y\setminus X$ is finite, then $f^T_n(Y)=f^T_n(X)+|Y\setminus X|$ for all sufficiently large $n$;
--   - *complement symmetry:* $f^{T^c}_n(X^c)=-f^T_n(X)$;
--   - *variation bound:* if $X$ and $Z$ agree on $P_n$ and $|d^T_m(X)-d^T_m(Z)|\le\delta$ for all $m\ge n$, then $|f^T_n(X)-f^T_n(Z)|\le2|P_n|\delta$;
--   - *block continuity:* if $I$ and $Y$ lie in the class of $T$, then for every $j\in\mathbb N$ and $\varepsilon>0$ there is $N\ge j$ such that $|f^T_n(X)-f^T_n(Z)|<\varepsilon$ for all $n\le j$ and all $X,Z$ with $I\subseteq X\subseteq Y$, $I\subseteq Z\subseteq Y$ that contain the same elements of block index $<N$.
--
--   The lower limit of $f^T_n(X)$ as $n\to\infty$ is what selects, inside the density class of $T$, the local bases of the self-dual matroid on $E_0$; the properties above are the source of the antichain, exchange and complementation behaviour of these local rules.
--
--   **Formalization Note** The definitions are `dBlock`, `wBlock`, `blockPrefix`, `traceFinset` (the finite set $s\cap X$), `finiteDensity`, `density`, `Small`, `SameClass T X` (which is `Small (X ∆ T)`), `tailSup`, `tailInf`, `dProbe`, `pProbe` and `fProbe T n X`. `finiteDensity` uses real division and would be $0$ for an empty $s$; all blocks are nonempty. `tailSup u n` and `tailInf u n` are `sSup` and `sInf` of the set $\{u_m: m\ge n\}$; they are only applied to the bounded sequences $d^T_m(X)$, so Lean's conventions for unbounded sets play no role. The properties listed above are the lemmas `fProbe_mono`, `fProbe_insert_le`, `finite_change_eventually`, `fProbe_compl`, `fProbe_variation` and `fProbe_block_continuity`, supported by elementary lemmas on traces, finite densities and tail extrema.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/BlockDensity.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/BlockDensity.lean by skeleton subtraction
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

namespace OAI

section

open Set Filter Finset
open scoped Topology symmDiff

namespace InfiniteMatroidCounterexample

noncomputable def dBlock (m : ℕ) : Finset D :=
  Finset.univ.map ⟨fun f ↦ ⟨m, f⟩, fun _ _ h ↦ by simpa using h⟩

noncomputable def wBlock (m : ℕ) : Finset E0 := (dBlock m).product Finset.univ

@[simp] lemma mem_dBlock (x : D) (m : ℕ) : x ∈ dBlock m ↔ x.1 = m := by
  classical
  rcases x with ⟨k, f⟩
  simp only [dBlock, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨g, h⟩
    exact congrArg Sigma.fst h.symm
  · intro h
    subst k
    exact ⟨f, rfl⟩

@[simp] lemma mem_wBlock (x : E0) (m : ℕ) : x ∈ wBlock m ↔ x.1.1 = m := by
  simp [wBlock]

@[simp] lemma card_dBlock (m : ℕ) : (dBlock m).card = 2 ^ (2 ^ m) := by
  simp [dBlock]

@[simp] lemma card_wBlock (m : ℕ) : (wBlock m).card = 2 * 2 ^ (2 ^ m) := by
  simp [wBlock, mul_comm]

lemma wBlock_disjoint : Pairwise (fun i j ↦ Disjoint (wBlock i) (wBlock j)) := by
  intro i j hij
  classical
  exact Finset.disjoint_left.mpr fun x hxi hxj ↦ hij ((mem_wBlock x i).mp hxi |>.symm.trans ((mem_wBlock x j).mp hxj))

noncomputable def blockPrefix (n : ℕ) : Finset E0 :=
  (Finset.range n).biUnion wBlock

@[simp] lemma mem_prefix (x : E0) (n : ℕ) : x ∈ blockPrefix n ↔ x.1.1 < n := by
  classical
  simp [blockPrefix]

lemma prefix_mono {n k : ℕ} (hnk : n ≤ k) : blockPrefix n ⊆ blockPrefix k := by
  intro x hx
  exact (mem_prefix x k).mpr ((mem_prefix x n).mp hx |>.trans_le hnk)

lemma card_prefix (n : ℕ) : (blockPrefix n).card = ∑ m ∈ Finset.range n, (wBlock m).card := by
  classical
  exact Finset.card_biUnion (fun i _ j _ hij ↦ wBlock_disjoint hij)

lemma block_growth (m : ℕ) : 2 * ∑ j ∈ Finset.range m, 2 ^ (2 ^ j) ≤ 2 ^ (2 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ, pow_mul]
    by_cases hm : m = 0
    · subst m
      norm_num
    · have h4 : 4 ≤ 2 ^ (2 ^ m) := by
        calc
          4 = 2 ^ (2 ^ 1) := by norm_num
          _ ≤ 2 ^ (2 ^ m) := Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      nlinarith

lemma block_prefix_growth {n k : ℕ} (hnk : n ≤ k) :
    2 * (blockPrefix n).card ≤ (wBlock k).card := by
  rw [card_prefix, card_wBlock]
  simp only [card_wBlock, ← Finset.mul_sum]
  have hsum : ∑ j ∈ Finset.range n, 2 ^ (2 ^ j) ≤ ∑ j ∈ Finset.range k, 2 ^ (2 ^ j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnk) (by intros; positivity)
  have hg := block_growth k
  nlinarith

noncomputable def traceFinset {α : Type*} (s : Finset α) (X : Set α) : Finset α := by
  classical
  exact s.filter (· ∈ X)

@[simp] lemma mem_traceFinset {α : Type*} (s : Finset α) (X : Set α) (x : α) :
    x ∈ traceFinset s X ↔ x ∈ s ∧ x ∈ X := by
  classical
  exact Finset.mem_filter

lemma traceFinset_subset {α : Type*} (s : Finset α) (X : Set α) : traceFinset s X ⊆ s := by
  intro x hx
  exact (mem_traceFinset s X x).mp hx |>.1

lemma traceFinset_mono {α : Type*} (s : Finset α) {X Y : Set α} (h : X ⊆ Y) :
    traceFinset s X ⊆ traceFinset s Y := by
  intro x hx
  obtain ⟨hxs, hxX⟩ := (mem_traceFinset s X x).mp hx
  exact (mem_traceFinset s Y x).mpr ⟨hxs, h hxX⟩

@[simp] lemma traceFinset_empty {α : Type*} (s : Finset α) : traceFinset s ∅ = ∅ := by
  ext x
  simp

@[simp] lemma traceFinset_univ {α : Type*} (s : Finset α) : traceFinset s univ = s := by
  ext x
  simp

lemma traceFinset_union {α : Type*} [DecidableEq α] (s : Finset α) (X Y : Set α) :
    traceFinset s (X ∪ Y) = traceFinset s X ∪ traceFinset s Y := by
  ext x
  simp only [mem_traceFinset, Set.mem_union, Finset.mem_union]
  tauto

lemma traceFinset_disjoint {α : Type*} (s : Finset α) {X Y : Set α} (h : Disjoint X Y) :
    Disjoint (traceFinset s X) (traceFinset s Y) := by
  exact Finset.disjoint_left.mpr fun x hx hy ↦
    Set.disjoint_left.mp h ((mem_traceFinset s X x).mp hx).2 ((mem_traceFinset s Y x).mp hy).2

/-- Counting density inside a finite block. -/
noncomputable def finiteDensity {α : Type*} (s : Finset α) (X : Set α) : ℝ :=
  ((traceFinset s X).card : ℝ) / s.card

lemma finiteDensity_nonneg {α : Type*} (s : Finset α) (X : Set α) :
    0 ≤ finiteDensity s X := by
  unfold finiteDensity
  positivity

lemma finiteDensity_le_one {α : Type*} (s : Finset α) (X : Set α) :
    finiteDensity s X ≤ 1 := by
  unfold finiteDensity
  exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_le_card (traceFinset_subset s X)) (by positivity)

lemma finiteDensity_mono {α : Type*} (s : Finset α) {X Y : Set α} (h : X ⊆ Y) :
    finiteDensity s X ≤ finiteDensity s Y := by
  unfold finiteDensity
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (traceFinset_mono s h)

lemma finiteDensity_union_le {α : Type*} (s : Finset α) (X Y : Set α) :
    finiteDensity s (X ∪ Y) ≤ finiteDensity s X + finiteDensity s Y := by
  classical
  unfold finiteDensity
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [traceFinset_union]
  exact_mod_cast Finset.card_union_le (traceFinset s X) (traceFinset s Y)

lemma finiteDensity_compl {α : Type*} (s : Finset α) (X : Set α) (hs : s.Nonempty) :
    finiteDensity s Xᶜ = 1 - finiteDensity s X := by
  classical
  have hc : (traceFinset s X).card + (traceFinset s Xᶜ).card = s.card := by
    rw [← Finset.card_union_of_disjoint (traceFinset_disjoint s disjoint_compl_right),
      ← traceFinset_union, union_compl_self, traceFinset_univ]
  have hs0 : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  unfold finiteDensity
  have hc' : ((traceFinset s X).card : ℝ) + ((traceFinset s Xᶜ).card : ℝ) = s.card :=
    by exact_mod_cast hc
  field_simp
  linarith

lemma finiteDensity_union {α : Type*} (s : Finset α) {X Y : Set α} (h : Disjoint X Y) :
    finiteDensity s (X ∪ Y) = finiteDensity s X + finiteDensity s Y := by
  classical
  simp only [finiteDensity, traceFinset_union,
    Finset.card_union_of_disjoint (traceFinset_disjoint s h), Nat.cast_add, add_div]

noncomputable def density (X : Set E0) (m : ℕ) : ℝ := finiteDensity (wBlock m) X

def Small (X : Set E0) : Prop := Tendsto (density X) atTop (𝓝 0)

lemma small_empty : Small ∅ := by
  have heq : density ∅ = fun _ ↦ 0 := by ext m; simp [density, finiteDensity]
  rw [Small, heq]
  exact tendsto_const_nhds

lemma small_subset {X Y : Set E0} (hY : Small Y) (hXY : X ⊆ Y) : Small X := by
  exact squeeze_zero (fun m ↦ finiteDensity_nonneg _ _) (fun m ↦ finiteDensity_mono _ hXY) hY

lemma small_union {X Y : Set E0} (hX : Small X) (hY : Small Y) : Small (X ∪ Y) := by
  have ht : Tendsto (fun m ↦ density X m + density Y m) atTop (𝓝 0) := by
    simpa using hX.add hY
  exact squeeze_zero (fun m ↦ finiteDensity_nonneg _ _) (fun m ↦ finiteDensity_union_le _ _ _) ht

lemma finite_subset_prefix {X : Set E0} (hX : X.Finite) : ∃ n, X ⊆ ↑(blockPrefix n) := by
  induction X, hX using Set.Finite.induction_on with
  | empty => exact ⟨0, empty_subset _⟩
  | @insert x X hx hX ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨max n (x.1.1+1), Set.insert_subset ?_ (hn.trans (prefix_mono (le_max_left _ _)))⟩
    exact (mem_prefix _ _).mpr (by omega)

def SameClass (T X : Set E0) : Prop := Small (X ∆ T)

lemma sameClass_refl (T : Set E0) : SameClass T T := by
  simpa [SameClass] using small_empty

lemma sameClass_trans {T X Y : Set E0} (hX : SameClass T X) (hY : SameClass X Y) : SameClass T Y := by
  exact small_subset (small_union hX hY) (by intro x; simp only [mem_symmDiff, mem_union]; tauto)

lemma sameClass_interval {T I X Y : Set E0} (hI : SameClass T I) (hY : SameClass T Y)
    (hIX : I ⊆ X) (hXY : X ⊆ Y) : SameClass T X := by
  apply small_subset (small_union hI hY)
  intro x hx
  simp only [mem_symmDiff, mem_union] at hx ⊢
  have hi := @hIX x
  have hy := @hXY x
  tauto

noncomputable def tailSup (u : ℕ → ℝ) (n : ℕ) : ℝ := sSup (u '' Ici n)
noncomputable def tailInf (u : ℕ → ℝ) (n : ℕ) : ℝ := sInf (u '' Ici n)

lemma tail_nonempty (u : ℕ → ℝ) (n : ℕ) : (u '' Ici n).Nonempty :=
  ⟨u n, mem_image_of_mem u (mem_Ici.mpr le_rfl)⟩

lemma le_tailSup {u : ℕ → ℝ} (hu : BddAbove (Set.range u)) {n m : ℕ} (hnm : n ≤ m) :
    u m ≤ tailSup u n :=
  le_csSup (hu.mono (image_subset_range _ _)) (mem_image_of_mem u hnm)

lemma tailInf_le {u : ℕ → ℝ} (hu : BddBelow (Set.range u)) {n m : ℕ} (hnm : n ≤ m) :
    tailInf u n ≤ u m :=
  csInf_le (hu.mono (image_subset_range _ _)) (mem_image_of_mem u hnm)

lemma tailSup_le_add {u v : ℕ → ℝ} {n : ℕ} {δ : ℝ}
    (hv : BddAbove (Set.range v)) (h : ∀ m ≥ n, u m ≤ v m + δ) :
    tailSup u n ≤ tailSup v n + δ := by
  apply csSup_le (tail_nonempty u n)
  rintro x ⟨m, hm, rfl⟩
  have hh := le_tailSup hv hm
  linarith [h m hm]

lemma tailInf_le_add {u v : ℕ → ℝ} {n : ℕ} {δ : ℝ}
    (hu : BddBelow (Set.range u)) (h : ∀ m ≥ n, u m ≤ v m + δ) :
    tailInf u n ≤ tailInf v n + δ := by
  have hh : tailInf u n - δ ≤ tailInf v n := by
    apply le_csInf (tail_nonempty v n)
    rintro x ⟨m, hm, rfl⟩
    have h1 := tailInf_le hu hm
    have h2 := h m hm
    linarith
  linarith

lemma tailSup_mono {u v : ℕ → ℝ} {n : ℕ}
    (hv : BddAbove (Set.range v)) (h : ∀ m ≥ n, u m ≤ v m) :
    tailSup u n ≤ tailSup v n := by
  simpa using tailSup_le_add hv (δ := 0) (by simpa using h)

lemma tailInf_mono {u v : ℕ → ℝ} {n : ℕ}
    (hu : BddBelow (Set.range u)) (h : ∀ m ≥ n, u m ≤ v m) :
    tailInf u n ≤ tailInf v n := by
  simpa using tailInf_le_add hu (δ := 0) (by simpa using h)

lemma tailSup_lipschitz {u v : ℕ → ℝ} {n : ℕ} {δ : ℝ}
    (hu : BddAbove (Set.range u)) (hv : BddAbove (Set.range v))
    (h : ∀ m ≥ n, |u m - v m| ≤ δ) : |tailSup u n - tailSup v n| ≤ δ := by
  have hle : ∀ m ≥ n, u m ≤ v m + δ := by
    intro m hm
    have hh := (abs_le.mp (h m hm)).2
    linarith
  have hge : ∀ m ≥ n, v m ≤ u m + δ := by
    intro m hm
    have hh := (abs_le.mp (h m hm)).1
    linarith
  have h1 := tailSup_le_add hv hle
  have h2 := tailSup_le_add hu hge
  rw [abs_le]
  constructor <;> linarith

lemma tailInf_lipschitz {u v : ℕ → ℝ} {n : ℕ} {δ : ℝ}
    (hu : BddBelow (Set.range u)) (hv : BddBelow (Set.range v))
    (h : ∀ m ≥ n, |u m - v m| ≤ δ) : |tailInf u n - tailInf v n| ≤ δ := by
  have hle : ∀ m ≥ n, u m ≤ v m + δ := by
    intro m hm
    have hh := (abs_le.mp (h m hm)).2
    linarith
  have hge : ∀ m ≥ n, v m ≤ u m + δ := by
    intro m hm
    have hh := (abs_le.mp (h m hm)).1
    linarith
  have h1 := tailInf_le_add hu hle
  have h2 := tailInf_le_add hv hge
  rw [abs_le]
  constructor <;> linarith

lemma tailSup_neg (u : ℕ → ℝ) (n : ℕ) : tailSup (-u) n = -tailInf u n := by
  open scoped Pointwise in
    have heq : (-u) '' Ici n = -(u '' Ici n) := by
      ext x
      simp [neg_eq_iff_eq_neg]
  unfold tailSup tailInf
  rw [heq, Real.sSup_neg]

lemma tailInf_neg (u : ℕ → ℝ) (n : ℕ) : tailInf (-u) n = -tailSup u n := by
  open scoped Pointwise in
    have heq : (-u) '' Ici n = -(u '' Ici n) := by
      ext x
      simp [neg_eq_iff_eq_neg]
  unfold tailSup tailInf
  rw [heq, Real.sInf_neg]

/-- The block-density difference d_m^T(X). -/
noncomputable def dProbe (T X : Set E0) (m : ℕ) : ℝ := density X m - density T m

/-- The finite-prefix count difference p_n^T(X). -/
noncomputable def pProbe (T X : Set E0) (n : ℕ) : ℝ :=
  (traceFinset (blockPrefix n) X).card - ((traceFinset (blockPrefix n) T).card : ℝ)

noncomputable def fProbe (T : Set E0) (n : ℕ) (X : Set E0) : ℝ :=
  pProbe T X n + (blockPrefix n).card * (tailSup (dProbe T X) n + tailInf (dProbe T X) n)

lemma dProbe_bounds (T X : Set E0) (m : ℕ) : -1 ≤ dProbe T X m ∧ dProbe T X m ≤ 1 := by
  have hX0 := finiteDensity_nonneg (wBlock m) X
  have hX1 := finiteDensity_le_one (wBlock m) X
  have hT0 := finiteDensity_nonneg (wBlock m) T
  have hT1 := finiteDensity_le_one (wBlock m) T
  dsimp [dProbe, density]
  constructor <;> linarith

lemma dProbe_bddAbove (T X : Set E0) : BddAbove (Set.range (dProbe T X)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨m, rfl⟩
  exact (dProbe_bounds T X m).2

lemma dProbe_bddBelow (T X : Set E0) : BddBelow (Set.range (dProbe T X)) := by
  refine ⟨-1, ?_⟩
  rintro x ⟨m, rfl⟩
  exact (dProbe_bounds T X m).1

lemma dProbe_mono (T : Set E0) {X Y : Set E0} (h : X ⊆ Y) (m : ℕ) :
    dProbe T X m ≤ dProbe T Y m := sub_le_sub_right (finiteDensity_mono _ h) _

lemma pProbe_mono (T : Set E0) {X Y : Set E0} (h : X ⊆ Y) (n : ℕ) :
    pProbe T X n ≤ pProbe T Y n := by
  classical
  apply sub_le_sub_right
  exact_mod_cast Finset.card_le_card (traceFinset_mono (blockPrefix n) h)

lemma fProbe_mono (T : Set E0) {X Y : Set E0} (h : X ⊆ Y) (n : ℕ) :
    fProbe T n X ≤ fProbe T n Y := by
  apply add_le_add (pProbe_mono T h n)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (tailSup_mono (dProbe_bddAbove T Y) (fun m _ ↦ dProbe_mono T h m))
    (tailInf_mono (dProbe_bddBelow T X) (fun m _ ↦ dProbe_mono T h m))

lemma traceFinset_insert {α : Type*} [DecidableEq α] (s : Finset α) (X : Set α)
    (e : α) (he : e ∈ s) : traceFinset s (insert e X) = insert e (traceFinset s X) := by
  ext x
  simp only [mem_traceFinset, Set.mem_insert_iff, Finset.mem_insert]
  constructor
  · rintro ⟨hxs, rfl | hx⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hxs, hx⟩
  · rintro (rfl | ⟨hxs, hx⟩)
    · exact ⟨he, Or.inl rfl⟩
    · exact ⟨hxs, Or.inr hx⟩

lemma traceFinset_insert_of_notMem {α : Type*} (s : Finset α) (X : Set α)
    (e : α) (he : e ∉ s) : traceFinset s (insert e X) = traceFinset s X := by
  ext x
  simp only [mem_traceFinset, Set.mem_insert_iff]
  constructor
  · rintro ⟨hxs, rfl | hx⟩
    · exact (he hxs).elim
    · exact ⟨hxs, hx⟩
  · rintro ⟨hxs, hx⟩
    exact ⟨hxs, Or.inr hx⟩

lemma traceFinset_of_agree {α : Type*} (s : Finset α) {X Y : Set α}
    (h : ∀ x ∈ s, (x ∈ X ↔ x ∈ Y)) : traceFinset s X = traceFinset s Y := by
  ext x
  simp only [mem_traceFinset]
  exact and_congr_right (h x)

lemma trace_card_insert_le {α : Type*} (s : Finset α) (X : Set α) (e : α) :
    (traceFinset s (insert e X)).card ≤ (traceFinset s X).card + 1 := by
  classical
  by_cases he : e ∈ s
  · rw [traceFinset_insert s X e he]
    exact Finset.card_insert_le _ _
  · rw [traceFinset_insert_of_notMem s X e he]
    omega

lemma finiteDensity_insert_le {α : Type*} (s : Finset α) (X : Set α) (e : α) :
    finiteDensity s (insert e X) ≤ finiteDensity s X + 1 / s.card := by
  rw [finiteDensity, finiteDensity, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast trace_card_insert_le s X e

lemma fProbe_insert_le (T X : Set E0) (e : E0) (n : ℕ) :
    fProbe T n (insert e X) ≤ fProbe T n X + 1 := by
  classical
  by_cases hen : e.1.1 < n
  · have ht : dProbe T (insert e X) '' Ici n = dProbe T X '' Ici n := by
      apply Set.image_congr
      intro m hm
      change n ≤ m at hm
      have he : e ∉ wBlock m := by simp only [mem_wBlock]; omega
      simp [dProbe, density, finiteDensity, traceFinset_insert_of_notMem _ _ _ he]
    have hp : pProbe T (insert e X) n ≤ pProbe T X n + 1 := by
      dsimp [pProbe]
      have hc : ((traceFinset (blockPrefix n) (insert e X)).card : ℝ) ≤
          (traceFinset (blockPrefix n) X).card + 1 := by
        exact_mod_cast trace_card_insert_le (blockPrefix n) X e
      linarith
    dsimp [fProbe, tailSup, tailInf]
    rw [ht]
    linarith
  · have hp : pProbe T (insert e X) n = pProbe T X n := by
      simp [pProbe, traceFinset_insert_of_notMem _ _ _ ((mem_prefix e n).not.mpr hen)]
    have hd : ∀ m ≥ n, dProbe T (insert e X) m ≤
        dProbe T X m + 1 / (wBlock e.1.1).card := by
      intro m hm
      by_cases hem : e.1.1 = m
      · subst m
        dsimp [dProbe, density]
        linarith [finiteDensity_insert_le (wBlock e.1.1) X e]
      · have he : e ∉ wBlock m := (mem_wBlock e m).not.mpr hem
        dsimp [dProbe, density, finiteDensity]
        rw [traceFinset_insert_of_notMem _ _ _ he]
        have : (0 : ℝ) ≤ 1 / (wBlock e.1.1).card := by positivity
        linarith
    have hs := tailSup_le_add (dProbe_bddAbove T X) hd
    have hi := tailInf_le_add (dProbe_bddBelow T (insert e X)) hd
    have hg : 2 * ((blockPrefix n).card : ℝ) ≤ (wBlock e.1.1).card := by
      exact_mod_cast block_prefix_growth (Nat.le_of_not_gt hen)
    have hc : (0 : ℝ) < (wBlock e.1.1).card := by simp
    have hm : (blockPrefix n).card * (2 / ((wBlock e.1.1).card : ℝ)) ≤ 1 := by
      rw [← mul_div_assoc, div_le_iff₀ hc]
      linarith
    have hmul := mul_le_mul_of_nonneg_left (add_le_add hs hi)
      (show (0 : ℝ) ≤ (blockPrefix n).card by positivity)
    dsimp [fProbe]
    rw [hp]
    simp only [div_eq_mul_inv] at hm hmul
    nlinarith

lemma finite_change_eventually {T X Y : Set E0} (hXY : X ⊆ Y)
    (hfin : (Y \ X).Finite) : ∀ᶠ n in atTop,
      fProbe T n Y = fProbe T n X + (Y \ X).ncard := by
  classical
  obtain ⟨N, hN⟩ := finite_subset_prefix hfin
  filter_upwards [eventually_ge_atTop N] with n hn
  have hd : ∀ m ≥ n, dProbe T Y m = dProbe T X m := by
    intro m hm
    suffices htrace : traceFinset (wBlock m) Y = traceFinset (wBlock m) X by
      simp [dProbe, density, finiteDensity, htrace]
    apply traceFinset_of_agree
    intro x hxm
    refine ⟨fun hxY ↦ ?_, fun hxX ↦ hXY hxX⟩
    by_contra hxX
    have hp := (mem_prefix x N).mp (hN ⟨hxY, hxX⟩)
    have hb := (mem_wBlock x m).mp hxm
    omega
  have ht : dProbe T Y '' Ici n = dProbe T X '' Ici n :=
    Set.image_congr (fun m hm ↦ hd m hm)
  have heq : traceFinset (blockPrefix n) (Y \ X) = hfin.toFinset := by
    ext x
    simp only [mem_traceFinset, Set.Finite.mem_toFinset]
    exact ⟨And.right, fun hx ↦ ⟨prefix_mono hn (hN hx), hx⟩⟩
  have hcard : (traceFinset (blockPrefix n) Y).card =
      (traceFinset (blockPrefix n) X).card + (Y \ X).ncard := by
    have hy : Y = X ∪ (Y \ X) := by ext x; simp only [Set.mem_union, Set.mem_sdiff]; have := @hXY x; tauto
    conv_lhs => rw [hy]
    rw [traceFinset_union, Finset.card_union_of_disjoint
      (traceFinset_disjoint _ Set.disjoint_sdiff_right), heq, ← Set.ncard_eq_toFinset_card (Y \ X) hfin]
  dsimp [fProbe, pProbe, tailSup, tailInf]
  rw [ht, hcard]
  push_cast
  ring

lemma dProbe_compl (T X : Set E0) : dProbe Tᶜ Xᶜ = -dProbe T X := by
  ext m
  have hn : (wBlock m).Nonempty := Finset.card_pos.mp (by simp)
  simp only [dProbe, density, finiteDensity_compl _ _ hn, Pi.neg_apply]
  ring

lemma pProbe_compl (T X : Set E0) (n : ℕ) : pProbe Tᶜ Xᶜ n = -pProbe T X n := by
  classical
  have hc (Z : Set E0) : ((traceFinset (blockPrefix n) Z).card : ℝ) +
      (traceFinset (blockPrefix n) Zᶜ).card = (blockPrefix n).card := by
    rw [← Nat.cast_add, ← Finset.card_union_of_disjoint
      (traceFinset_disjoint _ disjoint_compl_right), ← traceFinset_union,
      union_compl_self, traceFinset_univ]
  dsimp [pProbe]
  linarith [hc X, hc T]

lemma fProbe_compl (T X : Set E0) (n : ℕ) : fProbe Tᶜ n Xᶜ = -fProbe T n X := by
  simp only [fProbe, pProbe_compl, dProbe_compl, tailSup_neg, tailInf_neg]
  ring

lemma finiteDensity_interval {α : Type*} (s : Finset α) {I X Z Y : Set α}
    (hIX : I ⊆ X) (hXY : X ⊆ Y) (hIZ : I ⊆ Z) (hZY : Z ⊆ Y) :
    |finiteDensity s X - finiteDensity s Z| ≤ finiteDensity s (Y \ I) := by
  have hIY := hIX.trans hXY
  have hy : Y = I ∪ (Y \ I) := by ext x; simp only [Set.mem_union, Set.mem_sdiff]; have := @hIY x; tauto
  have heq : finiteDensity s Y = finiteDensity s I + finiteDensity s (Y \ I) := by
    conv_lhs => rw [hy]
    exact finiteDensity_union s Set.disjoint_sdiff_right
  rw [abs_le]
  have hiX := finiteDensity_mono s hIX
  have hXy := finiteDensity_mono s hXY
  have hiZ := finiteDensity_mono s hIZ
  have hZy := finiteDensity_mono s hZY
  constructor <;> linarith

lemma sameClass_gap {T I Y : Set E0} (hI : SameClass T I) (hY : SameClass T Y) :
    Small (Y \ I) := by
  apply small_subset (small_union hI hY)
  intro x hx
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_symmDiff] at hx ⊢
  tauto

lemma fProbe_variation (T : Set E0) {X Z : Set E0} {n : ℕ} {δ : ℝ}
    (hp : traceFinset (blockPrefix n) X = traceFinset (blockPrefix n) Z)
    (hd : ∀ m ≥ n, |dProbe T X m - dProbe T Z m| ≤ δ) :
    |fProbe T n X - fProbe T n Z| ≤ 2 * (blockPrefix n).card * δ := by
  have hs := tailSup_lipschitz (dProbe_bddAbove T X) (dProbe_bddAbove T Z) hd
  have hi := tailInf_lipschitz (dProbe_bddBelow T X) (dProbe_bddBelow T Z) hd
  have hsum : |(tailSup (dProbe T X) n + tailInf (dProbe T X) n) -
      (tailSup (dProbe T Z) n + tailInf (dProbe T Z) n)| ≤ 2 * δ := by
    calc
      _ = |(tailSup (dProbe T X) n - tailSup (dProbe T Z) n) +
        (tailInf (dProbe T X) n - tailInf (dProbe T Z) n)| := by congr 1; ring
      _ ≤ |tailSup (dProbe T X) n - tailSup (dProbe T Z) n| +
        |tailInf (dProbe T X) n - tailInf (dProbe T Z) n| := abs_add_le _ _
      _ ≤ 2 * δ := by linarith
  have hf : fProbe T n X - fProbe T n Z = (blockPrefix n).card *
      ((tailSup (dProbe T X) n + tailInf (dProbe T X) n) -
      (tailSup (dProbe T Z) n + tailInf (dProbe T Z) n)) := by
    simp only [fProbe, pProbe, hp]
    ring
  rw [hf, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have h := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ (blockPrefix n).card by positivity)
  linarith

lemma fProbe_block_continuity {T I Y : Set E0} (hI : SameClass T I) (hY : SameClass T Y)
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, j ≤ N ∧ ∀ X Z, I ⊆ X → X ⊆ Y → I ⊆ Z → Z ⊆ Y →
      (∀ x, x.1.1 < N → (x ∈ X ↔ x ∈ Z)) →
      ∀ n ≤ j, |fProbe T n X - fProbe T n Z| < ε := by
  let δ := ε / (2 * ((blockPrefix j).card : ℝ) + 1)
  have hden : (0 : ℝ) < 2 * ((blockPrefix j).card : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have ht := (sameClass_gap hI hY).eventually (gt_mem_nhds hδ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ht
  refine ⟨max j N₀, le_max_left _ _, ?_⟩
  intro X Z hIX hXY hIZ hZY hagree n hnj
  have hnjN : n ≤ max j N₀ := hnj.trans (le_max_left _ _)
  have hp : traceFinset (blockPrefix n) X = traceFinset (blockPrefix n) Z := by
    apply traceFinset_of_agree
    intro x hx
    exact hagree x (((mem_prefix x n).mp hx).trans_le hnjN)
  have hd : ∀ m ≥ n, |dProbe T X m - dProbe T Z m| ≤ δ := by
    intro m hm
    by_cases hmN : m < max j N₀
    · have htr : traceFinset (wBlock m) X = traceFinset (wBlock m) Z := by
        apply traceFinset_of_agree
        intro x hx
        exact hagree x (by simpa only [(mem_wBlock x m).mp hx] using hmN)
      simp [dProbe, density, finiteDensity, htr, hδ.le]
    · have hle : |dProbe T X m - dProbe T Z m| ≤ density (Y \ I) m := by
        dsimp [dProbe, density]
        rw [sub_sub_sub_cancel_right]
        exact finiteDensity_interval (wBlock m) hIX hXY hIZ hZY
      exact hle.trans (hN₀ m (by omega)).le
  have hv := fProbe_variation T hp hd
  have hc : ((blockPrefix n).card : ℝ) ≤ (blockPrefix j).card := by
    exact_mod_cast Finset.card_le_card (prefix_mono hnj)
  have hδeq : δ * (2 * ((blockPrefix j).card : ℝ) + 1) = ε := by
    exact div_mul_cancel₀ ε hden.ne'
  nlinarith

end InfiniteMatroidCounterexample
end

end OAI


