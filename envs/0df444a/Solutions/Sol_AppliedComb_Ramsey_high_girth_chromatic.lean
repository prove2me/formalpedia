-- Prove2me | solution 1 for AppliedComb.Ramsey.high_girth_chromatic
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:59:05.175907+00:00
-- url     : https://prove2.me/submissions/46125f8f-39aa-4753-a9dc-f25bdbc0f73b

import Mathlib

namespace HGC

/-- A cyclic injective tuple of length `m + 3` in `H`. -/
def IsCyc {V : Type*} (H : SimpleGraph V) {m : ℕ} (u : Fin (m + 3) → V) : Prop :=
  Function.Injective u ∧ ∀ i : Fin (m + 3), H.Adj (u i) (u (i + 1))

lemma exists_cyc_of_isCycle {V : Type*} {H : SimpleGraph V} {a : V} {w : H.Walk a a}
    (hw : w.IsCycle) :
    ∃ (m : ℕ) (u : Fin (m + 3) → V), w.length = m + 3 ∧ IsCyc H u := by
  obtain ⟨m, hm⟩ : ∃ m, w.length = m + 3 := ⟨w.length - 3, by have := hw.three_le_length; omega⟩
  refine ⟨m, fun i => w.getVert i.val, hm, ?_, ?_⟩
  · intro i j hij
    have hinj := hw.getVert_injOn'
    have := hinj (by simp only [Set.mem_ofPred_eq]; have := i.2; omega)
      (by simp only [Set.mem_ofPred_eq]; have := j.2; omega) hij
    exact Fin.ext this
  · intro i
    by_cases hi : i.val < m + 2
    · have hval : (i + 1 : Fin (m + 3)).val = i.val + 1 := Fin.val_add_one_of_lt (by
        rw [Fin.lt_def]; simp; omega)
      show H.Adj (w.getVert i.val) (w.getVert (i + 1 : Fin (m + 3)).val)
      rw [hval]
      exact w.adj_getVert_succ (by omega)
    · have hi' : i.val = m + 2 := by have := i.2; omega
      have hval : (i + 1 : Fin (m + 3)) = 0 := by
        apply Fin.ext
        simp [Fin.val_add, hi']
      show H.Adj (w.getVert i.val) (w.getVert (i + 1 : Fin (m + 3)).val)
      rw [hval, hi']
      have h1 := w.adj_getVert_succ (i := m + 2) (by omega)
      have h2 : w.getVert (m + 2 + 1) = a := by
        have := w.getVert_length
        rwa [hm] at this
      simpa [h2, Fin.val_zero, SimpleGraph.Walk.getVert_zero] using h1

end HGC

namespace HGC

open Finset

section weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weight of an edge-flag pattern `x` under independent flags with probability `p`. -/
noncomputable def wt (p : ℝ) (x : ι → Bool) : ℝ := ∏ e, if x e then p else 1 - p

lemma wt_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : ι → Bool) : 0 ≤ wt p x :=
  Finset.prod_nonneg fun e _ => by split_ifs <;> linarith

lemma sum_wt_piFinset (p : ℝ) (t : ι → Finset Bool) :
    ∑ x ∈ Fintype.piFinset t, wt p x = ∏ e, ∑ b ∈ t e, (if b then p else 1 - p) := by
  rw [Finset.prod_univ_sum (fun e => t e) (fun _ b => if b then p else 1 - p)]
  rfl

lemma sum_wt_univ (p : ℝ) : ∑ x : ι → Bool, wt p x = 1 := by
  have h := sum_wt_piFinset (ι := ι) p (fun _ => Finset.univ)
  rw [Fintype.piFinset_univ] at h
  rw [h]
  simp [Fintype.sum_bool]

/-- The weight of the event "all flags in `F₀` equal `b`". -/
lemma sum_wt_event (p : ℝ) (F₀ : Finset ι) (b : Bool) :
    ∑ x ∈ Finset.univ.filter (fun x : ι → Bool => ∀ e ∈ F₀, x e = b), wt p x =
      (if b then p else 1 - p) ^ F₀.card := by
  have hset : Finset.univ.filter (fun x : ι → Bool => ∀ e ∈ F₀, x e = b) =
      Fintype.piFinset (fun e => if e ∈ F₀ then {b} else Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h e
      by_cases he : e ∈ F₀
      · simp [he, h e he]
      · simp [he]
    · intro h e he
      have := h e
      simpa [he] using this
  rw [hset, sum_wt_piFinset]
  have : ∀ e : ι, (∑ c ∈ (if e ∈ F₀ then ({b} : Finset Bool) else Finset.univ),
      (if c then p else 1 - p)) = if e ∈ F₀ then (if b then p else 1 - p) else 1 := by
    intro e
    by_cases he : e ∈ F₀
    · simp [he]
    · simp [he, Fintype.sum_bool]
  simp_rw [this]
  rw [Finset.prod_ite_mem Finset.univ F₀ (fun _ => (if b then p else 1 - p))]
  simp

end weights

end HGC

namespace HGC

open Finset
open scoped Classical

/-- The graph on `Fin n` whose edges are the flagged pairs. -/
def gr {n : ℕ} (x : Sym2 (Fin n) → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | x e = true}

lemma gr_adj {n : ℕ} (x : Sym2 (Fin n) → Bool) (u v : Fin n) :
    (gr x).Adj u v ↔ x s(u, v) = true ∧ u ≠ v := by
  simp [gr, SimpleGraph.fromEdgeSet_adj]

/-- All cyclic edges of the tuple `u` are flagged. -/
def Pres {n m : ℕ} (x : Sym2 (Fin n) → Bool) (u : Fin (m + 3) → Fin n) : Prop :=
  ∀ i, x s(u i, u (i + 1)) = true

/-- The set of cyclic edges of a tuple. -/
noncomputable def edgesOf {V : Type*} {m : ℕ} (u : Fin (m + 3) → V) : Finset (Sym2 V) :=
  Finset.univ.image fun i => s(u i, u (i + 1))

lemma pres_iff {n m : ℕ} (x : Sym2 (Fin n) → Bool) (u : Fin (m + 3) → Fin n) :
    Pres x u ↔ ∀ e ∈ edgesOf u, x e = true := by
  simp [Pres, edgesOf]

lemma fin_succ_ne {m : ℕ} (i : Fin (m + 3)) : i + 1 ≠ i := by
  intro h
  have : (1 : Fin (m + 3)) = 0 := by simpa using h
  exact absurd (congrArg Fin.val this) (by simp)

lemma fin_two_ne {m : ℕ} (j : Fin (m + 3)) : j + 1 + 1 ≠ j := by
  intro h
  have h2 : (1 + 1 : Fin (m + 3)) = 0 := by
    have : j + (1 + 1) = j + 0 := by rw [← add_assoc, add_zero]; exact h
    exact add_left_cancel this
  have h3 : (((1 + 1 : Fin (m + 3)) : ℕ)) = 2 := by
    rw [Fin.val_add]
    simp
  rw [h2] at h3
  simp at h3

lemma edge_inj {V : Type*} {m : ℕ} {u : Fin (m + 3) → V} (hu : Function.Injective u) :
    Function.Injective fun i : Fin (m + 3) => s(u i, u (i + 1)) := by
  intro i j hij
  simp only [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact hu h1
  · have hi : i = j + 1 := hu h1
    have hj : i + 1 = j := hu h2
    rw [hi] at hj
    exact absurd hj (fin_two_ne j)

lemma card_edgesOf {V : Type*} {m : ℕ} {u : Fin (m + 3) → V}
    (hu : Function.Injective u) : (edgesOf u).card = m + 3 := by
  unfold edgesOf
  rw [Finset.card_image_of_injective _ (edge_inj hu)]
  simp

lemma isCyc_gr_iff {n m : ℕ} (x : Sym2 (Fin n) → Bool) (u : Fin (m + 3) → Fin n) :
    IsCyc (gr x) u ↔ Function.Injective u ∧ Pres x u := by
  unfold IsCyc Pres
  constructor
  · rintro ⟨hu, h⟩
    exact ⟨hu, fun i => ((gr_adj x _ _).1 (h i)).1⟩
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun i => (gr_adj x _ _).2 ⟨h i, fun heq => fin_succ_ne i (hu heq).symm⟩⟩

/-- Number of short cyclic tuples present in `x`. -/
noncomputable def Xc (n g : ℕ) (x : Sym2 (Fin n) → Bool) : ℕ :=
  ∑ m ∈ range (g - 2),
    (Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u ∧ Pres x u)).card

/-- Number of independent `a`-sets in `x`. -/
noncomputable def Yc (n a : ℕ) (x : Sym2 (Fin n) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).powersetCard a |>.filter
    (fun S => ∀ u ∈ S, ∀ v ∈ S, u ≠ v → x s(u, v) = false)).card

/-- General first-moment identity. -/
lemma sum_wt_mul_card_filter {ι κ : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (b : Bool)
    (𝒯 : Finset κ) (F : κ → Finset ι) :
    ∑ x : ι → Bool, wt p x * ((𝒯.filter (fun τ => ∀ e ∈ F τ, x e = b)).card : ℝ) =
      ∑ τ ∈ 𝒯, (if b then p else 1 - p) ^ (F τ).card := by
  have h1 : ∀ x : ι → Bool, wt p x * ((𝒯.filter (fun τ => ∀ e ∈ F τ, x e = b)).card : ℝ) =
      ∑ τ ∈ 𝒯, if (∀ e ∈ F τ, x e = b) then wt p x else 0 := by
    intro x
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← sum_wt_event p (F τ) b, Finset.sum_filter]


/-- Expected number of short cyclic tuples. -/
lemma sum_wt_Xc {n g : ℕ} {p : ℝ} (hp : 0 ≤ p) :
    ∑ x : Sym2 (Fin n) → Bool, wt p x * (Xc n g x : ℝ) ≤
      ∑ m ∈ range (g - 2), ((n : ℝ) * p) ^ (m + 3) := by
  have key : ∀ m : ℕ, ∑ x : Sym2 (Fin n) → Bool, wt p x *
      ((Finset.univ.filter (fun u : Fin (m + 3) → Fin n =>
        Function.Injective u ∧ Pres x u)).card : ℝ) ≤ ((n : ℝ) * p) ^ (m + 3) := by
    intro m
    have hcard : ∀ x : Sym2 (Fin n) → Bool,
        (Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u ∧ Pres x u)) =
        ((Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u)).filter
          (fun u => ∀ e ∈ edgesOf u, x e = true)) := by
      intro x
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun u _ => ?_
      rw [pres_iff]
    simp_rw [hcard]
    rw [sum_wt_mul_card_filter p true]
    simp only [if_true]
    have : ∀ u ∈ (Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u)),
        p ^ (edgesOf u).card = p ^ (m + 3) := by
      intro u hu
      rw [card_edgesOf (Finset.mem_filter.1 hu).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    have hle : ((Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u)).card : ℝ)
        ≤ (n : ℝ) ^ (m + 3) := by
      have : (Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u)).card ≤
          n ^ (m + 3) := by
        calc _ ≤ (Finset.univ : Finset (Fin (m + 3) → Fin n)).card := Finset.card_filter_le _ _
          _ = n ^ (m + 3) := by simp
      exact_mod_cast this
    calc _ ≤ (n : ℝ) ^ (m + 3) * p ^ (m + 3) := by gcongr
      _ = ((n : ℝ) * p) ^ (m + 3) := (mul_pow _ _ _).symm
  unfold Xc
  simp_rw [Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun m _ => key m

lemma indep_iff_forall_edges {n : ℕ} (x : Sym2 (Fin n) → Bool) (S : Finset (Fin n)) :
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → x s(u, v) = false) ↔
      ∀ e ∈ S.offDiag.image Sym2.mk.uncurry, x e = false := by
  constructor
  · intro h e he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 he
    rw [Finset.mem_offDiag] at huv
    exact h u huv.1 v huv.2.1 huv.2.2
  · intro h u hu v hv huv
    exact h _ (Finset.mem_image.2 ⟨(u, v), Finset.mem_offDiag.2 ⟨hu, hv, huv⟩, rfl⟩)

/-- Expected number of independent `a`-sets. -/
lemma sum_wt_Yc (n a : ℕ) (p : ℝ) :
    ∑ x : Sym2 (Fin n) → Bool, wt p x * (Yc n a x : ℝ) =
      (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) := by
  have hY : ∀ x : Sym2 (Fin n) → Bool, Yc n a x =
      (((Finset.univ : Finset (Fin n)).powersetCard a).filter
        (fun S => ∀ e ∈ S.offDiag.image Sym2.mk.uncurry, x e = false)).card := by
    intro x
    unfold Yc
    congr 1
    exact Finset.filter_congr fun S _ => indep_iff_forall_edges x S
  simp_rw [hY]
  rw [sum_wt_mul_card_filter p false]
  simp only [Bool.false_eq_true, if_false]
  have : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard a,
      (1 - p) ^ (S.offDiag.image Sym2.mk.uncurry).card = (1 - p) ^ (a.choose 2) := by
    intro S hS
    rw [Sym2.card_image_offDiag, (Finset.mem_powersetCard.1 hS).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  simp

/-- A flag pattern with few short cycles and no large independent set. -/
lemma exists_good_flags {n g a : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    (hX : ∑ m ∈ range (g - 2), ((n : ℝ) * p) ^ (m + 3) < n / 4)
    (hY : (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) < 1 / 2) :
    ∃ x : Sym2 (Fin n) → Bool, (Xc n g x : ℝ) < n / 2 ∧ Yc n a x = 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra hcon
  push Not at hcon
  have hZ : ∀ x : Sym2 (Fin n) → Bool, 1 ≤ (Yc n a x : ℝ) + 2 / n * (Xc n g x : ℝ) := by
    intro x
    by_cases h : (Xc n g x : ℝ) < n / 2
    · have hy : Yc n a x ≠ 0 := hcon x h
      have : (1 : ℝ) ≤ (Yc n a x : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hy
      have : 0 ≤ 2 / (n : ℝ) * (Xc n g x : ℝ) := by positivity
      linarith
    · push Not at h
      have : (1 : ℝ) ≤ 2 / n * (Xc n g x : ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hnr]; linarith
      have : (0 : ℝ) ≤ (Yc n a x : ℝ) := Nat.cast_nonneg _
      linarith
  have hsum : ∑ x : Sym2 (Fin n) → Bool, wt p x * 1 ≤
      ∑ x : Sym2 (Fin n) → Bool, wt p x * ((Yc n a x : ℝ) + 2 / n * (Xc n g x : ℝ)) :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hZ x) (wt_nonneg hp0 hp1 x)
  simp only [mul_one, sum_wt_univ] at hsum
  have hexp : ∑ x : Sym2 (Fin n) → Bool, wt p x * ((Yc n a x : ℝ) + 2 / n * (Xc n g x : ℝ)) =
      (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) +
        2 / n * ∑ x : Sym2 (Fin n) → Bool, wt p x * (Xc n g x : ℝ) := by
    rw [← sum_wt_Yc n a p, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hXb := sum_wt_Xc (n := n) (g := g) hp0
  have h2n : 0 ≤ 2 / (n : ℝ) := by positivity
  have : 2 / (n : ℝ) * ∑ x : Sym2 (Fin n) → Bool, wt p x * (Xc n g x : ℝ) <
      2 / (n : ℝ) * ((n : ℝ) / 4) := by
    calc _ ≤ 2 / (n : ℝ) * ∑ m ∈ range (g - 2), ((n : ℝ) * p) ^ (m + 3) :=
          mul_le_mul_of_nonneg_left hXb h2n
      _ < _ := mul_lt_mul_of_pos_left hX (by positivity)
  have h3 : 2 / (n : ℝ) * ((n : ℝ) / 4) = 1 / 2 := by field_simp; ring
  linarith

end HGC

namespace HGC

open Finset
open scoped Classical

lemma exists_graph {n g a t : ℕ} (hg : 3 ≤ g) {x : Sym2 (Fin n) → Bool}
    (hX : (Xc n g x : ℝ) < n / 2) (hY : Yc n a x = 0) (hbig : 2 * (t * a) ≤ n) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)),
      (t : ℕ∞) < G.chromaticNumber ∧ (g : ℕ∞) < G.egirth := by
  -- the deletion set: one vertex of every short cycle
  let D : Finset (Fin n) := (range (g - 2)).biUnion fun m =>
    (Finset.univ.filter (fun u : Fin (m + 3) → Fin n =>
      Function.Injective u ∧ Pres x u)).image (fun u => u 0)
  have hD : D.card ≤ Xc n g x := by
    calc D.card ≤ ∑ m ∈ range (g - 2), ((Finset.univ.filter (fun u : Fin (m + 3) → Fin n =>
          Function.Injective u ∧ Pres x u)).image (fun u => u 0)).card := Finset.card_biUnion_le
      _ ≤ ∑ m ∈ range (g - 2), (Finset.univ.filter (fun u : Fin (m + 3) → Fin n =>
          Function.Injective u ∧ Pres x u)).card :=
          Finset.sum_le_sum fun m _ => Finset.card_image_le
      _ = Xc n g x := rfl
  have hD2 : 2 * D.card < n := by
    have : (D.card : ℝ) ≤ Xc n g x := by exact_mod_cast hD
    have : (2 * D.card : ℝ) < n := by linarith
    exact_mod_cast this
  set K : Finset (Fin n) := Dᶜ with hK
  have hKcard : K.card = n - D.card := by
    rw [hK, Finset.card_compl, Fintype.card_fin]
  set N : ℕ := K.card with hN
  let e : Fin N ↪o Fin n := K.orderEmbOfFin rfl
  have he_mem : ∀ i, e i ∈ K := fun i => Finset.orderEmbOfFin_mem K rfl i
  let G : SimpleGraph (Fin N) := (gr x).comap e
  have hGadj : ∀ u v : Fin N, G.Adj u v ↔ x s(e u, e v) = true ∧ e u ≠ e v := fun u v => by
    show (gr x).Adj (e u) (e v) ↔ _
    exact gr_adj x _ _
  refine ⟨N, G, ?_, ?_⟩
  · -- chromatic number
    by_contra hnot
    rw [not_lt, SimpleGraph.chromaticNumber_le_iff_colorable] at hnot
    obtain ⟨c⟩ := hnot
    have hfiber : ∀ col : Fin t,
        (Finset.univ.filter (fun i : Fin N => c i = col)).card < a := by
      intro col
      by_contra hge
      push Not at hge
      obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hge
      have h1 : 1 ≤ Yc n a x := by
        unfold Yc
        apply Finset.card_pos.2
        refine ⟨T.image e, Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2
          ⟨Finset.subset_univ _, ?_⟩, ?_⟩⟩
        · rw [Finset.card_image_of_injective _ e.injective, hTcard]
        · intro u hu v hv huv
          obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨v', hv', rfl⟩ := Finset.mem_image.1 hv
          have hcu := (Finset.mem_filter.1 (hT hu')).2
          have hcv := (Finset.mem_filter.1 (hT hv')).2
          by_contra hne
          have hx : x s(e u', e v') = true := by simpa using hne
          have hadj : G.Adj u' v' := (hGadj u' v').2 ⟨hx, huv⟩
          exact c.valid hadj (hcu.trans hcv.symm)
      omega
    have hNle : N ≤ t * a := by
      have h1 : (Finset.univ : Finset (Fin N)).card =
          ∑ col : Fin t, (Finset.univ.filter (fun i : Fin N => c i = col)).card :=
        Finset.card_eq_sum_card_fiberwise (f := c) (fun _ _ => Finset.mem_univ _)
      have h2 : ∑ col : Fin t, (Finset.univ.filter (fun i : Fin N => c i = col)).card ≤
          ∑ _col : Fin t, a := Finset.sum_le_sum fun col _ => (hfiber col).le
      simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const, smul_eq_mul] at h1 h2
      omega
    have hNgt : n < 2 * N := by omega
    generalize t * a = k at *
    omega
  · -- girth
    have hle : ((g + 1 : ℕ) : ℕ∞) ≤ G.egirth := by
      rw [SimpleGraph.le_egirth]
      intro a' w hw
      obtain ⟨m, u, hlen, hcyc⟩ := exists_cyc_of_isCycle hw
      rw [hlen]
      by_contra hlt
      have hmg : m + 3 ≤ g := by
        have : ¬ (g + 1 ≤ m + 3) := by exact_mod_cast hlt
        omega
      let τ : Fin (m + 3) → Fin n := fun i => e (u i)
      have hτinj : Function.Injective τ := e.injective.comp hcyc.1
      have hτpres : Pres x τ := by
        intro i
        exact ((hGadj _ _).1 (hcyc.2 i)).1
      have hmem : τ 0 ∈ D :=
        Finset.mem_biUnion.2 ⟨m, Finset.mem_range.2 (by omega),
          Finset.mem_image.2 ⟨τ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hτinj, hτpres⟩, rfl⟩⟩
      exact (Finset.mem_compl.1 (he_mem (u 0))) hmem
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self g) hle

end HGC

namespace HGC

open Finset

lemma two_pow_ge_sq : ∀ j : ℕ, 4 ≤ j → j ^ 2 ≤ 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      _ ≤ k ^ 2 + k ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

/-- The independent-set first moment is small. -/
lemma bound_Y {n q mm a : ℕ} {L : ℝ} (hL : 0 ≤ L) (hq : 2 ≤ q) (hn : (n : ℝ) ≤ Real.exp L)
    (hmm : (mm : ℝ) = 4 * L + 4) (ha : a = q * mm) :
    (n.choose a : ℝ) * (1 - 1 / (q : ℝ)) ^ (a.choose 2) < 1 / 2 := by
  have hQ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hQpos : (0 : ℝ) < q := by linarith
  have hM8 : (4 : ℝ) ≤ mm := by rw [hmm]; linarith
  have hA : (a : ℝ) = q * mm := by rw [ha]; push_cast; ring
  have hA8 : (8 : ℝ) ≤ a := by rw [hA]; nlinarith
  -- choose ≤ n ^ a ≤ exp (a L)
  have h1 : (n.choose a : ℝ) ≤ Real.exp (a * L) := by
    calc (n.choose a : ℝ) ≤ (n : ℝ) ^ a := by exact_mod_cast Nat.choose_le_pow n a
      _ ≤ (Real.exp L) ^ a := by gcongr
      _ = Real.exp (a * L) := (Real.exp_nat_mul L a).symm
  -- (1 - 1/q) ^ C ≤ exp (- C / q)
  have hbase : 0 ≤ 1 - 1 / (q : ℝ) := by
    have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hQpos]; linarith
    linarith
  have h2 : (1 - 1 / (q : ℝ)) ^ (a.choose 2) ≤ Real.exp ((a.choose 2 : ℕ) * (-(1 / (q : ℝ)))) := by
    calc (1 - 1 / (q : ℝ)) ^ (a.choose 2) ≤ (Real.exp (-(1 / (q : ℝ)))) ^ (a.choose 2) := by
          gcongr
          have := Real.add_one_le_exp (-(1 / (q : ℝ)))
          linarith
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hC : ((a.choose 2 : ℕ) : ℝ) * (1 / (q : ℝ)) = (mm : ℝ) * (a - 1) / 2 := by
    rw [Nat.cast_choose_two, hA]
    field_simp
  have hprod : (n.choose a : ℝ) * (1 - 1 / (q : ℝ)) ^ (a.choose 2) ≤
      Real.exp (a * L - (mm : ℝ) * (a - 1) / 2) := by
    calc _ ≤ Real.exp (a * L) * Real.exp ((a.choose 2 : ℕ) * (-(1 / (q : ℝ)))) := by
          apply mul_le_mul h1 h2 (pow_nonneg hbase _) (Real.exp_pos _).le
      _ = Real.exp (a * L + (a.choose 2 : ℕ) * (-(1 / (q : ℝ)))) := (Real.exp_add _ _).symm
      _ = _ := by
          congr 1
          have : ((a.choose 2 : ℕ) : ℝ) * (-(1 / (q : ℝ))) = -(((a.choose 2 : ℕ) : ℝ) * (1 / (q : ℝ))) := by ring
          rw [this, hC]; ring
  have hexp : (a : ℝ) * L - (mm : ℝ) * (a - 1) / 2 ≤ -1 := by
    rw [hmm]
    nlinarith [mul_nonneg hL (sub_nonneg.2 (show (2 : ℝ) ≤ a by linarith))]
  have hexp1 : Real.exp ((a : ℝ) * L - (mm : ℝ) * (a - 1) / 2) ≤ Real.exp (-1) :=
    Real.exp_le_exp.2 hexp
  have hgt : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  have hneg : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    simpa using hgt
  linarith

end HGC

open HGC Finset in
theorem solution (g t : ℕ) (hg : 3 ≤ g) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)),
      (t : ℕ∞) < G.chromaticNumber ∧ (g : ℕ∞) < G.egirth := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = 4 * g + 16 * t * g + 8 * t + 4 := ⟨_, rfl⟩
  have hj4 : 4 ≤ j := by omega
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = 2 ^ j := ⟨_, rfl⟩
  have hs2 : 2 ≤ s := by
    rw [hs]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsj : j < s := by rw [hs]; exact Nat.lt_two_pow_self
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = s ^ (2 * g - 1) := ⟨_, rfl⟩
  have hq2 : 2 ≤ q := by
    have : s ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) s
    omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = q * s := ⟨_, rfl⟩
  have hn_eq : n = s ^ (2 * g) := by
    rw [hn, hq, ← pow_succ]
    congr 1
    omega
  obtain ⟨mm, hmm⟩ : ∃ mm : ℕ, mm = 8 * g * j + 4 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = q * mm := ⟨_, rfl⟩
  -- the size condition
  have hH2 : 2 * t * mm ≤ s := by
    have h1 : j ^ 2 ≤ 2 ^ j := two_pow_ge_sq j hj4
    calc 2 * t * mm = 16 * t * g * j + 8 * t := by rw [hmm]; ring
      _ ≤ 16 * t * g * j + 8 * t * j := by
          have : 8 * t ≤ 8 * t * j := Nat.le_mul_of_pos_right _ (by omega)
          omega
      _ = (16 * t * g + 8 * t) * j := by ring
      _ ≤ j * j := Nat.mul_le_mul_right _ (by omega)
      _ = j ^ 2 := (sq j).symm
      _ ≤ 2 ^ j := h1
      _ = s := hs.symm
  have hbig : 2 * (t * a) ≤ n := by
    calc 2 * (t * a) = q * (2 * t * mm) := by rw [ha]; ring
      _ ≤ q * s := Nat.mul_le_mul_left _ hH2
      _ = n := hn.symm
  have hnpos : 0 < n := by rw [hn]; positivity
  -- real parameters
  have hQ : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hQpos : (0 : ℝ) < q := by linarith
  have hp0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have hp1 : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hQpos]; linarith
  have hnp : (n : ℝ) * (1 / (q : ℝ)) = (s : ℝ) := by
    rw [hn]; push_cast; field_simp
  -- first moment of short cycles
  have hX : ∑ m ∈ range (g - 2), ((n : ℝ) * (1 / (q : ℝ))) ^ (m + 3) < (n : ℝ) / 4 := by
    rw [hnp]
    have hS1 : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
    have hSpos : (0 : ℝ) < s := by linarith
    have hterm : ∀ m ∈ range (g - 2), ((s : ℝ)) ^ (m + 3) ≤ (s : ℝ) ^ g := by
      intro m hm
      exact pow_le_pow_right₀ hS1 (by have := Finset.mem_range.1 hm; omega)
    have hsum : ∑ m ∈ range (g - 2), ((s : ℝ)) ^ (m + 3) ≤ (g : ℝ) * (s : ℝ) ^ g := by
      calc _ ≤ ∑ _m ∈ range (g - 2), (s : ℝ) ^ g := Finset.sum_le_sum hterm
        _ = ((g - 2 : ℕ) : ℝ) * (s : ℝ) ^ g := by simp
        _ ≤ (g : ℝ) * (s : ℝ) ^ g := by
            gcongr
            exact_mod_cast Nat.sub_le g 2
    have h4g : (4 * g : ℝ) < (s : ℝ) ^ g := by
      have h1 : 4 * g < s := by omega
      have h2 : s ≤ s ^ g := Nat.le_self_pow (by omega) s
      exact_mod_cast lt_of_lt_of_le h1 h2
    have hn' : (n : ℝ) = (s : ℝ) ^ g * (s : ℝ) ^ g := by
      rw [hn_eq, ← pow_add]; push_cast; ring_nf
    have hpos : (0 : ℝ) < (s : ℝ) ^ g := by positivity
    calc _ ≤ (g : ℝ) * (s : ℝ) ^ g := hsum
      _ < (n : ℝ) / 4 := by
          rw [hn']
          nlinarith
  -- first moment of independent sets
  have hn_exp : (n : ℝ) ≤ Real.exp ((j * (2 * g) : ℕ) : ℝ) := by
    have h1 : n = 2 ^ (j * (2 * g)) := by rw [hn_eq, hs, ← pow_mul]
    rw [h1]
    push_cast
    calc ((2 : ℝ)) ^ (j * (2 * g)) ≤ (Real.exp 1) ^ (j * (2 * g)) := by
          gcongr
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
      _ = Real.exp (((j * (2 * g) : ℕ) : ℝ) * 1) := (Real.exp_nat_mul 1 _).symm
      _ = _ := by push_cast; ring_nf
  have hmmL : (mm : ℝ) = 4 * ((j * (2 * g) : ℕ) : ℝ) + 4 := by
    rw [hmm]; push_cast; ring
  have hY := bound_Y (n := n) (q := q) (mm := mm) (a := a)
    (L := ((j * (2 * g) : ℕ) : ℝ)) (Nat.cast_nonneg _) hq2 hn_exp hmmL ha
  obtain ⟨x, hx1, hx2⟩ := exists_good_flags (n := n) (g := g) (a := a) hp0 hp1 hnpos hX hY
  exact exists_graph hg hx1 hx2 hbig
