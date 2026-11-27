-- Prove2me | solution 1 for AbelianCayleyHDX.Supplement.explicit_cube_label_family_log
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:02:56.644119+00:00
-- url     : https://prove2.me/submissions/5856d3cc-7e3a-4f47-9557-33ed7e4f1673

import Mathlib
import Definitions.Def_AbelianCayleyHDX_Supplement_cubeLabelComplex
import Definitions.Def_AbelianCayleyHDX_edges
import Definitions.Def_AbelianCayleyHDX_Supplement_faceMass
import Definitions.Def_OAIQ053K038
import Definitions.Def_OAIQ053K039
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_AbelianCayleyHDX_encRat
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AbelianCayleyHDX_Supplement_IsExplicitWeightedFamily
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset

/-! ### Positions and labels -/

section Basic
variable {k a : ℕ}

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

lemma vadd_self' {m : ℕ} (x : Vec m) : x + x = 0 := by
  ext i; simp only [Pi.add_apply, Pi.zero_apply]; exact z2_add_self _

lemma pos_add (x y : Vec (k + a)) : pos (x + y) = pos x + pos y := rfl
lemma lab_add (x y : Vec (k + a)) : lab (x + y) = lab x + lab y := rfl
lemma pos_zero : pos (0 : Vec (k + a)) = 0 := rfl
lemma lab_zero : lab (0 : Vec (k + a)) = 0 := rfl

/-- Assemble a vertex from its cube coordinate and its label. -/
def emb (u : Vec k) (b : Vec a) : Vec (k + a) := Fin.append u b

@[simp] lemma pos_emb (u : Vec k) (b : Vec a) : pos (emb u b) = u := by
  funext i; simp [pos, emb, Fin.append_left]

@[simp] lemma lab_emb (u : Vec k) (b : Vec a) : lab (emb u b) = b := by
  funext i; simp [lab, emb, Fin.append_right]

lemma emb_pos_lab (x : Vec (k + a)) : emb (pos x) (lab x) = x := by
  simp only [emb, pos, lab]
  exact Fin.append_castAdd_natAdd

lemma ext_pl {x y : Vec (k + a)} (h1 : pos x = pos y) (h2 : lab x = lab y) : x = y := by
  rw [← emb_pos_lab x, ← emb_pos_lab y, h1, h2]

lemma emb_add (u u' : Vec k) (b b' : Vec a) : emb u b + emb u' b' = emb (u + u') (b + b') := by
  apply ext_pl <;> simp [pos_add, lab_add]

lemma vec_eq_iff_add_eq_zero {m : ℕ} (x y : Vec m) : x = y ↔ x + y = 0 := by
  constructor
  · rintro rfl; exact vadd_self' x
  · intro h; have := congrArg (· + y) h; simpa [add_assoc, vadd_self'] using this

/-- Two cube coordinates are equal or adjacent. -/
def PosAdj (u v : Vec k) : Prop := u + v = 0 ∨ ∃ i : Fin k, u + v = Pi.single i 1

lemma posAdj_symm {u v : Vec k} : PosAdj u v → PosAdj v u := by
  unfold PosAdj; rw [add_comm]; exact id

lemma mem_gens {s : Vec (k + a)} :
    s ∈ gens k a ↔ lab s ≠ 0 ∧ PosAdj (pos s) 0 := by
  simp [gens, PosAdj]

lemma add_mem_gens {x y : Vec (k + a)} :
    x + y ∈ gens k a ↔ lab x ≠ lab y ∧ PosAdj (pos x) (pos y) := by
  rw [mem_gens, lab_add, pos_add]
  simp only [PosAdj, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by rw [h, vadd_self']), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 ((vec_eq_iff_add_eq_zero _ _).2 h), h2⟩

/-- Unit vectors: `e_i + e_j` is neither `0` nor a unit vector when `i ≠ j`. -/
lemma single_add_single_ne {i j : Fin k} (hij : i ≠ j) :
    (Pi.single i 1 + Pi.single j 1 : Vec k) ≠ 0 ∧
      ∀ l, (Pi.single i 1 + Pi.single j 1 : Vec k) ≠ Pi.single l 1 := by
  constructor
  · intro h; have := congrFun h i; simp [Pi.single_apply, hij] at this
  · intro l h
    have hi : (Pi.single l (1 : ZMod 2) : Vec k) i = 1 := by rw [← h]; simp [hij]
    have hj : (Pi.single l (1 : ZMod 2) : Vec k) j = 1 := by rw [← h]; simp [Ne.symm hij]
    have h1 : i = l := by
      by_contra hne; rw [Pi.single_apply, if_neg hne] at hi; exact zero_ne_one hi
    have h2 : j = l := by
      by_contra hne; rw [Pi.single_apply, if_neg hne] at hj; exact zero_ne_one hj
    exact hij (h1.trans h2.symm)

lemma single_ne_zero' (i : Fin k) : (Pi.single i 1 : Vec k) ≠ 0 := by
  intro h; have := congrFun h i; simp at this

lemma single_inj' {i j : Fin k} (h : (Pi.single i 1 : Vec k) = Pi.single j 1) : i = j := by
  by_contra hij
  have := congrFun h i
  simp [Pi.single_apply, hij] at this

end Basic

/-! ### Cliques -/

section Cliques
variable {d k a : ℕ}

/-- A clique of the Cayley graph. -/
def IsClique (T : Finset (Vec (k + a))) : Prop := ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x + y ∈ gens k a

lemma mem_tops {T : Finset (Vec (k + a))} : T ∈ tops d k a ↔ T.card = d + 1 ∧ IsClique T := by
  simp [tops, IsClique]

lemma IsClique.subset {T T' : Finset (Vec (k + a))} (h : IsClique T) (hs : T' ⊆ T) :
    IsClique T' := fun x hx y hy hxy => h x (hs hx) y (hs hy) hxy

lemma IsClique.lab_inj {T : Finset (Vec (k + a))} (h : IsClique T) {x y : Vec (k + a)}
    (hx : x ∈ T) (hy : y ∈ T) (hl : lab x = lab y) : x = y := by
  by_contra hxy
  exact (add_mem_gens.1 (h x hx y hy hxy)).1 hl

lemma IsClique.posAdj {T : Finset (Vec (k + a))} (h : IsClique T) {x y : Vec (k + a)}
    (hx : x ∈ T) (hy : y ∈ T) : PosAdj (pos x) (pos y) := by
  by_cases hxy : x = y
  · subst hxy; left; exact vadd_self' _
  · exact (add_mem_gens.1 (h x hx y hy hxy)).2

/-- The positions of a clique lie in one cube edge: if `x, y, z` are in a clique and
`pos y ≠ pos x`, then `pos z ∈ {pos x, pos y}`. -/
lemma IsClique.pos_two {T : Finset (Vec (k + a))} (h : IsClique T) {x y z : Vec (k + a)}
    (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T) (hxy : pos x ≠ pos y) :
    pos z = pos x ∨ pos z = pos y := by
  have h1 := h.posAdj hx hy
  have h2 := h.posAdj hx hz
  have h3 := h.posAdj hy hz
  rcases h1 with h1 | ⟨i, hi⟩
  · exact absurd ((vec_eq_iff_add_eq_zero _ _).2 h1) hxy
  rcases h2 with h2 | ⟨j, hj⟩
  · left; exact ((vec_eq_iff_add_eq_zero _ _).2 h2).symm
  rcases h3 with h3 | ⟨l, hl⟩
  · right; exact ((vec_eq_iff_add_eq_zero _ _).2 h3).symm
  -- pos y = pos x + e_i, pos z = pos x + e_j, pos y + pos z = e_l
  exfalso
  have : (Pi.single i 1 + Pi.single j 1 : Vec k) = Pi.single l 1 := by
    rw [← hi, ← hj, ← hl]
    ext t; simp only [Pi.add_apply]
    generalize pos x t = p; generalize pos y t = q; generalize pos z t = r
    revert p q r; decide
  by_cases hij : i = j
  · subst hij
    rw [vadd_self'] at this
    exact single_ne_zero' l this.symm
  · exact (single_add_single_ne hij).2 l this

/-- A nonempty clique with at most `d + 1` points extends to a top face, when there are at least
`d + 1` labels. -/
lemma exists_top_of_clique (ha : d + 1 ≤ 2 ^ a) {σ : Finset (Vec (k + a))} (hσ : IsClique σ)
    (hne : σ.Nonempty) (hcard : σ.card ≤ d + 1) : ∃ τ ∈ tops d k a, σ ⊆ τ := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  -- fresh labels
  set fresh := (Finset.univ : Finset (Vec a)) \ σ.image lab with hfresh
  have hfc : d + 1 - σ.card ≤ fresh.card := by
    rw [hfresh, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have : (σ.image lab).card ≤ σ.card := Finset.card_image_le
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    omega
  obtain ⟨Λ, hΛ, hΛc⟩ := Finset.exists_subset_card_eq hfc
  set new := Λ.image (emb (pos x0)) with hnew
  have hnewc : new.card = Λ.card := Finset.card_image_of_injective _ (fun b b' h => by
    simpa using congrArg lab h)
  have hdisj : Disjoint σ new := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy'
    have := hΛ hb
    rw [hfresh, Finset.mem_sdiff] at this
    exact this.2 (Finset.mem_image.2 ⟨_, hy, by simp⟩)
  refine ⟨σ ∪ new, ?_, Finset.subset_union_left⟩
  rw [mem_tops]
  refine ⟨?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hnewc, hΛc]; omega
  · intro y hy z hz hyz
    rw [Finset.mem_union] at hy hz
    rw [add_mem_gens]
    have hfr : ∀ b ∈ Λ, b ∉ σ.image lab := by
      intro b hb; have := hΛ hb; rw [hfresh, Finset.mem_sdiff] at this; exact this.2
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact add_mem_gens.1 (hσ y hy z hz hyz)
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
      refine ⟨fun h => hfr b hb (Finset.mem_image.2 ⟨y, hy, by simpa using h⟩), ?_⟩
      simpa using hσ.posAdj hy hx0
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      refine ⟨fun h => hfr b hb (Finset.mem_image.2 ⟨z, hz, by simpa using h.symm⟩), ?_⟩
      simpa using hσ.posAdj hx0 hz
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hz
      refine ⟨fun h => hyz (by simp at h; rw [h]), ?_⟩
      left; simp [vadd_self']

end Cliques

end AbelianCayleyHDX.Supplement.CubeLabel

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset

variable {d k a : ℕ}

/-- The number of points of `T` in the fibre of `x`. -/
def cnt (T : Finset (Vec (k + a))) (x : Vec (k + a)) : ℕ := (T.filter fun y => pos y = pos x).card

lemma cnt_pos {T : Finset (Vec (k + a))} {x : Vec (k + a)} (hx : x ∈ T) : 1 ≤ cnt T x :=
  Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hx, rfl⟩⟩

lemma cnt_add_cnt {T : Finset (Vec (k + a))} (hT : IsClique T) {x y : Vec (k + a)} (hx : x ∈ T)
    (hy : y ∈ T) (hxy : pos x ≠ pos y) : cnt T x + cnt T y = T.card := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext z
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro hz
      rcases hT.pos_two hx hy hz hxy with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  · rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_filter] at hz hz'
    exact hxy (hz.2.symm.trans hz'.2)

lemma choose_cnt_eq (hd : 1 ≤ d) {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a)
    {x y : Vec (k + a)} (hx : x ∈ T) (hy : y ∈ T) :
    Nat.choose (d - 1) (cnt T x - 1) = Nat.choose (d - 1) (cnt T y - 1) := by
  rw [mem_tops] at hT
  by_cases hxy : pos x = pos y
  · unfold cnt; rw [hxy]
  · have h := cnt_add_cnt hT.2 hx hy hxy
    rw [hT.1] at h
    have h1 := cnt_pos (T := T) hx
    have h2 := cnt_pos (T := T) hy
    rw [← Nat.choose_symm (by omega : cnt T x - 1 ≤ d - 1)]
    congr 1; omega

lemma weight_single {T : Finset (Vec (k + a))} (h : ∀ x ∈ T, ∀ y ∈ T, pos x = pos y) :
    weight d k a T = ((d : ℚ) - 1) * k := by
  unfold weight; rw [if_pos h]

lemma weight_split (hd : 1 ≤ d) {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a)
    (h : ¬ ∀ x ∈ T, ∀ y ∈ T, pos x = pos y) {x : Vec (k + a)} (hx : x ∈ T) :
    weight d k a T = 1 / (Nat.choose (d - 1) (cnt T x - 1) : ℚ) := by
  unfold weight
  rw [if_neg h]
  have hcard := (mem_tops.1 hT).1
  have : ∀ y ∈ T, (1 : ℚ) / (Nat.choose (d - 1) ((T.filter fun z => pos z = pos y).card - 1) : ℚ) =
      1 / (Nat.choose (d - 1) (cnt T x - 1) : ℚ) := by
    intro y hy
    have := choose_cnt_eq hd hT hy hx
    unfold cnt at this
    rw [this]; rfl
  rw [Finset.sum_congr rfl this, Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast
  field_simp

lemma choose_pos_of_mem (hd : 1 ≤ d) {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a)
    (h : ¬ ∀ x ∈ T, ∀ y ∈ T, pos x = pos y) {x : Vec (k + a)} (hx : x ∈ T) :
    0 < Nat.choose (d - 1) (cnt T x - 1) := by
  apply Nat.choose_pos
  push Not at h
  obtain ⟨y, hy, z, hz, hyz⟩ := h
  have hT' := mem_tops.1 hT
  -- `x` has a point of `T` in another fibre
  obtain ⟨w, hw, hxw⟩ : ∃ w ∈ T, pos x ≠ pos w := by
    by_cases h1 : pos x = pos y
    · exact ⟨z, hz, h1 ▸ hyz⟩
    · exact ⟨y, hy, h1⟩
  have := cnt_add_cnt hT'.2 hx hw hxw
  have := cnt_pos (T := T) hw
  omega

lemma weight_pos (hd : 2 ≤ d) (hk : 1 ≤ k) {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a) :
    0 < weight d k a T := by
  by_cases h : ∀ x ∈ T, ∀ y ∈ T, pos x = pos y
  · rw [weight_single h]
    have : (2 : ℚ) ≤ d := by exact_mod_cast hd
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    nlinarith
  · have hne : T.Nonempty := by
      rw [← Finset.card_pos, (mem_tops.1 hT).1]; omega
    obtain ⟨x, hx⟩ := hne
    rw [weight_split (by omega) hT h hx]
    have := choose_pos_of_mem (by omega) hT h hx
    positivity

/-! ### Translation invariance -/

lemma image_add_injective (g : Vec (k + a)) : Function.Injective fun x : Vec (k + a) => x + g :=
  add_left_injective g

lemma clique_image_add {T : Finset (Vec (k + a))} (hT : IsClique T) (g : Vec (k + a)) :
    IsClique (T.image (· + g)) := by
  intro x hx y hy hxy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
  have : x' + g + (y' + g) = x' + y' := by
    rw [add_add_add_comm, vadd_self', add_zero]
  rw [this]
  exact hT x' hx' y' hy' (fun h => hxy (by rw [h]))

lemma tops_image_add {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a) (g : Vec (k + a)) :
    T.image (· + g) ∈ tops d k a := by
  rw [mem_tops] at hT ⊢
  refine ⟨?_, clique_image_add hT.2 g⟩
  rw [Finset.card_image_of_injective _ (image_add_injective g), hT.1]

lemma filter_card_image_add (T : Finset (Vec (k + a))) (g x : Vec (k + a)) :
    ((T.image (· + g)).filter fun y => pos y = pos (x + g)).card =
      (T.filter fun y => pos y = pos x).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (image_add_injective g)]
  congr 1
  apply Finset.filter_congr
  intro y _
  simp only [Function.comp, pos_add]
  exact ⟨fun h => add_right_cancel h, fun h => by rw [h]⟩

lemma weight_image_add (T : Finset (Vec (k + a))) (g : Vec (k + a)) :
    weight d k a (T.image (· + g)) = weight d k a T := by
  unfold weight
  have hall : (∀ x ∈ T.image (· + g), ∀ y ∈ T.image (· + g), pos x = pos y) ↔
      ∀ x ∈ T, ∀ y ∈ T, pos x = pos y := by
    constructor
    · intro h x hx y hy
      have := h (x + g) (Finset.mem_image_of_mem _ hx) (y + g) (Finset.mem_image_of_mem _ hy)
      rw [pos_add, pos_add] at this
      exact add_right_cancel this
    · intro h x hx y hy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
      rw [pos_add, pos_add, h x' hx' y' hy']
  by_cases h : ∀ x ∈ T, ∀ y ∈ T, pos x = pos y
  · rw [if_pos (hall.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hall.1 h')), if_neg h]
    congr 1
    rw [Finset.sum_image (fun x _ y _ hxy => image_add_injective g hxy)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [filter_card_image_add]

lemma image_add_image_add (T : Finset (Vec (k + a))) (g : Vec (k + a)) :
    (T.image (· + g)).image (· + g) = T := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := T)]
  congr 1; funext x; simp [add_assoc, vadd_self']

/-! ### The normalized distribution -/

lemma total_pos (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : d + 1 ≤ 2 ^ a) :
    0 < ∑ τ ∈ tops d k a, weight d k a τ := by
  obtain ⟨τ, hτ, -⟩ := exists_top_of_clique (d := d) ha (σ := {0})
    (fun x hx y hy hxy => by simp at hx hy; rw [hx, hy] at hxy; exact absurd rfl hxy)
    (Finset.singleton_nonempty _) (by simp)
  exact Finset.sum_pos (fun τ hτ => weight_pos hd hk hτ) ⟨τ, hτ⟩

lemma mu_pos (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : d + 1 ≤ 2 ^ a) {T : Finset (Vec (k + a))}
    (hT : T ∈ tops d k a) : 0 < mu d k a T :=
  div_pos (weight_pos hd hk hT) (total_pos hd hk ha)

lemma mu_sum (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : d + 1 ≤ 2 ^ a) :
    ∑ τ ∈ tops d k a, mu d k a τ = 1 := by
  unfold mu
  rw [← Finset.sum_div, div_self (total_pos hd hk ha).ne']

lemma mu_image_add (T : Finset (Vec (k + a))) (g : Vec (k + a)) :
    mu d k a (T.image (· + g)) = mu d k a T := by
  unfold mu; rw [weight_image_add]

/-! ### Edges -/

lemma edges_eq (hd : 1 ≤ d) (ha : d + 1 ≤ 2 ^ a) :
    AbelianCayleyHDX.edges (tops d k a) =
      (Finset.univ ×ˢ gens k a).image (fun p : Vec (k + a) × Vec (k + a) => ({p.1, p.1 + p.2} : Finset _)) := by
  ext e
  simp only [AbelianCayleyHDX.edges, Finset.mem_biUnion, Finset.mem_powersetCard,
    Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨τ, hτ, hsub, hcard⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hcard
    have hc := (mem_tops.1 hτ).2
    refine ⟨x, x + y, hc x (hsub (by simp)) y (hsub (by simp)) hxy, ?_⟩
    rw [← add_assoc, vadd_self', zero_add]
  · rintro ⟨x, s, hs, rfl⟩
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; exact (mem_gens.1 hs).1 rfl
    have hxs : x ≠ x + s := by
      intro h; apply hs0
      have := congrArg (x + ·) h; simpa [← add_assoc, vadd_self'] using this.symm
    have hcl : IsClique ({x, x + s} : Finset (Vec (k + a))) := by
      intro y hy z hz hyz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
      have e1 : x + (x + s) = s := by rw [← add_assoc, vadd_self', zero_add]
      have e2 : x + s + x = s := by
        ext i; simp only [Pi.add_apply]; grind
      rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
      · exact absurd rfl hyz
      · rw [e1]; exact hs
      · rw [e2]; exact hs
      · exact absurd rfl hyz
    obtain ⟨τ, hτ, hsub⟩ := exists_top_of_clique ha hcl (by simp)
      (by rw [Finset.card_pair hxs]; omega)
    exact ⟨τ, hτ, hsub, Finset.card_pair hxs⟩

/-! ### Edge masses depend only on the generator -/

lemma faceMass_translate (σ : Finset (Vec (k + a))) (g : Vec (k + a)) :
    faceMass (tops d k a) (mu d k a) (σ.image (· + g)) = faceMass (tops d k a) (mu d k a) σ := by
  unfold faceMass
  apply Finset.sum_nbij' (fun τ => τ.image (· + g)) (fun τ => τ.image (· + g))
  · intro τ hτ
    simp only [Finset.mem_filter] at hτ ⊢
    refine ⟨tops_image_add hτ.1 g, ?_⟩
    have := Finset.image_subset_image (f := (· + g)) hτ.2
    rwa [image_add_image_add] at this
  · intro τ hτ
    simp only [Finset.mem_filter] at hτ ⊢
    exact ⟨tops_image_add hτ.1 g, Finset.image_subset_image hτ.2⟩
  · intro τ _; exact image_add_image_add τ g
  · intro τ _; exact image_add_image_add τ g
  · intro τ _
    exact (mu_image_add τ g).symm

lemma faceMass_edge (s x y : Vec (k + a)) :
    faceMass (tops d k a) (mu d k a) {x, x + s} = faceMass (tops d k a) (mu d k a) {y, y + s} := by
  rw [← faceMass_translate {y, y + s} (x + y)]
  congr 1
  simp only [Finset.image_insert, Finset.image_singleton]
  congr 1
  · rw [add_comm x y, ← add_assoc, vadd_self', zero_add]
  · congr 1
    rw [add_comm x y]
    ext i; simp only [Pi.add_apply]; grind

end AbelianCayleyHDX.Supplement.CubeLabel


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace AbelianCayleyHDX.XP

/-! ### General `Poly` combinators -/

theorem foldl_append_eq {α : Type} (xs : List (List α)) (acc : List α) :
    List.foldl (fun b a => b ++ a) acc xs = acc ++ xs.flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

theorem poly_flatten {α : Type} [Coding α] [Inhabited α] : Poly (List.flatten : List (List α) → List α) := by
  let P : PolyProgram (encodePair (encodeList (encodeList (enc : α → List Bool)))
      (encodeList (enc : α → List Bool))) (encodeList (enc : α → List Bool))
      (fun x : List (List α) × List α => List.foldl (fun b a => (b, a).1 ++ (b, a).2) x.2 x.1) :=
    PolyProgram.listFoldLinear (PolyProgram.listAppend (enc : α → List Bool) default) [] 1 (by
      intro b a
      simp only [EncodedList.append, List.length_append]
      omega)
  have h1 : Poly (fun xs : List (List α) => (xs, ([] : List α))) :=
    Poly.pair Poly.identity (OAI.MetricKMedian.Binary.Automatic.Poly.const ([] : List α))
  have h2 : Poly (fun x : List (List α) × List α =>
      List.foldl (fun b a => (b, a).1 ++ (b, a).2) x.2 x.1) := ⟨P⟩
  have := Poly.comp h2 h1
  convert this using 1
  funext xs
  simp only
  rw [foldl_append_eq, List.nil_append]

attribute [fun_prop] poly_flatten

variable {γ α β δ : Type} [Coding γ] [Coding α] [Coding β] [Coding δ]

@[fun_prop] theorem flatMap_ctx [Inhabited β] [Inhabited δ] {f : γ → β → List δ} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).flatMap (f x)) := by
  have h := Poly.comp poly_flatten (Poly.list_map hf ha)
  convert h using 2 with x
  rw [List.flatMap_def]

@[fun_prop] theorem map_ctx [Inhabited β] [Inhabited δ] {f : γ → β → δ} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).map (f x)) := Poly.list_map hf ha

@[fun_prop] theorem append_comp [Inhabited α] {f g : γ → List α} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x ++ g x) := Poly.comp Poly.list_append (Poly.pair hf hg)

@[fun_prop] theorem cons_comp {f : γ → α} {g : γ → List α} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x :: g x) := Poly.comp Poly.list_cons (Poly.pair hf hg)

@[fun_prop] theorem length_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => (f x).length) := Poly.comp Poly.list_length hf

@[fun_prop] theorem range_length_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => List.range (f x).length) :=
  Poly.comp (f := fun xs : List α => List.range xs.length) Poly.list_indices hf

@[fun_prop] theorem nat_eq_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x = g x)) := Poly.comp Poly.nat_eq (Poly.pair hf hg)

@[fun_prop] theorem nat_add_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x + g x) := Poly.comp Poly.nat_add (Poly.pair hf hg)

@[fun_prop] theorem nat_sub_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x - g x) := Poly.comp Poly.nat_sub (Poly.pair hf hg)

@[fun_prop] theorem rat_mul_comp {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x * g x) := Poly.comp Poly.rat_mul (Poly.pair hf hg)

@[fun_prop] theorem rat_div_comp {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x / g x) := Poly.comp Poly.rat_div (Poly.pair hf hg)

@[fun_prop] theorem rat_lt_comp' {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := Poly.comp Poly.rat_lt (Poly.pair hf hg)

@[fun_prop] theorem rat_ofNat_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => ((f x : ℕ) : ℚ)) :=
  Poly.comp Poly.rat_ofNat hf

@[fun_prop] theorem bits_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => Nat.bits (f x)) :=
  Poly.comp (⟨PolyProgram.natAsList⟩ : Poly (Nat.bits : ℕ → List Bool)) hf

@[fun_prop] theorem value_comp {f : γ → List Bool} (hf : Poly f) : Poly (fun x => Word.value (f x)) :=
  Poly.comp (⟨BooleanLists.valueProgram⟩ : Poly (Word.value : List Bool → ℕ)) hf

@[fun_prop] theorem num_abs_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => (f x).num.natAbs) :=
  Poly.comp (⟨PolyProgram.intAbs⟩ : Poly (Int.natAbs : ℤ → ℕ))
    (Poly.comp (⟨PolyProgram.ratNum⟩ : Poly (Rat.num : ℚ → ℤ)) hf)

@[fun_prop] theorem den_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => (f x).den) :=
  Poly.comp (⟨PolyProgram.ratDen⟩ : Poly (Rat.den : ℚ → ℕ)) hf

@[fun_prop] theorem const' (b : β) : Poly (fun _ : γ => b) :=
  OAI.MetricKMedian.Binary.Automatic.Poly.const b

@[fun_prop] theorem id' : Poly (fun x : γ => x) := Poly.identity

@[fun_prop] theorem fst' : Poly (fun x : γ × β => x.1) := Poly.fst

@[fun_prop] theorem snd' : Poly (fun x : γ × β => x.2) := Poly.snd

@[fun_prop] theorem fst_comp {f : γ → α × β} (hf : Poly f) : Poly (fun x => (f x).1) :=
  Poly.comp Poly.fst hf

@[fun_prop] theorem snd_comp {f : γ → α × β} (hf : Poly f) : Poly (fun x => (f x).2) :=
  Poly.comp Poly.snd hf

@[fun_prop] theorem pair' {f : γ → α} {g : γ → β} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => (f x, g x)) := Poly.pair hf hg

@[fun_prop] theorem ite' {p : γ → Bool} {f g : γ → α} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x = true then f x else g x) := Poly.ite hp hf hg

end AbelianCayleyHDX.XP

namespace AbelianCayleyHDX.XP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable {γ α : Type} [Coding γ] [Coding α]

@[fun_prop] theorem tail_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => (f x).tail) := Poly.comp Poly.list_tail hf

/-! ### The output function -/

/-- `encNat`, written with `Nat.bits`. -/
def encNatB (m : ℕ) : List Bool := (Nat.bits m).flatMap (fun b => [false, b]) ++ [true, false]

/-- `encNat 0` / `encNat 1`. -/
def cbit (b : Bool) : List Bool := if b then [false, true, true, false] else [true, false]

def encRatB (q : ℚ) : List Bool := decide (q < 0) :: (encNatB q.num.natAbs ++ encNatB q.den)

def vecB (n : ℕ) (cs : List Bool) : List Bool := encNatB n ++ cs.flatMap cbit

def posZero (k : ℕ) : List Bool := (List.range k).map (fun _ => false)

def posE (k i : ℕ) : List Bool := (List.range k).map (fun r => decide (r = i))

def pow2B (k : ℕ) : ℕ := Word.value (((List.range k).tail.map (fun _ => false)) ++ [true])

/-- The normalization `Z(k) = k · 2^{k-1} · K`. -/
def ZB (Kc : ℚ) (k : ℕ) : ℚ := (k : ℚ) * (pow2B k : ℚ) * Kc

def gensC (labNZ : List (List Bool)) (k : ℕ) : List (List Bool) :=
  (posZero k :: (List.range k).map (posE k)).flatMap (fun p => labNZ.map (fun b => p ++ b))

def repsC (T1 : List (List (List Bool))) (T2 : List (List (List Bool) × List (List Bool) × ℚ))
    (ws : ℚ) (k : ℕ) : List (List (List Bool) × ℚ) :=
  T1.map (fun L => (L.map (fun b => posZero k ++ b), ws * (k : ℚ))) ++
    (List.range k).flatMap (fun i => T2.map (fun e =>
      (e.1.map (fun b => posZero k ++ b) ++ e.2.1.map (fun b => posE k i ++ b), e.2.2)))

def outB (a : ℕ) (labNZ : List (List Bool)) (T1 : List (List (List Bool)))
    (T2 : List (List (List Bool) × List (List Bool) × ℚ)) (ws Kc : ℚ) (k : ℕ) : List Bool :=
  encNatB (k + a) ++
    (encNatB (gensC labNZ k).length ++ (gensC labNZ k).flatMap (vecB (k + a))) ++
    (encNatB (repsC T1 T2 ws k).length ++ (repsC T1 T2 ws k).flatMap (fun e =>
      encNatB e.1.length ++ e.1.flatMap (vecB (k + a)) ++ encRatB (e.2 / ZB Kc k)))

@[fun_prop] theorem encNatB_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => encNatB (f x)) := by
  unfold encNatB; fun_prop

@[fun_prop] theorem cbit_comp {f : γ → Bool} (hf : Poly f) : Poly (fun x => cbit (f x)) := by
  unfold cbit; fun_prop

@[fun_prop] theorem encRatB_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => encRatB (f x)) := by
  unfold encRatB; fun_prop

@[fun_prop] theorem vecB_comp {f : γ → ℕ} {g : γ → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => vecB (f x) (g x)) := by
  unfold vecB; fun_prop

theorem poly_outB (a : ℕ) (labNZ : List (List Bool)) (T1 : List (List (List Bool)))
    (T2 : List (List (List Bool) × List (List Bool) × ℚ)) (ws Kc : ℚ) :
    Poly (fun w : List Bool => outB a labNZ T1 T2 ws Kc w.length) := by
  unfold outB gensC repsC ZB pow2B posE posZero
  fun_prop

end AbelianCayleyHDX.XP

namespace AbelianCayleyHDX.XP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem poly_eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

/-- A `Poly` function on Boolean words is computed by a multi-stack machine within a polynomial
time bound in any upper bound of the input length. -/
theorem outputsWithin_of_poly {F : List Bool → List Bool}
    (hF : Poly (fun w : List Bool => F w)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (p : Polynomial ℕ), ∀ (w : List Bool) (N : ℕ),
      w.length ≤ N → HMBinPacking.OutputsWithin M w (F w) (p.eval N) := by
  let P : PolyProgram id id (id ∘ (F ∘ id)) :=
    BooleanLists.packProgram.comp (hF.program.comp BooleanLists.unpackProgram)
  refine ⟨⟨P.machine.tm, Equiv.refl _, Equiv.refl _⟩, P.time, fun w N hN => ?_⟩
  have h := P.outputs w
  have h' : Turing.TM2OutputsInTime P.machine.tm w (some (F w)) (P.time.eval N) :=
    ⟨h.toEvalsTo, le_trans h.steps_le_m (poly_eval_mono _ hN)⟩
  unfold HMBinPacking.OutputsWithin
  change Nonempty (Turing.TM2OutputsInTime P.machine.tm
    (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) w)
    (some (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (F w))) (P.time.eval N))
  have e1 : List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) w = w := List.map_id w
  have e2 : List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (F w) = F w :=
    List.map_id (F w)
  rw [e1, e2]
  exact ⟨h'⟩

end AbelianCayleyHDX.XP

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel.X

open Finset

variable {a : ℕ}

/-- Translation of a set of labels. -/
def tr (c : Vec a) (s : Finset (Vec a)) : Finset (Vec a) := s.image (· + c)

lemma mem_tr {c x : Vec a} {s : Finset (Vec a)} : x ∈ tr c s ↔ x + c ∈ s := by
  unfold tr
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [add_assoc, vadd_self', add_zero]
  · intro h; exact ⟨x + c, h, by rw [add_assoc, vadd_self', add_zero]⟩

lemma tr_zero (s : Finset (Vec a)) : tr 0 s = s := by
  ext x; rw [mem_tr, add_zero]

lemma tr_tr (c c' : Vec a) (s : Finset (Vec a)) : tr c (tr c' s) = tr (c + c') s := by
  ext x; rw [mem_tr, mem_tr, mem_tr, add_assoc]

lemma tr_self (c : Vec a) (s : Finset (Vec a)) : tr c (tr c s) = s := by
  rw [tr_tr, vadd_self', tr_zero]

lemma card_tr (c : Vec a) (s : Finset (Vec a)) : (tr c s).card = s.card :=
  Finset.card_image_of_injective _ (add_left_injective c)

lemma tr_nonempty {c : Vec a} {s : Finset (Vec a)} : (tr c s).Nonempty ↔ s.Nonempty := by
  unfold tr; exact Finset.image_nonempty

lemma disjoint_tr {c : Vec a} {s t : Finset (Vec a)} :
    Disjoint (tr c s) (tr c t) ↔ Disjoint s t := by
  unfold tr
  rw [Finset.disjoint_image (add_left_injective c)]

/-- The single-fibre label configurations. -/
def S1 (d a : ℕ) : Finset (Finset (Vec a)) := Finset.powersetCard (d + 1) Finset.univ

/-- The split label configurations: two nonempty disjoint label sets of total size `d + 1`. -/
def S2 (d a : ℕ) : Finset (Finset (Vec a) × Finset (Vec a)) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p =>
    p.1.Nonempty ∧ p.2.Nonempty ∧ Disjoint p.1 p.2 ∧ p.1.card + p.2.card = d + 1

lemma mem_S1 {d : ℕ} {s : Finset (Vec a)} : s ∈ S1 d a ↔ s.card = d + 1 := by
  simp [S1]

lemma mem_S2 {d : ℕ} {p : Finset (Vec a) × Finset (Vec a)} :
    p ∈ S2 d a ↔ p.1.Nonempty ∧ p.2.Nonempty ∧ Disjoint p.1 p.2 ∧ p.1.card + p.2.card = d + 1 := by
  simp [S2]

/-- Label translation. -/
def setoid1 (a : ℕ) : Setoid (Finset (Vec a)) where
  r s s' := ∃ c, s' = tr c s
  iseqv := ⟨fun s => ⟨0, (tr_zero s).symm⟩,
    fun ⟨c, h⟩ => ⟨c, by rw [h, tr_self]⟩,
    fun ⟨c, h⟩ ⟨c', h'⟩ => ⟨c' + c, by rw [h', h, tr_tr]⟩⟩

/-- Label translation together with exchanging the two sides. -/
def setoid2 (a : ℕ) : Setoid (Finset (Vec a) × Finset (Vec a)) where
  r p p' := ∃ c, (p'.1 = tr c p.1 ∧ p'.2 = tr c p.2) ∨ (p'.1 = tr c p.2 ∧ p'.2 = tr c p.1)
  iseqv := by
    refine ⟨fun p => ⟨0, Or.inl ⟨(tr_zero _).symm, (tr_zero _).symm⟩⟩, ?_, ?_⟩
    · rintro p p' ⟨c, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · exact ⟨c, Or.inl ⟨by rw [h1, tr_self], by rw [h2, tr_self]⟩⟩
      · exact ⟨c, Or.inr ⟨by rw [h2, tr_self], by rw [h1, tr_self]⟩⟩
    · rintro p p' p'' ⟨c, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ ⟨c', ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
      · exact ⟨c' + c, Or.inl ⟨by rw [h1', h1, tr_tr], by rw [h2', h2, tr_tr]⟩⟩
      · exact ⟨c' + c, Or.inr ⟨by rw [h1', h2, tr_tr], by rw [h2', h1, tr_tr]⟩⟩
      · exact ⟨c' + c, Or.inr ⟨by rw [h1', h1, tr_tr], by rw [h2', h2, tr_tr]⟩⟩
      · exact ⟨c' + c, Or.inl ⟨by rw [h1', h2, tr_tr], by rw [h2', h1, tr_tr]⟩⟩

noncomputable def canon1 (s : Finset (Vec a)) : Finset (Vec a) :=
  (Quotient.mk (setoid1 a) s).out

noncomputable def canon2 (p : Finset (Vec a) × Finset (Vec a)) : Finset (Vec a) × Finset (Vec a) :=
  (Quotient.mk (setoid2 a) p).out

lemma canon1_rel (s : Finset (Vec a)) : (setoid1 a).r s (canon1 s) :=
  (setoid1 a).iseqv.symm (Quotient.mk_out (s := setoid1 a) s)

lemma canon2_rel (p : Finset (Vec a) × Finset (Vec a)) : (setoid2 a).r p (canon2 p) :=
  (setoid2 a).iseqv.symm (Quotient.mk_out (s := setoid2 a) p)

lemma canon1_eq {s s' : Finset (Vec a)} (h : (setoid1 a).r s s') : canon1 s = canon1 s' := by
  unfold canon1; rw [Quotient.sound (s := setoid1 a) h]

lemma canon2_eq {p p' : Finset (Vec a) × Finset (Vec a)} (h : (setoid2 a).r p p') :
    canon2 p = canon2 p' := by
  unfold canon2; rw [Quotient.sound (s := setoid2 a) h]

lemma canon1_canon1 (s : Finset (Vec a)) : canon1 (canon1 s) = canon1 s :=
  (canon1_eq (canon1_rel s)).symm

lemma canon2_canon2 (p : Finset (Vec a) × Finset (Vec a)) : canon2 (canon2 p) = canon2 p :=
  (canon2_eq (canon2_rel p)).symm

lemma S1_rel {d : ℕ} {s s' : Finset (Vec a)} (h : (setoid1 a).r s s') (hs : s ∈ S1 d a) :
    s' ∈ S1 d a := by
  obtain ⟨c, rfl⟩ := h
  rw [mem_S1] at hs ⊢; rw [card_tr, hs]

lemma S2_rel {d : ℕ} {p p' : Finset (Vec a) × Finset (Vec a)} (h : (setoid2 a).r p p')
    (hp : p ∈ S2 d a) : p' ∈ S2 d a := by
  obtain ⟨c, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h <;> rw [mem_S2] at hp ⊢ <;> rw [h1, h2]
  · exact ⟨tr_nonempty.2 hp.1, tr_nonempty.2 hp.2.1, disjoint_tr.2 hp.2.2.1,
      by rw [card_tr, card_tr, hp.2.2.2]⟩
  · exact ⟨tr_nonempty.2 hp.2.1, tr_nonempty.2 hp.1, disjoint_tr.2 hp.2.2.1.symm,
      by rw [card_tr, card_tr, add_comm, hp.2.2.2]⟩

/-- The tables of orbit representatives. -/
noncomputable def T1 (d a : ℕ) : Finset (Finset (Vec a)) := (S1 d a).image canon1
noncomputable def T2 (d a : ℕ) : Finset (Finset (Vec a) × Finset (Vec a)) := (S2 d a).image canon2

lemma T1_sub {d : ℕ} {s : Finset (Vec a)} (h : s ∈ T1 d a) : s ∈ S1 d a ∧ canon1 s = s := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
  exact ⟨S1_rel (canon1_rel t) ht, canon1_canon1 t⟩

lemma T2_sub {d : ℕ} {p : Finset (Vec a) × Finset (Vec a)} (h : p ∈ T2 d a) :
    p ∈ S2 d a ∧ canon2 p = p := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
  exact ⟨S2_rel (canon2_rel t) ht, canon2_canon2 t⟩

lemma canon1_mem_T1 {d : ℕ} {s : Finset (Vec a)} (h : s ∈ S1 d a) : canon1 s ∈ T1 d a :=
  Finset.mem_image_of_mem _ h

lemma canon2_mem_T2 {d : ℕ} {p : Finset (Vec a) × Finset (Vec a)} (h : p ∈ S2 d a) :
    canon2 p ∈ T2 d a :=
  Finset.mem_image_of_mem _ h

/-- Two table entries in the same class coincide. -/
lemma T1_unique {d : ℕ} {s s' : Finset (Vec a)} (hs : s ∈ T1 d a) (hs' : s' ∈ T1 d a)
    (h : (setoid1 a).r s s') : s = s' := by
  rw [← (T1_sub hs).2, ← (T1_sub hs').2, canon1_eq h]

lemma T2_unique {d : ℕ} {p p' : Finset (Vec a) × Finset (Vec a)} (hp : p ∈ T2 d a)
    (hp' : p' ∈ T2 d a) (h : (setoid2 a).r p p') : p = p' := by
  rw [← (T2_sub hp).2, ← (T2_sub hp').2, canon2_eq h]

end AbelianCayleyHDX.Supplement.CubeLabel.X

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel.X

open Finset

variable {d k a : ℕ}

/-- The unit vector `eᵢ` of the cube. -/
abbrev ee (i : Fin k) : Vec k := Pi.single i 1

lemma emb_inj {u u' : Vec k} {b b' : Vec a} (h : emb u b = emb u' b') : u = u' ∧ b = b' :=
  ⟨by simpa using congrArg pos h, by simpa using congrArg lab h⟩

lemma image_emb_tr (u v : Vec k) (c : Vec a) (s : Finset (Vec a)) :
    (s.image (emb u)).image (· + emb v c) = (tr c s).image (emb (u + v)) := by
  rw [Finset.image_image, tr, Finset.image_image]
  congr 1; funext x; simp [Function.comp, emb_add]

lemma pos_of_mem_image {u : Vec k} {s : Finset (Vec a)} {x : Vec (k + a)}
    (hx : x ∈ s.image (emb u)) : pos x = u := by
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx; simp

lemma filter_image_emb_self {u w : Vec k} (huw : u ≠ w) (A B : Finset (Vec a)) :
    ((A.image (emb u) ∪ B.image (emb w)).filter fun x => pos x = u) = A.image (emb u) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hp⟩
    · exact hx
    · exact absurd ((pos_of_mem_image hx).symm.trans hp) (Ne.symm huw)
  · intro hx; exact ⟨Or.inl hx, pos_of_mem_image hx⟩

lemma labels_at {u w : Vec k} (huw : u ≠ w) (A B : Finset (Vec a)) :
    (((A.image (emb u) ∪ B.image (emb w)).filter fun x => pos x = u).image lab) = A := by
  rw [filter_image_emb_self huw, Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := A)]
  congr 1; funext b; simp

lemma img_emb_eq {u u' : Vec k} {s s' : Finset (Vec a)} (hs : s.Nonempty)
    (h : s.image (emb u) = s'.image (emb u')) : u = u' ∧ s = s' := by
  obtain ⟨b, hb⟩ := hs
  have hm : emb u b ∈ s'.image (emb u') := h ▸ Finset.mem_image_of_mem _ hb
  have hu : u = u' := by simpa using pos_of_mem_image hm
  subst hu
  refine ⟨rfl, ?_⟩
  have := congrArg (Finset.image lab) h
  rwa [Finset.image_image, Finset.image_image, show lab ∘ emb u = (id : Vec a → Vec a) from
    funext fun b => by simp, Finset.image_id, Finset.image_id] at this

lemma ee_ne_zero (i : Fin k) : (ee i : Vec k) ≠ 0 := single_ne_zero' i

lemma add_ee_ne (u : Vec k) (i : Fin k) : u ≠ u + ee i := by
  intro h; apply ee_ne_zero i
  have := congrArg (u + ·) h
  simpa [← add_assoc, vadd_self'] using this.symm

lemma ee_inj {i i' : Fin k} (h : (ee i : Vec k) = ee i') : i = i' := single_inj' h

lemma posset {u w v : Vec k} {A B : Finset (Vec a)} (hA : A.Nonempty) (hB : B.Nonempty) :
    (∃ x ∈ A.image (emb u) ∪ B.image (emb w), pos x = v) ↔ (v = u ∨ v = w) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Or.inl (pos_of_mem_image hx)
    · exact Or.inr (pos_of_mem_image hx)
  · rintro (rfl | rfl)
    · obtain ⟨b, hb⟩ := hA
      exact ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb), by simp⟩
    · obtain ⟨b, hb⟩ := hB
      exact ⟨_, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb), by simp⟩

lemma labels_at' {u w : Vec k} (huw : u ≠ w) (A B : Finset (Vec a)) :
    (((A.image (emb u) ∪ B.image (emb w)).filter fun x => pos x = w).image lab) = B := by
  rw [Finset.union_comm]; exact labels_at (Ne.symm huw) B A

/-- **Decomposition uniqueness** for two-sided faces. -/
lemma split_eq {u u' : Vec k} {i i' : Fin k} {A B A' B' : Finset (Vec a)}
    (hA : A.Nonempty) (hB : B.Nonempty) (hA' : A'.Nonempty) (hB' : B'.Nonempty)
    (h : A.image (emb u) ∪ B.image (emb (u + ee i)) =
      A'.image (emb u') ∪ B'.image (emb (u' + ee i'))) :
    i = i' ∧ ((u = u' ∧ A = A' ∧ B = B') ∨ (u = u' + ee i' ∧ A = B' ∧ B = A')) := by
  classical
  have hP : ∀ v : Vec k, (v = u ∨ v = u + ee i) ↔ (v = u' ∨ v = u' + ee i') := by
    intro v; rw [← posset hA hB, ← posset hA' hB', h]
  have hu := (hP u).1 (Or.inl rfl)
  have hui := (hP (u + ee i)).1 (Or.inr rfl)
  rcases hu with rfl | rfl
  · have hii : i = i' := by
      rcases hui with h1 | h1
      · exact absurd h1.symm (add_ee_ne u i)
      · exact ee_inj (add_left_cancel h1)
    subst hii
    refine ⟨rfl, Or.inl ⟨rfl, ?_, ?_⟩⟩
    · have := labels_at (add_ee_ne u i) A B
      rw [h, labels_at (add_ee_ne u i) A' B'] at this
      exact this.symm
    · have := labels_at' (add_ee_ne u i) A B
      rw [h, labels_at' (add_ee_ne u i) A' B'] at this
      exact this.symm
  · have hii : i = i' := by
      rcases hui with h1 | h1
      · have h2 : u' + (ee i' + ee i) = u' + 0 := by rw [← add_assoc, h1, add_zero]
        have h3 := add_left_cancel h2
        exact (ee_inj ((vec_eq_iff_add_eq_zero _ _).2 h3)).symm
      · have h2 : u' + ee i' + ee i = u' + ee i' + 0 := by rw [h1, add_zero]
        exact absurd (add_left_cancel h2) (ee_ne_zero i)
    subst hii
    have hu2 : u' + ee i + ee i = u' := by rw [add_assoc, vadd_self', add_zero]
    refine ⟨rfl, Or.inr ⟨rfl, ?_, ?_⟩⟩
    · have e1 := labels_at (add_ee_ne (u' + ee i) i) A B
      rw [h] at e1
      have e2 := labels_at' (add_ee_ne u' i) A' B'
      exact e1.symm.trans e2
    · have e1 := labels_at' (add_ee_ne (u' + ee i) i) A B
      rw [h, hu2] at e1
      have e2 := labels_at (add_ee_ne u' i) A' B'
      exact e1.symm.trans e2

lemma card_image_emb (u : Vec k) (s : Finset (Vec a)) : (s.image (emb u)).card = s.card :=
  Finset.card_image_of_injective _ (fun b b' h => (emb_inj h).2)

lemma disjoint_split {u w : Vec k} (huw : u ≠ w) (A B : Finset (Vec a)) :
    Disjoint (A.image (emb u)) (B.image (emb w)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact huw ((pos_of_mem_image hx).symm.trans (pos_of_mem_image hx'))

lemma single_mem_tops {u : Vec k} {s : Finset (Vec a)} (hs : s ∈ S1 d a) :
    s.image (emb u) ∈ tops d k a := by
  rw [mem_tops, card_image_emb, ← mem_S1.1 hs]
  refine ⟨rfl, fun x hx y hy hxy => ?_⟩
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨b', -, rfl⟩ := Finset.mem_image.1 hy
  rw [add_mem_gens]
  simp only [lab_emb, pos_emb]
  exact ⟨fun h => hxy (by rw [h]), Or.inl (vadd_self' u)⟩

lemma split_mem_tops {u : Vec k} {i : Fin k} {p : Finset (Vec a) × Finset (Vec a)}
    (hp : p ∈ S2 d a) : p.1.image (emb u) ∪ p.2.image (emb (u + ee i)) ∈ tops d k a := by
  rw [mem_S2] at hp
  rw [mem_tops, Finset.card_union_of_disjoint (disjoint_split (add_ee_ne u i) _ _),
    card_image_emb, card_image_emb, hp.2.2.2]
  refine ⟨rfl, fun x hx y hy hxy => ?_⟩
  rw [add_mem_gens]
  have hd := hp.2.2.1
  rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy <;>
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx <;> obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hy <;>
    simp only [lab_emb, pos_emb]
  · exact ⟨fun h => hxy (by rw [h]), Or.inl (vadd_self' u)⟩
  · refine ⟨fun h => Finset.disjoint_left.1 hd hb (h ▸ hb'), Or.inr ⟨i, ?_⟩⟩
    rw [← add_assoc, vadd_self', zero_add]
  · refine ⟨fun h => Finset.disjoint_left.1 hd hb' (h ▸ hb), Or.inr ⟨i, ?_⟩⟩
    rw [add_comm u (ee i), add_assoc, vadd_self', add_zero]
  · exact ⟨fun h => hxy (by rw [h]), Or.inl (vadd_self' _)⟩

lemma allSame_single (u : Vec k) (s : Finset (Vec a)) :
    ∀ x ∈ s.image (emb u), ∀ y ∈ s.image (emb u), pos x = pos y := fun x hx y hy => by
  rw [pos_of_mem_image hx, pos_of_mem_image hy]

lemma not_allSame_split {u : Vec k} {i : Fin k} {A B : Finset (Vec a)} (hA : A.Nonempty)
    (hB : B.Nonempty) :
    ¬ ∀ x ∈ A.image (emb u) ∪ B.image (emb (u + ee i)),
      ∀ y ∈ A.image (emb u) ∪ B.image (emb (u + ee i)), pos x = pos y := by
  intro h
  obtain ⟨b, hb⟩ := hA
  obtain ⟨b', hb'⟩ := hB
  have := h _ (Finset.mem_union_left _ (Finset.mem_image_of_mem (emb u) hb)) _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem (emb (u + ee i)) hb'))
  simp only [pos_emb] at this
  exact add_ee_ne u i this

lemma z2_eq_one {c : ZMod 2} (h : c ≠ 0) : c = 1 := by revert c h; decide

lemma lab_card {T : Finset (Vec (k + a))} (hT : IsClique T) (s : Finset (Vec (k + a)))
    (hs : s ⊆ T) : (s.image lab).card = s.card :=
  Finset.card_image_of_injOn (fun x hx y hy h => hT.lab_inj (hs hx) (hs hy) h)

/-- **Classification of top faces.** -/
lemma classify {τ : Finset (Vec (k + a))} (hτ : τ ∈ tops d k a) :
    (∃ u, ∃ s ∈ S1 d a, τ = s.image (emb u)) ∨
      (∃ i u, u i = 0 ∧ ∃ p ∈ S2 d a, τ = p.1.image (emb u) ∪ p.2.image (emb (u + ee i))) := by
  classical
  have hT := mem_tops.1 hτ
  obtain ⟨x0, hx0⟩ : τ.Nonempty := by rw [← Finset.card_pos, hT.1]; omega
  by_cases hall : ∀ y ∈ τ, pos y = pos x0
  · left
    refine ⟨pos x0, τ.image lab, ?_, ?_⟩
    · rw [mem_S1, lab_card hT.2 τ subset_rfl, hT.1]
    · ext x
      rw [Finset.image_image, Finset.mem_image]
      constructor
      · intro hx; exact ⟨x, hx, by simp only [Function.comp]; rw [← hall x hx, emb_pos_lab]⟩
      · rintro ⟨y, hy, rfl⟩; simp only [Function.comp]; rw [← hall y hy, emb_pos_lab]; exact hy
  · right
    push Not at hall
    obtain ⟨y0, hy0, hne⟩ := hall
    have hadj := hT.2.posAdj hx0 hy0
    obtain ⟨i, hi⟩ : ∃ i, pos x0 + pos y0 = ee i := by
      rcases hadj with h | h
      · exact absurd ((vec_eq_iff_add_eq_zero _ _).2 h) (Ne.symm hne)
      · exact h
    -- the lower endpoint
    obtain ⟨u, hu0, hset⟩ : ∃ u : Vec k, u i = 0 ∧
        ((pos x0 = u ∧ pos y0 = u + ee i) ∨ (pos y0 = u ∧ pos x0 = u + ee i)) := by
      have hy : pos y0 = pos x0 + ee i := by
        rw [← hi, ← add_assoc, vadd_self', zero_add]
      by_cases h0 : pos x0 i = 0
      · exact ⟨pos x0, h0, Or.inl ⟨rfl, hy⟩⟩
      · refine ⟨pos y0, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · rw [hy, Pi.add_apply, z2_eq_one h0]; simp; decide
        · rw [hy, add_assoc, vadd_self', add_zero]
    have hpos : ∀ z ∈ τ, pos z = u ∨ pos z = u + ee i := by
      intro z hz
      have := hT.2.pos_two hx0 hy0 hz (Ne.symm hne)
      rcases hset with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this
      · exact this
      · exact this.symm
    set A := (τ.filter fun z => pos z = u).image lab with hA
    set B := (τ.filter fun z => pos z = u + ee i).image lab with hB
    have hτeq : τ = A.image (emb u) ∪ B.image (emb (u + ee i)) := by
      ext x
      simp only [hA, hB, Finset.mem_union, Finset.image_image, Finset.mem_image,
        Finset.mem_filter, Function.comp]
      constructor
      · intro hx
        rcases hpos x hx with h | h
        · exact Or.inl ⟨x, ⟨hx, h⟩, by rw [← h, emb_pos_lab]⟩
        · exact Or.inr ⟨x, ⟨hx, h⟩, by rw [← h, emb_pos_lab]⟩
      · rintro (⟨y, ⟨hy, h⟩, rfl⟩ | ⟨y, ⟨hy, h⟩, rfl⟩) <;> rw [← h, emb_pos_lab] <;> exact hy
    refine ⟨i, u, hu0, (A, B), ?_, hτeq⟩
    have hAne : A.Nonempty := by
      rcases hset with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨lab x0, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hx0, h1⟩)⟩
      · exact ⟨lab y0, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hy0, h1⟩)⟩
    have hBne : B.Nonempty := by
      rcases hset with ⟨-, h1⟩ | ⟨-, h1⟩
      · exact ⟨lab y0, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hy0, h1⟩)⟩
      · exact ⟨lab x0, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hx0, h1⟩)⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro l hl hl'
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hl
      obtain ⟨z', hz', hzz⟩ := Finset.mem_image.1 hl'
      rw [Finset.mem_filter] at hz hz'
      have : z' = z := hT.2.lab_inj hz'.1 hz.1 hzz
      rw [this, hz.2] at hz'
      exact add_ee_ne u i hz'.2
    rw [mem_S2]
    refine ⟨hAne, hBne, hdisj, ?_⟩
    rw [← hT.1, hτeq, Finset.card_union_of_disjoint (disjoint_split (add_ee_ne u i) _ _),
      card_image_emb, card_image_emb]

end AbelianCayleyHDX.Supplement.CubeLabel.X

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel.X

open Finset

variable {d k a : ℕ}

noncomputable def T1L (d a : ℕ) : List (Finset (Vec a)) := (T1 d a).toList
noncomputable def T2L (d a : ℕ) : List (Finset (Vec a) × Finset (Vec a)) := (T2 d a).toList

noncomputable def rep1 (k : ℕ) (s : Finset (Vec a)) : List (Vec (k + a)) := s.toList.map (emb 0)

noncomputable def rep2 (i : Fin k) (p : Finset (Vec a) × Finset (Vec a)) : List (Vec (k + a)) :=
  p.1.toList.map (emb 0) ++ p.2.toList.map (emb (ee i))

noncomputable def reps (d k a : ℕ) : List (List (Vec (k + a))) :=
  (T1L d a).map (rep1 k) ++ (List.finRange k).flatMap (fun i => (T2L d a).map (rep2 i))

lemma rep1_toFinset (s : Finset (Vec a)) : (rep1 k s).toFinset = s.image (emb 0) := by
  ext x; simp [rep1]

lemma rep2_toFinset (i : Fin k) (p : Finset (Vec a) × Finset (Vec a)) :
    (rep2 i p).toFinset = p.1.image (emb 0) ∪ p.2.image (emb (0 + ee i)) := by
  ext x; simp [rep2]

lemma mem_reps {r : List (Vec (k + a))} :
    r ∈ reps d k a ↔ (∃ s ∈ T1 d a, r = rep1 k s) ∨ (∃ i, ∃ p ∈ T2 d a, r = rep2 i p) := by
  simp only [reps, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange, true_and,
    T1L, T2L, Finset.mem_toList]
  constructor
  · rintro (⟨s, hs, rfl⟩ | ⟨i, p, hp, rfl⟩)
    · exact Or.inl ⟨s, hs, rfl⟩
    · exact Or.inr ⟨i, p, hp, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨i, p, hp, rfl⟩)
    · exact Or.inl ⟨s, hs, rfl⟩
    · exact Or.inr ⟨i, p, hp, rfl⟩

lemma tr_single (s : Finset (Vec a)) (g : Vec (k + a)) :
    (s.image (emb (0 : Vec k))).image (· + g) = (tr (lab g) s).image (emb (pos g)) := by
  conv_lhs => rw [← emb_pos_lab g]
  rw [image_emb_tr, zero_add]

lemma tr_split (i : Fin k) (p : Finset (Vec a) × Finset (Vec a)) (g : Vec (k + a)) :
    (p.1.image (emb 0) ∪ p.2.image (emb (0 + ee i))).image (· + g) =
      (tr (lab g) p.1).image (emb (pos g)) ∪ (tr (lab g) p.2).image (emb (pos g + ee i)) := by
  rw [Finset.image_union]
  conv_lhs => rw [← emb_pos_lab g]
  rw [image_emb_tr, image_emb_tr, zero_add, zero_add, add_comm (ee i)]

lemma S2_ne {p : Finset (Vec a) × Finset (Vec a)} (hp : p ∈ S2 d a) :
    p.1.Nonempty ∧ p.2.Nonempty := ⟨(mem_S2.1 hp).1, (mem_S2.1 hp).2.1⟩

lemma S1_ne {s : Finset (Vec a)} (hs : s ∈ S1 d a) : s.Nonempty := by
  rw [← Finset.card_pos, mem_S1.1 hs]; omega

/-- **Exactly one listed representative per translation orbit.** -/
theorem exists_unique_rep {τ : Finset (Vec (k + a))} (hτ : τ ∈ tops d k a) :
    ∃! r, r ∈ reps d k a ∧ ∃ g : Vec (k + a), τ = r.toFinset.image (· + g) := by
  classical
  rcases classify hτ with ⟨u, s, hs, rfl⟩ | ⟨i, u, -, p, hp, rfl⟩
  · -- single-fibre face
    obtain ⟨c, hc⟩ := canon1_rel s
    refine ⟨rep1 k (canon1 s), ⟨mem_reps.2 (Or.inl ⟨_, canon1_mem_T1 hs, rfl⟩),
      emb u c, ?_⟩, ?_⟩
    · rw [rep1_toFinset, tr_single, lab_emb, pos_emb, hc, tr_self]
    · rintro r ⟨hr, g, hg⟩
      rcases mem_reps.1 hr with ⟨s', hs', rfl⟩ | ⟨i', q, hq, rfl⟩
      · rw [rep1_toFinset, tr_single] at hg
        obtain ⟨-, hss⟩ := img_emb_eq (S1_ne hs) hg
        have : (setoid1 a).r s' s := ⟨lab g, hss⟩
        rw [← (T1_sub hs').2, canon1_eq this]
      · exfalso
        rw [rep2_toFinset, tr_split] at hg
        obtain ⟨hq1, hq2⟩ := S2_ne (T2_sub hq).1
        exact not_allSame_split (tr_nonempty.2 hq1) (tr_nonempty.2 hq2)
          (hg ▸ allSame_single u s)
  · -- split face
    obtain ⟨hp1, hp2⟩ := S2_ne hp
    obtain ⟨c, ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩⟩ := canon2_rel p
    · refine ⟨rep2 i (canon2 p), ⟨mem_reps.2 (Or.inr ⟨i, _, canon2_mem_T2 hp, rfl⟩),
        emb u c, ?_⟩, ?_⟩
      · rw [rep2_toFinset, tr_split, lab_emb, pos_emb, hc1, hc2, tr_self, tr_self]
      · rintro r ⟨hr, g, hg⟩
        rcases mem_reps.1 hr with ⟨s', hs', rfl⟩ | ⟨i', q, hq, rfl⟩
        · exfalso
          rw [rep1_toFinset, tr_single] at hg
          exact not_allSame_split hp1 hp2 (hg ▸ allSame_single _ _)
        · rw [rep2_toFinset, tr_split] at hg
          obtain ⟨hq1, hq2⟩ := S2_ne (T2_sub hq).1
          obtain ⟨rfl, h⟩ := split_eq hp1 hp2 (tr_nonempty.2 hq1) (tr_nonempty.2 hq2) hg
          have hrel : (setoid2 a).r q p := by
            rcases h with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
            · exact ⟨lab g, Or.inl ⟨h1, h2⟩⟩
            · exact ⟨lab g, Or.inr ⟨h1, h2⟩⟩
          rw [← (T2_sub hq).2, canon2_eq hrel]
    · refine ⟨rep2 i (canon2 p), ⟨mem_reps.2 (Or.inr ⟨i, _, canon2_mem_T2 hp, rfl⟩),
        emb (u + ee i) c, ?_⟩, ?_⟩
      · rw [rep2_toFinset, tr_split, lab_emb, pos_emb, hc1, hc2, tr_self, tr_self,
          add_assoc, vadd_self', add_zero, Finset.union_comm]
      · rintro r ⟨hr, g, hg⟩
        rcases mem_reps.1 hr with ⟨s', hs', rfl⟩ | ⟨i', q, hq, rfl⟩
        · exfalso
          rw [rep1_toFinset, tr_single] at hg
          exact not_allSame_split hp1 hp2 (hg ▸ allSame_single _ _)
        · rw [rep2_toFinset, tr_split] at hg
          obtain ⟨hq1, hq2⟩ := S2_ne (T2_sub hq).1
          obtain ⟨rfl, h⟩ := split_eq hp1 hp2 (tr_nonempty.2 hq1) (tr_nonempty.2 hq2) hg
          have hrel : (setoid2 a).r q p := by
            rcases h with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
            · exact ⟨lab g, Or.inl ⟨h1, h2⟩⟩
            · exact ⟨lab g, Or.inr ⟨h1, h2⟩⟩
          rw [← (T2_sub hq).2, canon2_eq hrel]

lemma emb_injective (u : Vec k) : Function.Injective (emb (a := a) u) :=
  fun b b' h => (emb_inj h).2

lemma rep_valid {r : List (Vec (k + a))} (hr : r ∈ reps d k a) :
    r.Nodup ∧ r.toFinset ∈ tops d k a := by
  rcases mem_reps.1 hr with ⟨s, hs, rfl⟩ | ⟨i, p, hp, rfl⟩
  · refine ⟨(Finset.nodup_toList s).map (emb_injective 0), ?_⟩
    rw [rep1_toFinset]; exact single_mem_tops (T1_sub hs).1
  · refine ⟨?_, ?_⟩
    · rw [rep2, List.nodup_append]
      refine ⟨(Finset.nodup_toList _).map (emb_injective 0),
        (Finset.nodup_toList _).map (emb_injective _), ?_⟩
      intro x hx y hy hxy
      simp only [List.mem_map] at hx hy
      obtain ⟨b, -, rfl⟩ := hx
      obtain ⟨b', -, rfl⟩ := hy
      exact ee_ne_zero i (emb_inj hxy).1.symm
    · rw [rep2_toFinset]; exact split_mem_tops (T2_sub hp).1

lemma rep1_ne_rep2 {s : Finset (Vec a)} {i : Fin k} {p : Finset (Vec a) × Finset (Vec a)}
    (hp : p ∈ S2 d a) : rep1 k s ≠ rep2 i p := by
  intro h
  have := congrArg List.toFinset h
  rw [rep1_toFinset, rep2_toFinset] at this
  obtain ⟨h1, h2⟩ := S2_ne hp
  exact not_allSame_split h1 h2 (this ▸ allSame_single _ _)

lemma rep2_eq {i i' : Fin k} {p q : Finset (Vec a) × Finset (Vec a)} (hp : p ∈ S2 d a)
    (hq : q ∈ S2 d a) (h : rep2 i p = rep2 i' q) : i = i' ∧ p = q := by
  have := congrArg List.toFinset h
  rw [rep2_toFinset, rep2_toFinset] at this
  obtain ⟨hp1, hp2⟩ := S2_ne hp
  obtain ⟨hq1, hq2⟩ := S2_ne hq
  obtain ⟨rfl, h⟩ := split_eq hp1 hp2 hq1 hq2 this
  rcases h with ⟨-, h1, h2⟩ | ⟨h0, -, -⟩
  · exact ⟨rfl, Prod.ext h1 h2⟩
  · exact absurd (by rw [zero_add] at h0; exact h0.symm) (ee_ne_zero i)

lemma reps_nodup : (reps d k a).Nodup := by
  classical
  rw [reps, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · refine (Finset.nodup_toList _).map (fun s s' h => ?_)
    have := congrArg List.toFinset h
    rw [rep1_toFinset, rep1_toFinset] at this
    exact Finset.image_injective (emb_injective 0) this
  · rw [List.nodup_flatMap]
    refine ⟨fun i _ => (Finset.nodup_toList _).map_on (fun p hp q hq h =>
      (rep2_eq (T2_sub (Finset.mem_toList.1 hp)).1 (T2_sub (Finset.mem_toList.1 hq)).1 h).2), ?_⟩
    refine (List.nodup_finRange k).imp (fun {i i'} hii => ?_)
    rw [Function.onFun, List.disjoint_left]
    intro r hr hr'
    simp only [List.mem_map, T2L, Finset.mem_toList] at hr hr'
    obtain ⟨p, hp, rfl⟩ := hr
    obtain ⟨q, hq, hpq⟩ := hr'
    exact hii (rep2_eq (T2_sub hq).1 (T2_sub hp).1 hpq).1.symm
  · intro r hr r' hr' h
    subst h
    simp only [List.mem_map, T1L, Finset.mem_toList] at hr
    obtain ⟨s, -, rfl⟩ := hr
    simp only [List.mem_flatMap, List.mem_map, T2L, Finset.mem_toList] at hr'
    obtain ⟨i, -, p, hp, hps⟩ := hr'
    exact rep1_ne_rep2 (T2_sub hp).1 hps.symm

/-! ### Generators -/

noncomputable def LNZ (a : ℕ) : List (Vec a) := (Finset.univ.filter fun b : Vec a => b ≠ 0).toList

noncomputable def gensL (k a : ℕ) : List (Vec (k + a)) :=
  ((0 : Vec k) :: (List.finRange k).map ee).flatMap (fun u => (LNZ a).map (emb u))

lemma gensL_nodup : (gensL k a).Nodup := by
  classical
  rw [gensL, List.nodup_flatMap]
  refine ⟨fun u _ => (Finset.nodup_toList _).map (emb_injective u), ?_⟩
  have hnd : ((0 : Vec k) :: (List.finRange k).map ee).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, (List.nodup_finRange k).map (fun i i' h => ee_inj h)⟩
    simp only [List.mem_map, List.mem_finRange, true_and, not_exists]
    intro i h; exact ee_ne_zero i h
  refine hnd.imp (fun {u u'} huu => ?_)
  rw [Function.onFun, List.disjoint_left]
  intro x hx hx'
  simp only [List.mem_map] at hx hx'
  obtain ⟨b, -, rfl⟩ := hx
  obtain ⟨b', -, h⟩ := hx'
  exact huu (emb_inj h).1.symm

lemma gensL_toFinset : (gensL k a).toFinset = gens k a := by
  classical
  ext x
  rw [List.mem_toFinset, mem_gens]
  simp only [gensL, List.mem_flatMap, List.mem_cons, List.mem_map, List.mem_finRange, true_and,
    LNZ, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro ⟨u, hu, b, hb, rfl⟩
    simp only [lab_emb, pos_emb]
    refine ⟨hb, ?_⟩
    rcases hu with rfl | ⟨i, rfl⟩
    · left; simp
    · right; exact ⟨i, by simp⟩
  · rintro ⟨hl, hp⟩
    refine ⟨pos x, ?_, lab x, hl, emb_pos_lab x⟩
    rcases hp with h | ⟨i, h⟩
    · left; simpa using h
    · right; exact ⟨i, by simpa using h.symm⟩

end AbelianCayleyHDX.Supplement.CubeLabel.X

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel.X

open Finset

variable {d k a : ℕ}

/-! ### Weights of the representatives -/

lemma weight_rep1 {s : Finset (Vec a)} (hs : s ∈ S1 d a) :
    weight d k a (rep1 k s).toFinset = ((d : ℚ) - 1) * k := by
  rw [rep1_toFinset, weight_single (allSame_single _ _)]

lemma cnt_split {u : Vec k} {i : Fin k} {A B : Finset (Vec a)} {b : Vec a} (hb : b ∈ A) :
    cnt (A.image (emb u) ∪ B.image (emb (u + ee i))) (emb u b) = A.card := by
  unfold cnt
  rw [pos_emb, filter_image_emb_self (add_ee_ne u i), card_image_emb]

lemma weight_split' (hd : 1 ≤ d) {u : Vec k} {i : Fin k} {p : Finset (Vec a) × Finset (Vec a)}
    (hp : p ∈ S2 d a) :
    weight d k a (p.1.image (emb u) ∪ p.2.image (emb (u + ee i))) =
      1 / (Nat.choose (d - 1) (p.1.card - 1) : ℚ) := by
  obtain ⟨hp1, hp2⟩ := S2_ne hp
  obtain ⟨b, hb⟩ := hp1
  rw [weight_split hd (split_mem_tops hp) (not_allSame_split ⟨b, hb⟩ hp2)
    (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)), cnt_split hb]

lemma weight_rep2 (hd : 1 ≤ d) {i : Fin k} {p : Finset (Vec a) × Finset (Vec a)}
    (hp : p ∈ S2 d a) :
    weight d k a (rep2 i p).toFinset = 1 / (Nat.choose (d - 1) (p.1.card - 1) : ℚ) := by
  rw [rep2_toFinset, weight_split' hd hp]

/-! ### The normalization -/

noncomputable def Qd (d a : ℕ) : ℚ :=
  ∑ p ∈ S2 d a, 1 / (Nat.choose (d - 1) (p.1.card - 1) : ℚ)

noncomputable def Kd (d a : ℕ) : ℚ := 2 * ((S1 d a).card : ℚ) * ((d : ℚ) - 1) + Qd d a

lemma card_coord_zero (hk : 1 ≤ k) (i : Fin k) :
    (Finset.univ.filter fun u : Vec k => u i = 0).card = 2 ^ (k - 1) := by
  classical
  have hbij : (Finset.univ.filter fun u : Vec k => u i = 0).card =
      (Finset.univ.filter fun u : Vec k => ¬ u i = 0).card := by
    apply Finset.card_bij (fun u _ => u + ee i)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [Pi.add_apply, hu]; simp
    · intro u _ u' _ h; exact add_right_cancel h
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨v + ee i, ?_, by rw [add_assoc, vadd_self', add_zero]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Pi.add_apply, z2_eq_one hv]; simp; decide
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Vec k)))
    (fun u => u i = 0)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at htot
  have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

lemma card_base (hk : 1 ≤ k) :
    (Finset.univ.filter fun x : Fin k × Vec k => x.2 x.1 = 0).card = k * 2 ^ (k - 1) := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have : ∀ i : Fin k, (∑ u : Vec k, if u i = 0 then 1 else 0) = 2 ^ (k - 1) := by
    intro i; rw [← Finset.card_filter, card_coord_zero hk]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

lemma singles_eq (d k a : ℕ) :
    (tops d k a).filter (fun T => ∀ x ∈ T, ∀ y ∈ T, pos x = pos y) =
      ((Finset.univ : Finset (Vec k)) ×ˢ S1 d a).image (fun q => q.2.image (emb q.1)) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨hτ, hall⟩
    rcases classify hτ with ⟨u, s, hs, rfl⟩ | ⟨i, u, -, p, hp, rfl⟩
    · exact ⟨u, s, hs, rfl⟩
    · exact absurd hall (not_allSame_split (S2_ne hp).1 (S2_ne hp).2)
  · rintro ⟨u, s, hs, rfl⟩
    exact ⟨single_mem_tops hs, allSame_single u s⟩

lemma splits_eq (d k a : ℕ) :
    (tops d k a).filter (fun T => ¬ ∀ x ∈ T, ∀ y ∈ T, pos x = pos y) =
      (((Finset.univ : Finset (Fin k × Vec k)).filter fun x => x.2 x.1 = 0) ×ˢ S2 d a).image
        (fun q => q.2.1.image (emb q.1.2) ∪ q.2.2.image (emb (q.1.2 + ee q.1.1))) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨hτ, hall⟩
    rcases classify hτ with ⟨u, s, hs, rfl⟩ | ⟨i, u, hu, p, hp, rfl⟩
    · exact absurd (allSame_single u s) hall
    · exact ⟨i, u, p.1, p.2, ⟨hu, hp⟩, rfl⟩
  · rintro ⟨i, u, A, B, ⟨hu, hp⟩, rfl⟩
    exact ⟨split_mem_tops hp, not_allSame_split (S2_ne hp).1 (S2_ne hp).2⟩

/-- **The normalization constant.** -/
theorem total_weight (hd : 1 ≤ d) (hk : 1 ≤ k) :
    ∑ τ ∈ tops d k a, weight d k a τ = (k : ℚ) * (2 ^ (k - 1) : ℕ) * Kd d a := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (tops d k a)
    (fun T => ∀ x ∈ T, ∀ y ∈ T, pos x = pos y), singles_eq, splits_eq]
  rw [Finset.sum_image, Finset.sum_image]
  · -- evaluate the two sums
    have h1 : ∑ x ∈ (Finset.univ : Finset (Vec k)) ×ˢ S1 d a, weight d k a (x.2.image (emb x.1)) =
        ∑ x ∈ (Finset.univ : Finset (Vec k)) ×ˢ S1 d a, (((d : ℚ) - 1) * k) :=
      Finset.sum_congr rfl (fun x _ => weight_single (allSame_single _ _))
    have h2 : ∑ x ∈ ((Finset.univ : Finset (Fin k × Vec k)).filter fun x => x.2 x.1 = 0) ×ˢ S2 d a,
        weight d k a (x.2.1.image (emb x.1.2) ∪ x.2.2.image (emb (x.1.2 + ee x.1.1))) =
        ∑ x ∈ ((Finset.univ : Finset (Fin k × Vec k)).filter fun x => x.2 x.1 = 0) ×ˢ S2 d a,
          1 / (Nat.choose (d - 1) (x.2.1.card - 1) : ℚ) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Finset.mem_product] at hx
      exact weight_split' hd hx.2
    rw [h1, h2, Finset.sum_const, Finset.sum_product]
    simp only []
    rw [Finset.sum_const, card_base hk]
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, nsmul_eq_mul]
    unfold Kd Qd
    have h2k : (2 : ℚ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    push_cast
    rw [h2k]; ring
  · -- injectivity of the split parametrization
    rintro ⟨⟨i, u⟩, A, B⟩ hx ⟨⟨i', u'⟩, A', B'⟩ hx' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx hx'
    obtain ⟨hA, hB⟩ := S2_ne hx.2
    obtain ⟨hA', hB'⟩ := S2_ne hx'.2
    obtain ⟨rfl, h⟩ := split_eq hA hB hA' hB' h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨h0, -, -⟩
    · rfl
    · exfalso
      have := hx.1
      have h0' : u = u' + ee i := h0
      rw [h0'] at this
      simp only [Pi.add_apply, hx'.1, zero_add, ee, Pi.single_eq_same] at this
      exact one_ne_zero this
  · -- injectivity of the single-fibre parametrization
    rintro ⟨u, s⟩ hx ⟨u', s'⟩ hx' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, true_and] at hx hx'
    obtain ⟨rfl, rfl⟩ := img_emb_eq (S1_ne hx) h
    rfl

end AbelianCayleyHDX.Supplement.CubeLabel.X

open ReplParity (Vec)
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.Supplement.CubeLabel.X

open Finset AbelianCayleyHDX.XP OAI.MetricKMedian.Binary

variable {d k a : ℕ}

/-! ### Encodings -/

lemma encNat_eq (m : ℕ) : encNat m = encNatB m := by
  unfold encNat encBits encNatB
  congr 2
  rw [Nat.digits_two_eq_bits, List.map_map]
  conv_rhs => rw [← List.map_id m.bits]
  congr 1; funext b; cases b <;> rfl

lemma encZMod_eq (x : ZMod 2) : encZMod x = cbit (decide (x = 1)) := by
  fin_cases x <;> rfl

def bitsOf {m : ℕ} (v : Vec m) : List Bool := (List.ofFn v).map (fun x => decide (x = 1))

lemma encVec_eq {m : ℕ} (v : Vec m) : encVec v = vecB m (bitsOf v) := by
  unfold encVec encList vecB bitsOf
  rw [List.length_ofFn, encNat_eq, List.flatMap_map]
  congr 1
  exact List.flatMap_congr (fun x _ => encZMod_eq x)

lemma encRat_eq (q : ℚ) : AbelianCayleyHDX.encRat q = encRatB q := by
  unfold AbelianCayleyHDX.encRat encRatB; rw [encNat_eq, encNat_eq]

lemma bitsOf_emb (u : Vec k) (b : Vec a) : bitsOf (emb u b) = bitsOf u ++ bitsOf b := by
  unfold bitsOf emb
  rw [List.ofFn_fin_append, List.map_append]

lemma bitsOf_zero : bitsOf (0 : Vec k) = posZero k := by
  unfold bitsOf posZero
  apply List.ext_getElem (by simp)
  intro r h1 h2
  simp

lemma bitsOf_ee (i : Fin k) : bitsOf (ee i) = posE k i.val := by
  unfold bitsOf posE
  apply List.ext_getElem (by simp)
  intro r h1 h2
  simp only [List.getElem_map, List.getElem_ofFn, List.getElem_range, ee]
  by_cases hr : r = i.val
  · subst hr; simp
  · have : (⟨r, by simpa using h1⟩ : Fin k) ≠ i := fun h => hr (by rw [← h])
    simp [Pi.single_apply, this, hr]

lemma value_pow (m : ℕ) : Word.value (List.replicate m false ++ [true]) = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.cons_append, Word.value, ih]; simp [pow_succ]; ring

lemma pow2B_eq (k : ℕ) : pow2B k = 2 ^ (k - 1) := by
  unfold pow2B
  rw [show (List.range k).tail.map (fun _ => false) = List.replicate (k - 1) false by
    rw [List.map_const', List.length_tail, List.length_range], value_pow]

/-! ### The data -/

noncomputable def labNZ (a : ℕ) : List (List Bool) := (LNZ a).map bitsOf

noncomputable def wt2 (d : ℕ) (p : Finset (Vec a) × Finset (Vec a)) : ℚ :=
  1 / (Nat.choose (d - 1) (p.1.card - 1) : ℚ)

noncomputable def T1bits (d a : ℕ) : List (List (List Bool)) :=
  (T1L d a).map (fun s => s.toList.map bitsOf)

noncomputable def T2bits (d a : ℕ) : List (List (List Bool) × List (List Bool) × ℚ) :=
  (T2L d a).map (fun p => (p.1.toList.map bitsOf, p.2.toList.map bitsOf, wt2 d p))

noncomputable def repsP (d k a : ℕ) : List (List (Vec (k + a)) × ℚ) :=
  (T1L d a).map (fun s => (rep1 k s, ((d : ℚ) - 1) * (k : ℚ))) ++
    (List.finRange k).flatMap (fun i => (T2L d a).map (fun p => (rep2 i p, wt2 d p)))

lemma reps_eq : reps d k a = (repsP d k a).map Prod.fst := by
  simp [reps, repsP, List.map_flatMap, Function.comp_def]

lemma gensC_eq : gensC (labNZ a) k = (gensL k a).map bitsOf := by
  unfold gensC gensL labNZ
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def, bitsOf_emb]
  rw [List.flatMap_cons, List.flatMap_cons, bitsOf_zero]
  congr 1
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map, List.flatMap_map, List.flatMap_map]
  refine List.flatMap_congr (fun i _ => ?_)
  rw [bitsOf_ee]

lemma repsC_eq : repsC (T1bits d a) (T2bits d a) ((d : ℚ) - 1) k =
    (repsP d k a).map (fun e => (e.1.map bitsOf, e.2)) := by
  unfold repsC repsP T1bits T2bits
  rw [List.map_append]
  congr 1
  · simp only [List.map_map, Function.comp_def, rep1, bitsOf_emb, bitsOf_zero]
  · rw [List.map_flatMap, ← List.map_coe_finRange_eq_range, List.flatMap_map]
    refine List.flatMap_congr (fun i _ => ?_)
    simp only [List.map_map, Function.comp_def, rep2, List.map_append, bitsOf_emb,
      bitsOf_zero, bitsOf_ee]

lemma mu_repsP (hd : 1 ≤ d) (hk : 1 ≤ k) {e : List (Vec (k + a)) × ℚ} (he : e ∈ repsP d k a) :
    mu d k a e.1.toFinset = e.2 / ZB (Kd d a) k := by
  unfold mu ZB
  rw [total_weight hd hk, pow2B_eq]
  congr 1
  simp only [repsP, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange, true_and,
    T1L, T2L, Finset.mem_toList] at he
  rcases he with ⟨s, hs, rfl⟩ | ⟨i, p, hp, rfl⟩
  · exact weight_rep1 (T1_sub hs).1
  · exact weight_rep2 hd (T2_sub hp).1

/-- **The output string.** -/
theorem output_eq (hd : 1 ≤ d) (hk : 1 ≤ k) :
    encNat (k + a) ++ encList encVec (gensL k a) ++
      encList (fun r => encList encVec r ++ AbelianCayleyHDX.encRat (mu d k a r.toFinset))
        (reps d k a) =
    outB a (labNZ a) (T1bits d a) (T2bits d a) ((d : ℚ) - 1) (Kd d a) k := by
  unfold outB
  rw [encNat_eq, gensC_eq, repsC_eq, reps_eq]
  congr 1
  · unfold encList
    rw [encNat_eq, List.length_map, List.flatMap_map,
      List.flatMap_congr (fun v (_ : v ∈ gensL k a) => encVec_eq v)]

  · unfold encList
    rw [encNat_eq, List.length_map, List.length_map, List.flatMap_map, List.flatMap_map]
    congr 1
    refine List.flatMap_congr (fun e he => ?_)
    simp only
    rw [encNat_eq, List.length_map, List.flatMap_map, encRat_eq, mu_repsP hd hk he]
    congr 2
    exact List.flatMap_congr (fun v _ => encVec_eq v)

end AbelianCayleyHDX.Supplement.CubeLabel.X

open AbelianCayleyHDX.Supplement.CubeLabel AbelianCayleyHDX.Supplement.CubeLabel.X in
/-- **Explicitness of the cube–label family, indexed by `kⱼ = |encNat j|`.** -/
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    AbelianCayleyHDX.Supplement.IsExplicitWeightedFamily
      (fun j => (encNat j).length + (d + 2))
      (fun j => AbelianCayleyHDX.Supplement.CubeLabel.gens (encNat j).length (d + 2))
      (fun j => AbelianCayleyHDX.Supplement.CubeLabel.tops d (encNat j).length (d + 2))
      (fun j => AbelianCayleyHDX.Supplement.CubeLabel.mu d (encNat j).length (d + 2)) := by
  obtain ⟨M, p, hM⟩ := AbelianCayleyHDX.XP.outputsWithin_of_poly
    (AbelianCayleyHDX.XP.poly_outB (d + 2) (labNZ (d + 2)) (T1bits d (d + 2)) (T2bits d (d + 2))
      ((d : ℚ) - 1) (Kd d (d + 2)))
  refine ⟨M, p, fun j => ⟨gensL _ _, reps d _ _, gensL_nodup, gensL_toFinset, reps_nodup,
    fun r hr => rep_valid hr, fun τ hτ => exists_unique_rep hτ, ?_⟩⟩
  have hk : 1 ≤ (encNat j).length := by
    unfold encNat encBits; simp
  rw [output_eq (by omega) hk]
  exact hM (encNat j) _ (Nat.le_add_right _ _)
