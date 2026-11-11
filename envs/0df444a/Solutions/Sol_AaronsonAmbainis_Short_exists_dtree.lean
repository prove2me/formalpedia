-- Prove2me | solution 1 for AaronsonAmbainis.Short.exists_dtree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:27:24.2067+00:00
-- url     : https://prove2.me/submissions/0bdf2d15-4056-4fec-87a6-3bfd84243cad

import Mathlib
import Definitions.Def_AaronsonAmbainis_Short
import Theorems.Thm_AaronsonAmbainis_twoSidedInequality
open AaronsonAmbainis
open Finset

namespace AASolTree

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Average over the cube. -/
noncomputable def avg (g : Cube ι → ℝ) : ℝ := (∑ x, g x) / 2 ^ Fintype.card ι

/-- Real indicator of a proposition. -/
noncomputable def ind (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

lemma ind_nonneg (p : Prop) [Decidable p] : 0 ≤ ind p := by
  unfold ind; split_ifs <;> norm_num

lemma ind_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : ind p = ind q := by
  unfold ind; exact if_congr h rfl rfl

lemma avg_mono {f g : Cube ι → ℝ} (h : ∀ x, f x ≤ g x) : avg f ≤ avg g := by
  unfold avg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

lemma avg_nonneg {f : Cube ι → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg fun x _ => h x) (by positivity)

lemma avg_add (f g : Cube ι → ℝ) : avg (fun x => f x + g x) = avg f + avg g := by
  unfold avg; rw [Finset.sum_add_distrib, add_div]

lemma avg_congr {f g : Cube ι → ℝ} (h : ∀ x, f x = g x) : avg f = avg g := by
  rw [show f = g from funext h]

/-! ### Coordinate flips and restrictions -/

lemma fl_self (x : Cube ι) (i : ι) : flipSet x {i} i = !(x i) := by
  simp [flipSet]

lemma fl_fl (i : ι) (x : Cube ι) : flipSet (flipSet x {i}) {i} = x := by
  funext j
  by_cases h : j = i
  · subst h; simp [flipSet]
  · simp [flipSet, h]

lemma up_fl (x : Cube ι) (i : ι) (b : Bool) :
    Function.update (flipSet x {i}) i b = Function.update x i b := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [flipSet, h]

lemma up_self {x : Cube ι} {i : ι} {b : Bool} (h : x i = b) : Function.update x i b = x := by
  subst h; exact Function.update_eq_self i x

lemma fl_eq_up {x : Cube ι} {i : ι} {b : Bool} (h : x i = b) :
    flipSet x {i} = Function.update x i (!b) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [flipSet, h]
  · simp [flipSet, hj]

lemma fl_up_comm {i j : ι} (hj : j ≠ i) (x : Cube ι) (b : Bool) :
    Function.update (flipSet x {j}) i b = flipSet (Function.update x i b) {j} := by
  funext k
  by_cases hk : k = i
  · subst hk
    have : k ≠ j := fun h => hj h.symm
    simp [flipSet, this]
  · simp [Function.update_of_ne hk, flipSet]

lemma up_flipSet (x : Cube ι) (S : Finset ι) (i : ι) (b : Bool) :
    Function.update (flipSet x S) i b = flipSet (Function.update x i b) (S.erase i) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [flipSet]
  · simp [flipSet, hk]

/-- Splitting an average along coordinate `i`. -/
lemma avg_split (i : ι) (b : Bool) (h : Cube ι → ℝ) :
    avg h = avg (fun x => if x i = b then h x else 0)
      + avg (fun x => if x i = b then h (flipSet x {i}) else 0) := by
  have e : avg (fun x => if x i = b then h (flipSet x {i}) else 0)
      = avg (fun x => if x i = b then 0 else h x) := by
    unfold avg; congr 1
    refine (Fintype.sum_bijective (fun x : Cube ι => flipSet x {i})
      (Function.Involutive.bijective (fl_fl i)) _ _ ?_).symm
    intro x
    simp only [fl_fl, fl_self]
    cases hx : x i <;> cases b <;> simp
  rw [e, ← avg_add]
  apply avg_congr; intro x
  by_cases hx : x i = b
  · rw [if_pos hx, if_pos hx, add_zero]
  · rw [if_neg hx, if_neg hx, zero_add]

lemma avg_up (i : ι) (b : Bool) (g : Cube ι → ℝ) :
    avg (fun x => g (Function.update x i b)) = 2 * avg (fun x => if x i = b then g x else 0) := by
  have h1 : avg (fun x => if x i = b then g (Function.update x i b) else 0)
      = avg (fun x => if x i = b then g x else 0) := by
    apply avg_congr; intro x
    by_cases hx : x i = b
    · rw [if_pos hx, if_pos hx, up_self hx]
    · rw [if_neg hx, if_neg hx]
  have h2 : avg (fun x => if x i = b then g (Function.update (flipSet x {i}) i b) else 0)
      = avg (fun x => if x i = b then g x else 0) := by
    apply avg_congr; intro x
    by_cases hx : x i = b
    · rw [if_pos hx, if_pos hx, up_fl, up_self hx]
    · rw [if_neg hx, if_neg hx]
  have h3 := avg_split i b (fun x => g (Function.update x i b))
  rw [h3, two_mul]
  exact congrArg₂ (· + ·) h1 h2

lemma avg_restrict (i : ι) (g : Cube ι → ℝ) :
    avg (fun x => g (Function.update x i false)) + avg (fun x => g (Function.update x i true))
      = 2 * avg g := by
  rw [avg_up, avg_up, ← mul_add, ← avg_add]
  congr 1
  apply avg_congr; intro x
  cases x i <;> simp

/-! ### Densities, errors, influences -/

/-- Density of the points of `U` on which `G` equals `c`. -/
noncomputable def dl (c : Bool) (G : Cube ι → Bool) (U : Finset (Cube ι)) : ℝ :=
  avg (fun x => ind (x ∈ U ∧ G x = c))

/-- Density of the points of `U` on which `F` errs. -/
noncomputable def er (F G : Cube ι → Bool) (U : Finset (Cube ι)) : ℝ :=
  avg (fun x => ind (x ∈ U ∧ F x ≠ G x))

/-- Preimage of `U` under the restriction `x ↦ x[i := b]`. -/
def RU (i : ι) (b : Bool) (U : Finset (Cube ι)) : Finset (Cube ι) :=
  univ.filter (fun x => Function.update x i b ∈ U)

lemma mem_RU (i : ι) (b : Bool) (U : Finset (Cube ι)) (x : Cube ι) :
    x ∈ RU i b U ↔ Function.update x i b ∈ U := by
  simp [RU]

lemma dl_nonneg (c : Bool) (G : Cube ι → Bool) (U : Finset (Cube ι)) : 0 ≤ dl c G U :=
  avg_nonneg fun _ => ind_nonneg _

lemma er_nonneg (F G : Cube ι → Bool) (U : Finset (Cube ι)) : 0 ≤ er F G U :=
  avg_nonneg fun _ => ind_nonneg _

lemma er_eq (F G : Cube ι → Bool) (U : Finset (Cube ι)) :
    ((U.filter fun x => F x ≠ G x).card : ℝ) / 2 ^ Fintype.card ι = er F G U := by
  have h : U.filter (fun x => F x ≠ G x) = univ.filter (fun x => x ∈ U ∧ F x ≠ G x) := by
    ext x; simp
  unfold er avg ind
  rw [Finset.sum_boole, h]

lemma infl_eq (G : Cube ι → Bool) (j : ι) :
    infl G j = avg (fun x => ind (G (flipSet x {j}) ≠ G x)) := by
  unfold infl avg ind
  rw [Finset.sum_boole]

lemma infl_nonneg (G : Cube ι → Bool) (j : ι) : 0 ≤ infl G j := by
  rw [infl_eq]; exact avg_nonneg fun _ => ind_nonneg _

lemma er_const (c : Bool) (G : Cube ι → Bool) (U : Finset (Cube ι)) :
    er (fun _ => !c) G U = dl c G U := by
  unfold er dl
  apply avg_congr; intro x
  apply ind_congr
  cases c <;> cases G x <;> simp

lemma dl_restrict (i : ι) (c : Bool) (G : Cube ι → Bool) (U : Finset (Cube ι)) :
    dl c (fun x => G (Function.update x i false)) (RU i false U)
      + dl c (fun x => G (Function.update x i true)) (RU i true U) = 2 * dl c G U := by
  unfold dl
  simp only [mem_RU]
  exact avg_restrict i (fun x => ind (x ∈ U ∧ G x = c))

lemma infl_restrict_self (i : ι) (b : Bool) (G : Cube ι → Bool) :
    infl (fun x => G (Function.update x i b)) i = 0 := by
  rw [infl_eq]
  have : avg (fun x : Cube ι => ind (G (Function.update (flipSet x {i}) i b)
      ≠ G (Function.update x i b))) = avg (fun _ : Cube ι => (0 : ℝ)) := by
    apply avg_congr; intro x
    rw [up_fl]; simp [ind]
  rw [this]; simp [avg]

lemma infl_restrict_ne {i j : ι} (hj : j ≠ i) (G : Cube ι → Bool) :
    infl (fun x => G (Function.update x i false)) j
      + infl (fun x => G (Function.update x i true)) j = 2 * infl G j := by
  rw [infl_eq, infl_eq, infl_eq]
  simp only [fl_up_comm hj]
  exact avg_restrict i (fun x => ind (G (flipSet x {j}) ≠ G x))

lemma sum_infl_restrict (i : ι) (G : Cube ι → Bool) :
    ∑ j, infl (fun x => G (Function.update x i false)) j
      + ∑ j, infl (fun x => G (Function.update x i true)) j + 2 * infl G i
      = 2 * ∑ j, infl G j := by
  have h : ∀ j, infl (fun x => G (Function.update x i false)) j
      + infl (fun x => G (Function.update x i true)) j
      + (if j = i then 2 * infl G i else 0) = 2 * infl G j := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, infl_restrict_self, infl_restrict_self]; ring
    · rw [if_neg hj, infl_restrict_ne hj, add_zero]
  have h2 := Finset.sum_congr (rfl : (univ : Finset ι) = univ) (fun j _ => h j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' univ i,
    if_pos (mem_univ i), ← Finset.mul_sum] at h2
  exact h2

/-! ### Rows -/

lemma row_ge_one {G : Cube ι → Bool} {x y : Cube ι} (hxy : G y ≠ G x) {l : ι → ℝ}
    (h : IsRow G x l) : 1 ≤ ∑ j, l j := by
  have e : flipSet x (diffSet x y) = y := by
    funext j
    simp only [flipSet, diffSet, mem_filter, mem_univ, true_and]
    cases hx : x j <;> cases hy : y j <;> simp
  have h1 := h.2 (diffSet x y) (by rw [e]; exact hxy)
  exact le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => h.1 j))

lemma isRow_restrict {G : Cube ι → Bool} {lam : Cube ι → ι → ℝ} (hrow : ∀ x, IsRow G x (lam x))
    (i : ι) (b : Bool) (x : Cube ι) :
    IsRow (fun x => G (Function.update x i b)) x (lam (Function.update x i b)) := by
  refine ⟨(hrow _).1, ?_⟩
  intro S hS
  have hS' : G (flipSet (Function.update x i b) (S.erase i)) ≠ G (Function.update x i b) := by
    rw [← up_flipSet]; exact hS
  exact le_trans ((hrow _).2 _ hS')
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => (hrow _).1 j))

lemma exists_of_dl_pos {c : Bool} {G : Cube ι → Bool} {U : Finset (Cube ι)} (h : 0 < dl c G U) :
    ∃ x, x ∈ U ∧ G x = c := by
  by_contra hne
  have h0 : dl c G U = 0 := by
    unfold dl avg
    rw [Finset.sum_eq_zero, zero_div]
    intro x _
    unfold ind
    rw [if_neg]
    exact fun hx => hne ⟨x, hx⟩
  linarith

lemma dl_le (G : Cube ι → Bool) (lam : Cube ι → ι → ℝ) (hrow : ∀ x, IsRow G x (lam x))
    (U : Finset (Cube ι)) (γ : ℝ) (hγ : 0 < γ) (hU : ∀ x ∈ U, ∑ j, lam x j ≤ γ)
    (hnc : ∀ x, ∃ y, G y ≠ G x) (c : Bool) :
    dl c G U ≤ γ * ((∑ x ∈ univ.filter (fun x : Cube ι => G x = c), (∑ j, lam x j)⁻¹)
      / 2 ^ Fintype.card ι) := by
  unfold dl avg
  rw [Finset.sum_filter, ← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  have hnn : 0 ≤ ∑ j, lam x j := Finset.sum_nonneg fun j _ => (hrow x).1 j
  by_cases hx : x ∈ U ∧ G x = c
  · obtain ⟨y, hy⟩ := hnc x
    have h1 : 1 ≤ ∑ j, lam x j := row_ge_one hy (hrow x)
    have hpos : 0 < ∑ j, lam x j := by linarith
    have h2 := hU x hx.1
    unfold ind
    rw [if_pos hx, if_pos hx.2, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  · unfold ind
    rw [if_neg hx]
    apply mul_nonneg hγ.le
    split_ifs
    · exact inv_nonneg.mpr hnn
    · exact le_refl _

lemma key (G : Cube ι → Bool) (lam : Cube ι → ι → ℝ) (hrow : ∀ x, IsRow G x (lam x))
    (U : Finset (Cube ι)) (γ : ℝ) (hγ : 0 < γ) (hU : ∀ x ∈ U, ∑ j, lam x j ≤ γ)
    (hf : 0 < dl false G U) (ht : 0 < dl true G U)
    (τ : ℝ) (hτ : 0 ≤ τ) (hinf : ∀ j, infl G j ≤ τ) :
    dl false G U * dl true G U ≤ γ ^ 2 / 4 * τ := by
  obtain ⟨x0, -, h0⟩ := exists_of_dl_pos hf
  obtain ⟨x1, -, h1⟩ := exists_of_dl_pos ht
  have hnc : ∀ x, ∃ y, G y ≠ G x := by
    intro x
    cases h : G x
    · exact ⟨x1, by simp [h1]⟩
    · exact ⟨x0, by simp [h0]⟩
  have hF := dl_le G lam hrow U γ hγ hU hnc false
  have hT := dl_le G lam hrow U γ hγ hU hnc true
  have h2 := AaronsonAmbainis.twoSidedInequality ι G lam hrow τ hτ hinf
  set At := (∑ x ∈ univ.filter (fun x : Cube ι => G x = true), (∑ j, lam x j)⁻¹)
    / 2 ^ Fintype.card ι with hAt
  set Af := (∑ x ∈ univ.filter (fun x : Cube ι => G x = false), (∑ j, lam x j)⁻¹)
    / 2 ^ Fintype.card ι with hAf
  have h3 : dl false G U * dl true G U ≤ (γ * Af) * (γ * At) :=
    mul_le_mul hF hT ht.le (le_trans hf.le hF)
  have h4 : γ ^ 2 / 4 * (4 * At * Af) ≤ γ ^ 2 / 4 * τ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : (γ * Af) * (γ * At) = γ ^ 2 / 4 * (4 * At * Af) := by ring
  linarith

/-! ### Decision trees -/

lemma dtree_mono {n : ℕ} {h : Cube ι → Bool} (hh : Short.DTree n h) : Short.DTree (n + 1) h := by
  induction hh with
  | const n c => exact Short.DTree.const (n + 1) c
  | query n i h0 h1 _ _ ih0 ih1 => exact Short.DTree.query (n + 1) i h0 h1 ih0 ih1

lemma dtree_restrict (i : ι) (c : Bool) {n : ℕ} {h : Cube ι → Bool} (hh : Short.DTree n h) :
    Short.DTree n (fun x => h (Function.update x i c)) := by
  induction hh with
  | const n c' => exact Short.DTree.const n c'
  | query n j h0 h1 _ _ ih0 ih1 =>
    by_cases hj : j = i
    · subst hj
      cases c
      · have e : (fun x : Cube ι => if (Function.update x j false) j
            then h1 (Function.update x j false) else h0 (Function.update x j false))
            = fun x => h0 (Function.update x j false) := by
          funext x; simp
        rw [e]; exact dtree_mono ih0
      · have e : (fun x : Cube ι => if (Function.update x j true) j
            then h1 (Function.update x j true) else h0 (Function.update x j true))
            = fun x => h1 (Function.update x j true) := by
          funext x; simp
        rw [e]; exact dtree_mono ih1
    · have e : (fun x : Cube ι => if (Function.update x i c) j
          then h1 (Function.update x i c) else h0 (Function.update x i c))
          = fun x => if x j then (fun x => h1 (Function.update x i c)) x
            else (fun x => h0 (Function.update x i c)) x := by
        funext x; simp [Function.update_of_ne hj]
      rw [e]; exact Short.DTree.query n j _ _ ih0 ih1

/-- Remove the dependence of a subtree on the queried coordinate without increasing the error
on the relevant half-cube beyond half the error of the restricted problem. -/
lemma fix_tree (G : Cube ι → Bool) (U : Finset (Cube ι)) (i : ι) (b : Bool) (s : ℕ)
    (Fb : Cube ι → Bool) (hFb : Short.DTree s Fb) :
    ∃ F' : Cube ι → Bool, Short.DTree s F' ∧
      avg (fun x => ind (x i = b ∧ x ∈ U ∧ F' x ≠ G x))
        ≤ er Fb (fun x => G (Function.update x i b)) (RU i b U) / 2 := by
  have hsplit : er Fb (fun x => G (Function.update x i b)) (RU i b U)
      = avg (fun x => if x i = b then
            ind (Function.update x i b ∈ U ∧ Fb x ≠ G (Function.update x i b)) else 0)
        + avg (fun x => if x i = b then
            ind (Function.update (flipSet x {i}) i b ∈ U
              ∧ Fb (flipSet x {i}) ≠ G (Function.update (flipSet x {i}) i b)) else 0) := by
    unfold er
    simp only [mem_RU]
    exact avg_split i b _
  have hA : avg (fun x => if x i = b then
        ind (Function.update x i b ∈ U ∧ Fb x ≠ G (Function.update x i b)) else 0)
      = avg (fun x => ind (x i = b ∧ x ∈ U ∧ Fb (Function.update x i b) ≠ G x)) := by
    apply avg_congr; intro x
    by_cases hx : x i = b
    · rw [if_pos hx, up_self hx]
      exact ind_congr (by simp [hx])
    · rw [if_neg hx]; unfold ind; rw [if_neg (fun h => hx h.1)]
  have hB : avg (fun x => if x i = b then
        ind (Function.update (flipSet x {i}) i b ∈ U
          ∧ Fb (flipSet x {i}) ≠ G (Function.update (flipSet x {i}) i b)) else 0)
      = avg (fun x => ind (x i = b ∧ x ∈ U ∧ Fb (Function.update x i (!b)) ≠ G x)) := by
    apply avg_congr; intro x
    by_cases hx : x i = b
    · rw [if_pos hx, up_fl, up_self hx, fl_eq_up hx]
      exact ind_congr (by simp [hx])
    · rw [if_neg hx]; unfold ind; rw [if_neg (fun h => hx h.1)]
  rw [hA, hB] at hsplit
  rcases le_total (avg (fun x => ind (x i = b ∧ x ∈ U ∧ Fb (Function.update x i b) ≠ G x)))
      (avg (fun x => ind (x i = b ∧ x ∈ U ∧ Fb (Function.update x i (!b)) ≠ G x))) with h | h
  · exact ⟨fun x => Fb (Function.update x i b), dtree_restrict i b hFb, by linarith⟩
  · exact ⟨fun x => Fb (Function.update x i (!b)), dtree_restrict i (!b) hFb, by linarith⟩

lemma er_query (G : Cube ι → Bool) (U : Finset (Cube ι)) (i : ι) (F0 F1 : Cube ι → Bool) :
    er (fun x => if x i then F1 x else F0 x) G U
      = avg (fun x => ind (x i = false ∧ x ∈ U ∧ F0 x ≠ G x))
        + avg (fun x => ind (x i = true ∧ x ∈ U ∧ F1 x ≠ G x)) := by
  unfold er
  rw [← avg_add]
  apply avg_congr; intro x
  unfold ind
  cases hx : x i <;> simp [hx]

/-! ### The induction -/

/-- The strengthened conclusion. -/
def Good (γ : ℝ) (s : ℕ) (G : Cube ι → Bool) (U : Finset (Cube ι)) : Prop :=
  ∃ F : Cube ι → Bool, Short.DTree s F ∧ er F G U ≤ dl false G U ∧ er F G U ≤ dl true G U ∧
    (s : ℝ) * er F G U ^ 2 ≤ γ ^ 2 / 4 * ∑ j, infl G j

lemma rhs_nonneg (γ : ℝ) (G : Cube ι → Bool) : 0 ≤ γ ^ 2 / 4 * ∑ j, infl G j :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => infl_nonneg G j)

lemma good_of_zero (γ : ℝ) (s : ℕ) (G : Cube ι → Bool) (U : Finset (Cube ι)) (c : Bool)
    (h : dl c G U = 0) : Good γ s G U := by
  refine ⟨fun _ => !c, Short.DTree.const s _, ?_, ?_, ?_⟩
  · rw [er_const, h]; exact dl_nonneg _ _ _
  · rw [er_const, h]; exact dl_nonneg _ _ _
  · rw [er_const, h]
    have := rhs_nonneg γ G
    simpa using this

lemma good_zero (γ : ℝ) (G : Cube ι → Bool) (U : Finset (Cube ι)) : Good γ 0 G U := by
  have hr := rhs_nonneg γ G
  rcases le_total (dl false G U) (dl true G U) with h | h
  · refine ⟨fun _ => !false, Short.DTree.const 0 _, ?_, ?_, ?_⟩
    · rw [er_const]
    · rw [er_const]; exact h
    · simpa using hr
  · refine ⟨fun _ => !true, Short.DTree.const 0 _, ?_, ?_, ?_⟩
    · rw [er_const]; exact h
    · rw [er_const]
    · simpa using hr

lemma arith {s e ef et c If It ii I df dt : ℝ} (hs : 0 ≤ s) (he0 : 0 ≤ e)
    (he : e ≤ (ef + et) / 2)
    (hf : s * ef ^ 2 ≤ c * If) (ht : s * et ^ 2 ≤ c * It)
    (hsum : If + It + 2 * ii = 2 * I)
    (hdf : e ≤ df) (hdt : e ≤ dt) (hkey : df * dt ≤ c * ii) :
    (s + 1) * e ^ 2 ≤ c * I := by
  have h1 : e ^ 2 ≤ ((ef + et) / 2) ^ 2 := pow_le_pow_left₀ he0 he 2
  have h2 : ((ef + et) / 2) ^ 2 ≤ (ef ^ 2 + et ^ 2) / 2 := by
    nlinarith [sq_nonneg (ef - et)]
  have h3 : s * e ^ 2 ≤ s * ((ef ^ 2 + et ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left (le_trans h1 h2) hs
  have h4 : e * e ≤ df * dt := mul_le_mul hdf hdt he0 (le_trans he0 hdf)
  have h5 : c * If + c * It + 2 * (c * ii) = 2 * (c * I) := by
    linear_combination c * hsum
  have h6 : e ^ 2 = e * e := sq e
  have h7 : s * ((ef ^ 2 + et ^ 2) / 2) = (s * ef ^ 2 + s * et ^ 2) / 2 := by ring
  have h8 : (s + 1) * e ^ 2 = s * e ^ 2 + e ^ 2 := by ring
  linarith

theorem main (γ : ℝ) (hγ : 0 < γ) (s : ℕ) :
    ∀ (G : Cube ι → Bool) (lam : Cube ι → ι → ℝ), (∀ x, IsRow G x (lam x)) →
      ∀ U : Finset (Cube ι), (∀ x ∈ U, ∑ j, lam x j ≤ γ) → Good γ s G U := by
  induction s with
  | zero => intro G lam _ U _; exact good_zero γ G U
  | succ s ih =>
    intro G lam hrow U hU
    by_cases hf0 : dl false G U = 0
    · exact good_of_zero γ _ G U false hf0
    by_cases ht0 : dl true G U = 0
    · exact good_of_zero γ _ G U true ht0
    have hf : 0 < dl false G U := lt_of_le_of_ne (dl_nonneg _ _ _) (Ne.symm hf0)
    have ht : 0 < dl true G U := lt_of_le_of_ne (dl_nonneg _ _ _) (Ne.symm ht0)
    obtain ⟨x0, -, h0⟩ := exists_of_dl_pos hf
    obtain ⟨x1, -, h1⟩ := exists_of_dl_pos ht
    have hne : Nonempty ι := by
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      have : x0 = x1 := Subsingleton.elim _ _
      rw [this, h1] at h0
      exact Bool.noConfusion h0
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image (univ : Finset ι) (infl G) univ_nonempty
    have hkey := key G lam hrow U γ hγ hU hf ht (infl G i) (infl_nonneg G i)
      (fun j => hi j (mem_univ j))
    have IH : ∀ b : Bool, Good γ s (fun x => G (Function.update x i b)) (RU i b U) := fun b =>
      ih _ (fun x => lam (Function.update x i b)) (isRow_restrict hrow i b) _
        (fun x hx => hU _ ((mem_RU i b U x).1 hx))
    obtain ⟨Ff, hFf, hff, hft, hfb⟩ := IH false
    obtain ⟨Ft, hFt, htf, htt, htb⟩ := IH true
    obtain ⟨Ff', hFf', hff'⟩ := fix_tree G U i false s Ff hFf
    obtain ⟨Ft', hFt', htt'⟩ := fix_tree G U i true s Ft hFt
    have hq := er_query G U i Ff' Ft'
    have hdf := dl_restrict i false G U
    have hdt := dl_restrict i true G U
    have hsum := sum_infl_restrict i G
    have he0 := er_nonneg (fun x => if x i then Ft' x else Ff' x) G U
    have he : er (fun x => if x i then Ft' x else Ff' x) G U
        ≤ (er Ff (fun x => G (Function.update x i false)) (RU i false U)
          + er Ft (fun x => G (Function.update x i true)) (RU i true U)) / 2 := by
      linarith
    refine ⟨fun x => if x i then Ft' x else Ff' x, Short.DTree.query s i Ff' Ft' hFf' hFt',
      by linarith, by linarith, ?_⟩
    have := arith (Nat.cast_nonneg s) he0 he hfb htb hsum
      (by linarith : er (fun x => if x i then Ft' x else Ff' x) G U ≤ dl false G U)
      (by linarith : er (fun x => if x i then Ft' x else Ff' x) G U ≤ dl true G U) hkey
    rw [Nat.cast_succ]
    exact this

end AASolTree

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Cube ι → Bool) (lam : Cube ι → ι → ℝ) (hrow : ∀ x, IsRow G x (lam x))
    (U : Finset (Cube ι)) (γ : ℝ) (hγ : 0 < γ) (hU : ∀ x ∈ U, ∑ j, lam x j ≤ γ) (s : ℕ) :
    ∃ F : Cube ι → Bool, Short.DTree s F ∧
      (s : ℝ) * (((U.filter fun x => F x ≠ G x).card : ℝ) / 2 ^ Fintype.card ι) ^ 2
        ≤ γ ^ 2 / 4 * ∑ j, infl G j := by
  obtain ⟨F, hF, -, -, hb⟩ := AASolTree.main γ hγ s G lam hrow U hU
  exact ⟨F, hF, by rw [AASolTree.er_eq]; exact hb⟩
