-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:28.315399+00:00
-- url     : https://prove2.me/theorems/942362dd-9558-427a-bba4-6253852aa4d2
-- title:
--   Levi Quotient Of Block Det
-- statement:
--   Definitions and structural lemmas for Levi Quotient Of Block Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
section Gen
variable {α κ β : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
def Pm (R : Type) [CommRing R] (e : κ → α) : Matrix α κ R := (1 : Matrix α α R).submatrix id e
open Classical in

def Dm (R : Type) [CommRing R] (e : κ → α) : Matrix α α R :=
  Matrix.diagonal fun a => if a ∈ Set.range e then 0 else 1
def jM (e : κ → α) (m : Matrix κ κ R) : Matrix α α R := Pm R e * m * (Pm R e)ᵀ + Dm R e
theorem Pm_apply (e : κ → α) (a : α) (x : κ) : Pm R e a x = if a = e x then 1 else 0 := by
  simp [Pm, Matrix.one_apply]
theorem Pmt_mul [Fintype β] (e : κ → α) (g : Matrix α β R) (x : κ) (b : β) :
    ((Pm R e)ᵀ * g) x b = g (e x) b := by
  simp [Matrix.mul_apply, Pm_apply]
theorem mul_Pm [Fintype β] (e : κ → α) (g : Matrix β α R) (b : β) (x : κ) :
    (g * Pm R e) b x = g b (e x) := by
  simp [Matrix.mul_apply, Pm_apply]
theorem Dm_apply (e : κ → α) (a b : α) :
    Dm R e a b = if a = b ∧ a ∉ Set.range e then 1 else 0 := by
  classical
  unfold Dm
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq]
    by_cases h2 : a ∈ Set.range e
    · rw [if_pos h2, if_neg fun hh => hh.2 h2]
    · rw [if_neg h2, if_pos ⟨rfl, h2⟩]
  · rw [Matrix.diagonal_apply_ne _ h, if_neg fun hh => h hh.1]
theorem Pmt_Pm {e : κ → α} (he : Function.Injective e) : (Pm R e)ᵀ * Pm R e = 1 := by
  ext x y
  rw [Pmt_mul, Pm_apply, Matrix.one_apply]
  simp [he.eq_iff]
theorem Pmt_Dm (e : κ → α) : (Pm R e)ᵀ * Dm R e = 0 := by
  ext x a
  rw [Pmt_mul, Dm_apply, if_neg fun hh => hh.2 ⟨x, rfl⟩]
  rfl
theorem Dm_Pm (e : κ → α) : Dm R e * Pm R e = 0 := by
  ext a x
  rw [mul_Pm, Dm_apply, if_neg fun hh => hh.2 ⟨x, hh.1.symm⟩]
  rfl
theorem Dm_Dm (e : κ → α) : Dm R e * Dm R e = Dm R e := by
  classical
  unfold Dm
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : a ∈ Set.range e <;> simp [h]
theorem Pm_Pmt_add {e : κ → α} (he : Function.Injective e) :
    Pm R e * (Pm R e)ᵀ + Dm R e = 1 := by
  ext a b
  rw [Matrix.add_apply, Dm_apply, Matrix.one_apply]
  by_cases h : a ∈ Set.range e
  · obtain ⟨x, rfl⟩ := h
    have : (Pm R e * (Pm R e)ᵀ) (e x) b = if e x = b then 1 else 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single x]
      · simp [Pm_apply, eq_comm]
      · intro y _ hy
        simp [Pm_apply, he.eq_iff, Ne.symm hy]
      · simp
    rw [this]
    simp
  · have : (Pm R e * (Pm R e)ᵀ) a b = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun y _ => ?_
      have : a ≠ e y := fun hh => h ⟨y, hh.symm⟩
      simp [Pm_apply, this]
    rw [this]
    simp [h]
theorem jM_one {e : κ → α} (he : Function.Injective e) : jM e (1 : Matrix κ κ R) = 1 := by
  simp [jM, Pm_Pmt_add he]
theorem jM_mul {e : κ → α} (he : Function.Injective e) (m n : Matrix κ κ R) :
    jM e (m * n) = jM e m * jM e n := by
  unfold jM
  have h1 : Pm R e * m * (Pm R e)ᵀ * (Pm R e * n * (Pm R e)ᵀ) = Pm R e * (m * n) * (Pm R e)ᵀ := by
    calc _ = Pm R e * m * ((Pm R e)ᵀ * Pm R e) * n * (Pm R e)ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Pmt_Pm he]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h2 : Pm R e * m * (Pm R e)ᵀ * Dm R e = 0 := by
    rw [Matrix.mul_assoc, Pmt_Dm, Matrix.mul_zero]
  have h3 : Dm R e * (Pm R e * n * (Pm R e)ᵀ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Dm_Pm]; simp
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2, h3, Dm_Dm]
  simp
theorem jM_off_right (e : κ → α) (m : Matrix κ κ R) (a b : α) (h : b ∉ Set.range e) :
    jM e m a b = (1 : Matrix α α R) a b := by
  have h0 : ∀ y, Pm R e b y = 0 := fun y => by
    have : b ≠ e y := fun hh => h ⟨y, hh.symm⟩
    simp [Pm_apply, this]
  unfold jM
  rw [Matrix.add_apply, Matrix.mul_apply, Dm_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp [h0, h]
  · simp [h0, hab]
theorem Pm_map {S : Type} [CommRing S] (f : R →+* S) (e : κ → α) : (Pm R e).map f = Pm S e := by
  ext a x
  simp only [Matrix.map_apply, Pm_apply]
  split_ifs <;> simp
theorem Dm_map {S : Type} [CommRing S] (f : R →+* S) (e : κ → α) : (Dm R e).map f = Dm S e := by
  ext a b
  simp only [Matrix.map_apply, Dm_apply]
  split_ifs <;> simp
theorem jM_map {S : Type} [CommRing S] (f : R →+* S) (e : κ → α) (m : Matrix κ κ R) :
    (jM e m).map f = jM e (m.map f) := by
  unfold jM
  rw [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_mul, Pm_map, Dm_map, Matrix.transpose_map, Pm_map]
theorem Dm_transpose (e : κ → α) : (Dm R e)ᵀ = Dm R e := by
  classical
  unfold Dm
  simp
theorem jM_transpose (e : κ → α) (m : Matrix κ κ R) : (jM e m)ᵀ = jM e mᵀ := by
  unfold jM
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Dm_transpose,
    Matrix.mul_assoc]
def jH (e : κ → α) (he : Function.Injective e) : Matrix κ κ R →* Matrix α α R where
  toFun := jM e
  map_one' := jM_one he
  map_mul' := jM_mul he
theorem sub_mul_of (e : κ → α) (he : Function.Injective e) (a b : Matrix α α R)
    (h : ∀ x y, ∀ m, m ∉ Set.range e → a (e x) m * b m (e y) = 0) :
    (a * b).submatrix e e = a.submatrix e e * b.submatrix e e := by
  ext x y
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
  symm
  exact Fintype.sum_of_injective e he _ _ (fun m hm => h x y m hm) (fun _ => rfl)
end Gen
section Split
variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R] {s : Set ι}
def emb (s : Set ι) : (↥sᶜ ⊕ ↥sᶜ) → ι ⊕ ι := Sum.map Subtype.val Subtype.val
theorem emb_inj : Function.Injective (emb s) :=
  Sum.map_injective.2 ⟨Subtype.val_injective, Subtype.val_injective⟩
theorem inl_mem_range (i : ι) : Sum.inl i ∈ Set.range (emb s) ↔ i ∉ s := by
  constructor
  · rintro ⟨x | x, h⟩
    · have : x.1 = i := Sum.inl_injective h
      exact this ▸ x.2
    · cases h
  · exact fun h => ⟨Sum.inl ⟨i, h⟩, rfl⟩
theorem inr_mem_range (i : ι) : Sum.inr i ∈ Set.range (emb s) ↔ i ∉ s := by
  constructor
  · rintro ⟨x | x, h⟩
    · cases h
    · have : x.1 = i := Sum.inr_injective h
      exact this ▸ x.2
  · exact fun h => ⟨Sum.inr ⟨i, h⟩, rfl⟩
theorem not_range_cases {m : ι ⊕ ι} (h : m ∉ Set.range (emb s)) :
    (∃ i ∈ s, m = Sum.inl i) ∨ ∃ i ∈ s, m = Sum.inr i := by
  rcases m with i | i
  · exact Or.inl ⟨i, by_contra fun hi => h ((inl_mem_range i).2 hi), rfl⟩
  · exact Or.inr ⟨i, by_contra fun hi => h ((inr_mem_range i).2 hi), rfl⟩
theorem emb_not_inl (x : ↥sᶜ ⊕ ↥sᶜ) : emb s x ∉ (Sum.inl '' s : Set (ι ⊕ ι)) := by
  rintro ⟨i, hi, h⟩
  exact (inl_mem_range i).1 ⟨x, h.symm⟩ hi
theorem emb_not_inr (x : ↥sᶜ ⊕ ↥sᶜ) : emb s x ∉ (Sum.inr '' s : Set (ι ⊕ ι)) := by
  rintro ⟨i, hi, h⟩
  exact (inr_mem_range i).1 ⟨x, h.symm⟩ hi
theorem J_mul_inl {β : Type} (ε : ℤˣ) (b : Matrix (ι ⊕ ι) β R) (i : ι) (c : β) :
    (Ad.J R ε ι * b) (Sum.inl i) c = b (Sum.inr i) c := by
  simp [Ad.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
theorem J_mul_inr {β : Type} (ε : ℤˣ) (b : Matrix (ι ⊕ ι) β R) (i : ι) (c : β) :
    (Ad.J R ε ι * b) (Sum.inr i) c = ((ε : ℤ) : R) * b (Sum.inl i) c := by
  simp [Ad.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
theorem mul_J_inl {β : Type} [Fintype β] (ε : ℤˣ) (b : Matrix β (ι ⊕ ι) R) (a : β) (j : ι) :
    (b * Ad.J R ε ι) a (Sum.inl j) = ((ε : ℤ) : R) * b a (Sum.inr j) := by
  simp [Ad.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, mul_comm]
theorem mul_J_inr {β : Type} [Fintype β] (ε : ℤˣ) (b : Matrix β (ι ⊕ ι) R) (a : β) (j : ι) :
    (b * Ad.J R ε ι) a (Sum.inr j) = b a (Sum.inl j) := by
  simp [Ad.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
theorem J_off (ε : ℤˣ) {m : ι ⊕ ι} (h : m ∉ Set.range (emb s))
    (y : ↥sᶜ ⊕ ↥sᶜ) : Ad.J R ε ι m (emb s y) = 0 := by
  rcases not_range_cases h with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> rcases y with y | y <;>
    have hne : i ≠ y.1 := fun h => y.2 (h ▸ hi)
  all_goals simp [Ad.J, emb, Matrix.one_apply, hne]
section Comp
variable [Fintype ↥sᶜ] [DecidableEq ↥sᶜ]
theorem sub_J (ε : ℤˣ) : (Ad.J R ε ι).submatrix (emb s) (emb s) = Ad.J R ε ↥sᶜ := by
  ext (a | a) (b | b) <;> simp [Ad.J, emb, Matrix.one_apply, Subtype.ext_iff]
theorem J_Pm (ε : ℤˣ) : Ad.J R ε ι * Pm R (emb s) = Pm R (emb s) * Ad.J R ε ↥sᶜ := by
  ext (a | a) (b | b)
  · rw [J_mul_inl, mul_J_inl, Pm_apply, Pm_apply]; simp [emb]
  · rw [J_mul_inl, mul_J_inr, Pm_apply, Pm_apply]; simp [emb]
  · rw [J_mul_inr, mul_J_inl, Pm_apply, Pm_apply]; simp [emb]
  · rw [J_mul_inr, mul_J_inr, Pm_apply, Pm_apply]; simp [emb]
theorem Pmt_J (ε : ℤˣ) : (Pm R (emb s))ᵀ * Ad.J R ε ι = Ad.J R ε ↥sᶜ * (Pm R (emb s))ᵀ := by
  ext (a | a) (b | b)
  · rw [Pmt_mul, J_mul_inl, Matrix.transpose_apply, Pm_apply]; simp [Ad.J, emb]
  · rw [Pmt_mul, J_mul_inl, Matrix.transpose_apply, Pm_apply]
    simp [Ad.J, emb, Matrix.one_apply, eq_comm]
  · rw [Pmt_mul, J_mul_inr, Matrix.transpose_apply, Pm_apply]
    simp [Ad.J, emb, Matrix.one_apply, eq_comm]
  · rw [Pmt_mul, J_mul_inr, Matrix.transpose_apply, Pm_apply]; simp [Ad.J, emb]
theorem J_Dm (ε : ℤˣ) : Ad.J R ε ι * Dm R (emb s) = Dm R (emb s) * Ad.J R ε ι := by
  have hd : ∀ a b : ι, Dm R (emb s) (Sum.inl a) (Sum.inl b) = Dm R (emb s) (Sum.inr a) (Sum.inr b) := fun a b => by
    rw [Dm_apply, Dm_apply]
    refine if_congr ?_ rfl rfl
    rw [inl_mem_range, inr_mem_range, Sum.inl.injEq, Sum.inr.injEq]
  ext (a | a) (b | b)
  · rw [J_mul_inl, mul_J_inl, Dm_apply, Dm_apply]; simp
  · rw [J_mul_inl, mul_J_inr, hd]
  · rw [J_mul_inr, mul_J_inl, hd]
  · rw [J_mul_inr, mul_J_inr, Dm_apply, Dm_apply]; simp
theorem jM_unitary (ε : ℤˣ) (x y : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R)
    (h : x * Ad.J R ε ↥sᶜ * y = Ad.J R ε ↥sᶜ) :
    jM (emb s) x * Ad.J R ε ι * jM (emb s) y = Ad.J R ε ι := by
  unfold jM
  set p := Pm R (emb s)
  set D := Dm R (emb s)
  have hp : pᵀ * p = 1 := Pmt_Pm emb_inj
  have hc : p * pᵀ + D = 1 := Pm_Pmt_add emb_inj
  have h1 : pᵀ * D = 0 := Pmt_Dm _
  have h2 : D * p = 0 := Dm_Pm _
  have h3 : D * D = D := Dm_Dm _
  have h4 : Ad.J R ε ι * p = p * Ad.J R ε ↥sᶜ := J_Pm ε
  have h5 : pᵀ * Ad.J R ε ι = Ad.J R ε ↥sᶜ * pᵀ := Pmt_J ε
  have h6 : Ad.J R ε ι * D = D * Ad.J R ε ι := J_Dm ε
  have e1 : (p * x * pᵀ + D) * Ad.J R ε ι = p * x * Ad.J R ε ↥sᶜ * pᵀ + D * Ad.J R ε ι := by
    rw [Matrix.add_mul, Matrix.mul_assoc (p * x), h5]
    simp only [Matrix.mul_assoc]
  have e2 : p * x * Ad.J R ε ↥sᶜ * pᵀ * (p * y * pᵀ) = Ad.J R ε ι * (p * pᵀ) := by
    calc _ = p * x * Ad.J R ε ↥sᶜ * (pᵀ * p) * y * pᵀ := by simp only [Matrix.mul_assoc]
      _ = p * (x * Ad.J R ε ↥sᶜ * y) * pᵀ := by rw [hp]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by rw [h, ← Matrix.mul_assoc, ← h4]
  have e3 : p * x * Ad.J R ε ↥sᶜ * pᵀ * D = 0 := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have e4 : D * Ad.J R ε ι * (p * y * pᵀ) = 0 := by
    calc _ = D * (Ad.J R ε ι * p) * y * pᵀ := by simp only [Matrix.mul_assoc]
      _ = (D * p) * Ad.J R ε ↥sᶜ * y * pᵀ := by rw [h4]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h2]; simp
  have e5 : D * Ad.J R ε ι * D = Ad.J R ε ι * D := by
    rw [← h6, Matrix.mul_assoc, h3]
  rw [e1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e2, e3, e4, e5, add_zero, zero_add, ← Matrix.mul_add, hc,
    Matrix.mul_one]
end Comp
structure Tri (s : Set ι) (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) : Prop where
  col : ∀ r, r ∉ (Sum.inl '' s : Set (ι ⊕ ι)) → ∀ i ∈ s, g r (Sum.inl i) = 0
  row : ∀ i ∈ s, ∀ c, c ∉ (Sum.inr '' s : Set (ι ⊕ ι)) → g (Sum.inr i) c = 0
section Comp2
variable [Fintype ↥sᶜ] [DecidableEq ↥sᶜ]
theorem Tri.sub_mul {a b : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (ha : Tri s a) (hb : Tri s b) :
    (a * b).submatrix (emb s) (emb s) = a.submatrix (emb s) (emb s) * b.submatrix (emb s) (emb s) := by
  refine sub_mul_of _ emb_inj a b fun x y m hm => ?_
  rcases not_range_cases hm with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · rw [ha.col _ (emb_not_inl x) i hi, zero_mul]
  · rw [hb.row i hi _ (emb_not_inr y), mul_zero]
theorem Tri.sub_unitary (ε : ℤˣ) {a b : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (ha : Tri s a) (hb : Tri s b) :
    (aᵀ * Ad.J R ε ι * b).submatrix (emb s) (emb s) =
      (a.submatrix (emb s) (emb s))ᵀ * Ad.J R ε ↥sᶜ * b.submatrix (emb s) (emb s) := by
  rw [sub_mul_of _ emb_inj (aᵀ * Ad.J R ε ι) b, sub_mul_of _ emb_inj aᵀ (Ad.J R ε ι), sub_J]
  · rfl
  · intro x y m hm
    rw [J_off ε hm, mul_zero]
  · intro x y m hm
    rcases not_range_cases hm with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [mul_J_inl, Matrix.transpose_apply, ha.row i hi _ (emb_not_inr x)]
      simp
    · rw [hb.row i hi _ (emb_not_inr y), mul_zero]
end Comp2
theorem row_of_stab (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (ε : ℤˣ) (g : GL (ι ⊕ ι) R)
    (hJ : (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map σ = Ad.J R ε ι)
    (hc : ∀ r, r ∉ (Sum.inl '' s : Set (ι ⊕ ι)) → ∀ c ∈ (Sum.inl '' s : Set (ι ⊕ ι)),
      ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) r c = 0) :
    ∀ i ∈ s, ∀ c, c ∉ (Sum.inr '' s : Set (ι ⊕ ι)) → (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) c = 0 := by
  intro i hi c hcs
  have h0 : ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h1 : Ad.J R ε ι * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map σ =
      ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι := by
    conv_rhs => rw [← hJ]
    simp only [← Matrix.mul_assoc]
    rw [h0, Matrix.one_mul]
  have h2 := congrFun (congrFun h1 (Sum.inl i)) c
  rw [J_mul_inl, Matrix.map_apply] at h2
  have h3 : σ ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) c) = 0 := by
    rw [h2]
    rcases c with j | j
    · rw [mul_J_inl, Matrix.transpose_apply, hc _ (by rintro ⟨_, _, h⟩; cases h) _ ⟨i, hi, rfl⟩, mul_zero]
    · have hj : j ∉ s := fun h => hcs ⟨j, h, rfl⟩
      rw [mul_J_inr, Matrix.transpose_apply]
      refine hc _ ?_ _ ⟨i, hi, rfl⟩
      rintro ⟨k, hk, h⟩
      exact hj (Sum.inl_injective h ▸ hk)
  rw [← hσ ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) c), h3, map_zero]
end Split
section Groups
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
theorem tri_mem (A : Ad E R) (hσ : ∀ x, A.σ (A.σ x) = x) (ε : ℤˣ) (g : GL (ι ⊕ ι) R) (h1 : g ∈ A.uSub ε ι)
    (h2 : g ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι))) : Tri s (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) where
  col := fun r hr i hi => (h2 r hr _ ⟨i, hi, rfl⟩).1
  row := row_of_stab A.σ hσ ε g h1 fun r hr c hc => (h2 r hr c hc).2
variable [Fintype ↥sᶜ] [DecidableEq ↥sᶜ]
def piG {F : Type} [CommRing F] (g : GL (ι ⊕ ι) F) (h : Tri s (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F))
    (h' : Tri s ((g⁻¹ : GL (ι ⊕ ι) F) : Matrix (ι ⊕ ι) (ι ⊕ ι) F)) : GL (↥sᶜ ⊕ ↥sᶜ) F where
  val := (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F).submatrix (emb s) (emb s)
  inv := ((g⁻¹ : GL (ι ⊕ ι) F) : Matrix (ι ⊕ ι) (ι ⊕ ι) F).submatrix (emb s) (emb s)
  val_inv := by rw [← h.sub_mul h', Units.mul_inv, Matrix.submatrix_one _ emb_inj]
  inv_val := by rw [← h'.sub_mul h, Units.inv_mul, Matrix.submatrix_one _ emb_inj]
variable (A : Ad E R) (ε : ℤˣ)
theorem q_stab (q : A.uQ ε s) : (q : A.U ε ι).1 ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι)) :=
  Subgroup.mem_subgroupOf.1 q.2
theorem q_tri (hσ : ∀ x, A.σ (A.σ x) = x) (q : A.uQ ε s) :
    Tri s ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
  tri_mem A hσ ε _ (q : A.U ε ι).2 (q_stab A ε q)
theorem q_tri' (hσ : ∀ x, A.σ (A.σ x) = x) (q : A.uQ ε s) :
    Tri s ((((q : A.U ε ι).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
  tri_mem A hσ ε _ ((A.uSub ε ι).inv_mem (q : A.U ε ι).2) ((stab R _).inv_mem (q_stab A ε q))
def piQ (hσ : ∀ x, A.σ (A.σ x) = x) : A.uQ ε s →* A.U ε ↥sᶜ where
  toFun q := ⟨piG (q : A.U ε ι).1 (q_tri A ε hσ q) (q_tri' A ε hσ q), by
    have h : ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι *
        ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ = Ad.J R ε ι := (q : A.U ε ι).2
    have h2 := (q_tri A ε hσ q).sub_unitary ε (b := ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ)
      ⟨fun r hr i hi => by rw [Matrix.map_apply, (q_tri A ε hσ q).col r hr i hi, map_zero],
        fun i hi c hc => by rw [Matrix.map_apply, (q_tri A ε hσ q).row i hi c hc, map_zero]⟩
    rw [h, sub_J] at h2
    exact h2.symm⟩
  map_one' := Subtype.ext (Units.ext (Matrix.submatrix_one _ emb_inj))
  map_mul' := fun a b => Subtype.ext (Units.ext ((q_tri A ε hσ a).sub_mul (q_tri A ε hσ b)))
def jG (F : Type) [CommRing F] : GL (↥sᶜ ⊕ ↥sᶜ) F →* GL (ι ⊕ ι) F := Units.map (jH (emb s) emb_inj)
theorem jG_val {F : Type} [CommRing F] (m : GL (↥sᶜ ⊕ ↥sᶜ) F) :
    (jG (s := s) F m : Matrix (ι ⊕ ι) (ι ⊕ ι) F) = jM (emb s) (m : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) F) := rfl
theorem jG_inv {F : Type} [CommRing F] (m : GL (↥sᶜ ⊕ ↥sᶜ) F) :
    (((jG (s := s) F m)⁻¹ : GL (ι ⊕ ι) F) : Matrix (ι ⊕ ι) (ι ⊕ ι) F) =
      jM (emb s) ((m⁻¹ : GL (↥sᶜ ⊕ ↥sᶜ) F) : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) F) := by
  rw [← map_inv]
  rfl
theorem jG_stab {F : Type} [CommRing F] (m : GL (↥sᶜ ⊕ ↥sᶜ) F) :
    jG (s := s) F m ∈ stab F (Sum.inl '' s : Set (ι ⊕ ι)) := by
  intro r hr c hc
  have hc' : c ∉ Set.range (emb s) := by
    obtain ⟨i, hi, rfl⟩ := hc
    exact fun h => (inl_mem_range i).1 h hi
  have hne : r ≠ c := fun h => hr (h ▸ hc)
  rw [jG_inv, jG_val, jM_off_right _ _ _ _ hc', jM_off_right _ _ _ _ hc', Matrix.one_apply_ne hne]
  exact ⟨rfl, rfl⟩
def jQ : A.U ε ↥sᶜ →* A.uQ ε s where
  toFun m := ⟨⟨jG R m.1, by
    have h : (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R)ᵀ * Ad.J R ε ↥sᶜ *
      (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R).map A.σ = Ad.J R ε ↥sᶜ := m.2
    change (jM (emb s) (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R))ᵀ * Ad.J R ε ι *
      (jM (emb s) (m.1 : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R)).map A.σ = Ad.J R ε ι
    rw [jM_transpose, jM_map]
    exact jM_unitary ε _ _ h⟩, Subgroup.mem_subgroupOf.2 (jG_stab m.1)⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (jG R)))
  map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul (jG R) a.1 b.1))
end Groups
section Blocks
variable {R : Type} [CommRing R]
theorem Tri.map {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {S : Type} [CommRing S] (f : R →+* S)
    {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : Tri s g) : Tri s (g.map f) :=
  ⟨fun r hr i hi => by rw [Matrix.map_apply, h.col r hr i hi, map_zero],
    fun i hi c hc => by rw [Matrix.map_apply, h.row i hi c hc, map_zero]⟩
end Blocks
section Parts
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
end Parts
section Main
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
section Cont
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ)
end Cont
variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ)
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {_fF : Fintype ↥sᶜ} {_fD : DecidableEq ↥sᶜ}
def c₀ (A : Ad E R) (ε : ℤˣ) (s : Set ι) : A.U ε ι → ℂ := fun g => (A.χ (bdet (Sum.inl '' s) g.1) : ℂ)
end Main
end GlobalTheory.CompanionTheory.RgEisLeviQUnit


