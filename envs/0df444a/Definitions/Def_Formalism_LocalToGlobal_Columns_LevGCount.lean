-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- name    : Formalism_LocalToGlobal_Columns_LevGCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:17.377802+00:00
-- url     : https://prove2.me/theorems/1690f8ae-1033-4d9d-ba38-ee18eb141080
-- title:
--   Lev GCount
-- statement:
--   Definitions and structural lemmas for Lev GCount, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_card_lt_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
namespace Formalism.L2.Col
section
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
theorem diagEmb_mem_uniUT {s : ℕ} (h : s ≤ n) {a : ℕ} {bl : List ℕ} {g : GL (Fin s) κ} (hg : g ∈ uniUT s κ a bl) :
    diagEmb κ h g ∈ uniUT n κ a bl := by
  have hv : ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = diagMat s n (g : Matrix (Fin s) (Fin s) κ) := rfl
  obtain ⟨h1, h2⟩ := hg
  show diagEmb κ h g ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i i = 1
  refine ⟨?_, fun i hi => ?_⟩
  · show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine a bl i.val)
    intro i j hij
    rw [hv]
    simp only [diagMat]
    split_ifs with hs
    · exact h1 (i := ⟨i.val, hs.1⟩) (j := ⟨j.val, hs.2⟩) hij
    · exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  · rw [hv]
    simp only [diagMat]
    split_ifs with hs
    · exact h2 ⟨i.val, hs.1⟩ hi
    · exact Matrix.one_apply_eq i
theorem diagEmb_mem_fixCol {s : ℕ} (h : s ≤ n) {c : ℕ} (hc : s ≤ c) (g : GL (Fin s) κ) : diagEmb κ h g ∈ fixCol n κ c := by
  show ∀ i j : Fin n, j.val = c → ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j
  intro i j hj
  show diagMat s n (g : Matrix (Fin s) (Fin s) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j
  simp only [diagMat]
  split_ifs with hs
  · exact absurd hs.2 (by omega)
  · rfl
end
section Uni
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
def uMat (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    Matrix (Fin n) (Fin n) κ :=
  fun i j => if i = j then 1 else if h : P i j then f ⟨(i, j), h⟩ else 0
theorem uMat_diag (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) (i : Fin n) :
    uMat P f i i = 1 := by
  simp [uMat]
theorem uMat_pos {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) {i j : Fin n}
    (hne : i ≠ j) (h : P i j) : uMat P f i j = f ⟨(i, j), h⟩ := by
  simp only [uMat, if_neg hne, dif_pos h]
theorem uMat_neg {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) {i j : Fin n}
    (hne : i ≠ j) (h : ¬ P i j) : uMat P f i j = 0 := by
  simp only [uMat, if_neg hne, dif_neg h]
theorem uMat_det {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : (uMat P f).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [uMat_diag]
  · intro i j hji
    have hne : i ≠ j := (ne_of_lt hji).symm
    exact uMat_neg f hne (fun h => absurd hji (not_lt.mpr (le_of_lt (hP i j h))))
def uGL {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : GL (Fin n) κ :=
  Matrix.GeneralLinearGroup.mk'' (uMat P f) (by rw [uMat_det hP]; exact isUnit_one)
theorem uGL_val {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : (uGL hP f : Matrix (Fin n) (Fin n) κ) = uMat P f := rfl
def uSet (κ : Type) [CommRing κ] (P : Fin n → Fin n → Prop) : Set (GL (Fin n) κ) :=
  {M | (∀ i, (M : Matrix (Fin n) (Fin n) κ) i i = 1) ∧ ∀ i j, i ≠ j → ¬ P i j → (M : Matrix (Fin n) (Fin n) κ) i j = 0}
def uEquiv {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j) :
    ↥(uSet κ P) ≃ ({p : Fin n × Fin n // P p.1 p.2} → κ) where
  toFun M p := (M.1 : Matrix (Fin n) (Fin n) κ) p.1.1 p.1.2
  invFun f := ⟨uGL hP f, fun i => uMat_diag P f i, fun _ _ hne h => uMat_neg f hne h⟩
  left_inv M := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    show uMat P (fun p => (M.1 : Matrix (Fin n) (Fin n) κ) p.1.1 p.1.2) i j = _
    by_cases hne : i = j
    · rw [hne, uMat_diag, M.2.1]
    · by_cases h : P i j
      · rw [uMat_pos _ hne h]
      · rw [uMat_neg _ hne h, M.2.2 i j hne h]
  right_inv f := by
    funext p
    show uMat P f p.1.1 p.1.2 = _
    rw [uMat_pos f (ne_of_lt (hP _ _ p.2)) p.2]
theorem card_uSet {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j) :
    Nat.card ↥(uSet κ P) = Nat.card κ ^ Nat.card {p : Fin n × Fin n // P p.1 p.2} := by
  rw [Nat.card_congr (uEquiv hP), Nat.card_fun]
theorem uniUT_full_eq : ((uniUT n κ n [] : Subgroup (GL (Fin n) κ)) : Set (GL (Fin n) κ)) = uSet κ (fun i j : Fin n => i < j) := by
  ext M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq]
  constructor
  · intro hM
    obtain ⟨h1, h2⟩ := hM
    refine ⟨fun i => h2 i i.2, fun i j hne hlt => ?_⟩
    have hji : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
    exact h1 ((fine_lt_right i.2).mpr hji)
  · rintro ⟨h1, h2⟩
    show M ∈ btG n κ (fine n []) ∧ ∀ i : Fin n, i.val < n → (M : Matrix (Fin n) (Fin n) κ) i i = 1
    refine ⟨?_, fun i _ => h1 i⟩
    show (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine n [] i.val)
    intro i j hji
    have hji' : j.val < i.val := (fine_lt_right i.2).mp hji
    exact h2 i j (fun e => by subst e; exact lt_irrefl _ hji') (fun h => absurd hji' (not_lt.mpr (le_of_lt h)))
theorem card_lt_pairs (k : ℕ) : Nat.card {p : Fin k × Fin k // p.1 < p.2} = k * (k - 1) / 2 := by
  have e : {p : Fin k × Fin k // p.1 < p.2} ≃ Σ j : Fin k, Fin j.val :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
      invFun := fun q => ⟨(⟨q.2.val, lt_trans q.2.2 q.1.2⟩, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h2 : ∑ j : Fin k, (j : ℕ) = ∑ i ∈ Finset.range k, i := Fin.sum_univ_eq_sum_range (fun i => i) k
  rw [h2, Finset.sum_range_id]
theorem card_HU (κ : Type) [CommRing κ] (k : ℕ) : Nat.card ↥(HU κ k) = Nat.card κ ^ (k * (k - 1) / 2) := by
  have h1 : Nat.card ↥(HU κ k) = Nat.card ↥(uSet κ (fun i j : Fin k => i < j)) := by
    rw [← uniUT_full_eq]; rfl
  rw [h1, card_uSet (fun _ _ h => h)]
  congr 1
  exact card_lt_pairs k
theorem uGL_mem_uniUT {a : ℕ} (bl : List ℕ) {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)]
    (hP : ∀ i j, P i j → i < j) (hPa : ∀ i j, P i j → j.val < a) (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    uGL hP f ∈ uniUT n κ a bl := by
  show uGL hP f ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → (uGL hP f : Matrix (Fin n) (Fin n) κ) i i = 1
  refine ⟨?_, fun i _ => by rw [uGL_val]; exact uMat_diag P f i⟩
  show (uGL hP f : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine a bl i.val)
  intro i j hij
  rw [uGL_val]
  have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
  refine uMat_neg f hne (fun hp => ?_)
  have h1 := hP i j hp
  have h2 := hPa i j hp
  have h3 : i.val < a := lt_trans (show i.val < j.val from h1) h2
  have hij' := (fine_lt_right (bl := bl) h3).mp hij
  exact absurd hij' (not_lt.mpr (le_of_lt h1))
theorem detChar_uGL (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)]
    (hP : ∀ i j, P i j → i < j) (hPa : ∀ i j, P i j → j.val < a) (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    detChar χ n a bl ⟨uGL hP f, uniUT_le_blockUT n κ a bl (uGL_mem_uniUT bl hP hPa f)⟩ = 1 := by
  unfold detChar
  rw [MonoidHom.finset_prod_apply]
  apply Finset.prod_eq_one
  intro s _
  rw [MonoidHom.comp_apply]
  have hb : blkDet n κ (coarse a bl) (s + 1) ⟨uGL hP f, uniUT_le_blockUT n κ a bl (uGL_mem_uniUT bl hP hPa f)⟩ = 1 := by
    apply Units.ext
    change Matrix.det ((uGL hP f : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a bl i.val) (s + 1)) = (1 : κ)
    have hI : (uGL hP f : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a bl i.val) (s + 1) = 1 := by
      ext i j
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply, uGL_val, Matrix.one_apply]
      split_ifs with h
      · rw [h]; exact uMat_diag P f _
      · refine uMat_neg f (fun e => h (Subtype.ext e)) (fun hp => ?_)
        have h1 := hPa _ _ hp
        have h3 : coarse a bl (j : Fin n).val = 0 := by simp only [coarse, blkIdx, if_pos h1]
        have h4 : coarse a bl (j : Fin n).val = s + 1 := j.2
        omega
    rw [hI, Matrix.det_one]
  rw [hb, map_one]
theorem lamGen_val_of_det (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (S : Finset ℕ) (M : ↥(uniUT n κ a bl))
    (hd : detChar χ n a bl ⟨M.1, uniUT_le_blockUT n κ a bl M.2⟩ = 1) :
    ((lamGen ψ χ n a bl S M : Kˣ) : K) = ψ (supSum a S (M.1 : Matrix (Fin n) (Fin n) κ)) := by
  unfold lamGen
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply]
  have hi : Subgroup.inclusion (uniUT_le_blockUT n κ a bl) M = ⟨M.1, uniUT_le_blockUT n κ a bl M.2⟩ := rfl
  rw [hi, hd, mul_one]
  rfl
theorem supSum_elem {a : ℕ} (S : Finset ℕ) (i₀ j₀ : Fin n) (h₀ : i₀.val + 1 = j₀.val) (ha : j₀.val < a) (hS : i₀.val ∈ S) (c : κ) :
    supSum a S (uMat (fun i j : Fin n => i = i₀ ∧ j = j₀) (fun _ => c)) = c := by
  unfold supSum
  rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
  · rw [if_pos ⟨h₀, ha, hS⟩, uMat_pos _ (fun e => by rw [e] at h₀; omega) ⟨rfl, rfl⟩]
  · intro j _ hj
    split_ifs with h
    · exact uMat_neg _ (fun e => by rw [e] at h; exact absurd h.1 (by omega)) (fun hp => hj hp.2)
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · exact uMat_neg _ (fun e => by rw [e] at h; exact absurd h.1 (by omega)) (fun hp => hi hp.1)
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h
theorem lamGen_elem (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (S : Finset ℕ) (i₀ j₀ : Fin n)
    (h₀ : i₀.val + 1 = j₀.val) (ha : j₀.val < a) (hS : i₀.val ∈ S) (c : κ) :
    ∃ M : ↥(uniUT n κ a bl), ((lamGen ψ χ n a bl S M : Kˣ) : K) = ψ c := by
  have hP : ∀ i j : Fin n, (i = i₀ ∧ j = j₀) → i < j := by
    rintro i j ⟨rfl, rfl⟩; show i.val < j.val; omega
  have hPa : ∀ i j : Fin n, (i = i₀ ∧ j = j₀) → j.val < a := by
    rintro i j ⟨rfl, rfl⟩; exact ha
  refine ⟨⟨uGL hP (fun _ => c), uGL_mem_uniUT bl hP hPa _⟩, ?_⟩
  rw [lamGen_val_of_det ψ χ bl S ⟨uGL hP (fun _ => c), uGL_mem_uniUT bl hP hPa _⟩ (detChar_uGL χ bl hP hPa _)]
  congr 1
  exact supSum_elem S i₀ j₀ h₀ ha hS c
theorem lamGen_ne_one {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) {S : Finset ℕ} {i₀ : ℕ}
    (hS : i₀ ∈ S) (ha : i₀ + 1 < a) (han : a ≤ n) : lamGen ψ χ n a bl S ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ : ∃ c, ψ c ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hψ (DFunLike.ext _ _ fun x => (hcon x).trans (AddChar.one_apply x).symm)
  obtain ⟨M, hM⟩ := lamGen_elem ψ χ bl S (⟨i₀, by omega⟩ : Fin n) (⟨i₀ + 1, by omega⟩ : Fin n) rfl ha hS c
  rw [h, MonoidHom.one_apply, Units.val_one] at hM
  exact hc hM.symm
theorem lamX_ne_one {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {k : ℕ} (m t j : ℕ) (hk : 2 ≤ k) (hn : k + j ≤ n) :
    lamX ψ χ n k m t j ≠ 1 := by
  unfold lamX
  refine lamGen_ne_one hψ χ _ (i₀ := 0) ?_ (by omega) hn
  unfold SX
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Or.inl (by omega)⟩
end Uni
section Diag
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
def dGL (i₀ : Fin n) (u : κˣ) : GL (Fin n) κ :=
  Units.map (Matrix.diagonalRingHom (Fin n) κ).toMonoidHom (MulEquiv.piUnits.symm (Function.update 1 i₀ u))
theorem dGL_val (i₀ : Fin n) (u : κˣ) :
    (dGL i₀ u : Matrix (Fin n) (Fin n) κ) = Matrix.diagonal fun i => ((Function.update (1 : Fin n → κˣ) i₀ u i : κˣ) : κ) := rfl
theorem dGL_mem_btG (β : ℕ → ℕ) (i₀ : Fin n) (u : κˣ) : dGL i₀ u ∈ btG n κ β := by
  show (dGL i₀ u : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => β i.val)
  rw [dGL_val]
  exact Matrix.blockTriangular_diagonal _
theorem HK_conj_diagEmb {r : ℕ} (h : r ≤ n) {bl : List ℕ} (g : GL (Fin r) κ) {M : GL (Fin n) κ} (hM : M ∈ HK n κ r bl) :
    diagEmb κ h g * M * (diagEmb κ h g)⁻¹ ∈ HK n κ r bl := by
  have hD : diagEmb κ h g ∈ blockUT n κ r bl := by
    show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r bl i.val)
    intro i j hij
    show diagMat r n (g : Matrix (Fin r) (Fin r) κ) i j = 0
    simp only [diagMat]
    have hi : ¬ i.val < r := by
      intro hi
      have h0 : coarse r bl i.val = 0 := by simp only [coarse, blkIdx, if_pos hi]
      have hij' : coarse r bl j.val < coarse r bl i.val := hij
      omega
    rw [dif_neg (fun hc => hi hc.1)]
    exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  unfold HK at hM ⊢
  rw [Subgroup.mem_map] at hM ⊢
  obtain ⟨M', hM', hMe⟩ := hM
  refine ⟨⟨diagEmb κ h g, hD⟩ * M' * ⟨diagEmb κ h g, hD⟩⁻¹, ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hM' ⊢
    rw [map_mul, map_mul, hM', mul_one, ← map_mul, mul_inv_cancel, map_one]
  · rw [← hMe, map_mul, map_mul, map_inv]
    rfl
end Diag
instance finite_res (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ w.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
instance finite_GLs (E : Type) [Field E] [NumberField E] (SG : Finset (HeightOneSpectrum (𝓞 E))) (n : ℕ) : Finite (GLs E SG n) :=
  Pi.finite
example : Nat.card ↥(HU (ZMod 3) 2) = 3 := by rw [card_HU]; simp
example : Nat.card ↥(HU (ZMod 5) 4) = 5 ^ 6 := by rw [card_HU]; simp
theorem stdAddChar_ne_one : (ZMod.stdAddChar (N := 3)) ≠ 1 := by
  have hp := ZMod.isPrimitive_stdAddChar 3
  have h := hp (a := 1) (by decide)
  rwa [AddChar.mulShift_one] at h
example : lamX (ZMod.stdAddChar (N := 3)) (fun _ => 1) 8 3 2 4 1 ≠ 1 :=
  lamX_ne_one stdAddChar_ne_one _ 2 4 1 (by norm_num) (by norm_num)
section DiagChar
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
end DiagChar
section Sym
variable {n : ℕ} {κ : Type} [CommRing κ]
end Sym
section More
variable {κ : Type} [CommRing κ] {K : Type} [Field K]
end More
section Res
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
end Res
section ParId
variable {n : ℕ} {κ : Type} [CommRing κ]
end ParId
end Formalism.L2.Col


