-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:44.721087+00:00
-- url     : https://prove2.me/theorems/5bfd78e3-8719-4337-a560-e46590d9a8a1
-- title:
--   Exists Eq Transpose Mul Map Of Idempotent
-- statement:
--   Definitions and structural lemmas for Exists Eq Transpose Mul Map Of Idempotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEqTransposeMulMapOfIdempotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BinaryFormUniversal
import Theorems.Thm_GlobalTheory_BinaryFormUniversal_binary_form_universal
import Theorems.Thm_GlobalTheory_QuadraticEtale_exists_add_eq_one
import Theorems.Thm_GlobalTheory_QuadraticEtale_isIntegral_of_involution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix IsLocalRing
namespace GlobalTheory.UnramifiedHermitian
section Diagonal
variable {R : Type*} [CommRing R] (c : R →+* R) {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem exists_shear (G : Matrix ι ι R) (p : ι) (τ : ι → R) (hτ : τ p = 0) :
    ∃ P : Matrix ι ι R, IsUnit P.det ∧ ∀ x y, (Pᵀ * G * P.map c) x y
      = G x y + τ x * G p y + c (τ y) * G x p + τ x * c (τ y) * G p p := by
  refine ⟨1 + vecMulVec (Pi.single p 1) τ, ?_, fun x y => ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := 1 - vecMulVec (Pi.single p 1) τ) ?_
    rw [mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_vecMulVec]
    simp [hτ]
  · simp only [Matrix.mul_apply, transpose_apply, map_apply, Matrix.add_apply, vecMulVec_apply,
      Matrix.one_apply, Pi.single_apply, map_add, map_mul, apply_ite c, map_one, map_zero,
      add_mul, mul_add, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
omit [DecidableEq ι] in

theorem hermitian_congr (hc : ∀ x, c (c x) = x) {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a)
    (P : Matrix ι ι R) (a b : ι) : c ((Pᵀ * G * P.map c) a b) = (Pᵀ * G * P.map c) b a := by
  simp only [Matrix.mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hG,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
theorem det_congr (G P : Matrix ι ι R) :
    (Pᵀ * G * P.map c).det = P.det * c P.det * G.det := by
  rw [det_mul, det_mul, det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  ring
omit [DecidableEq ι] in

theorem congr_mul (G P Q : Matrix ι ι R) :
    (P * Q)ᵀ * G * (P * Q).map c = Qᵀ * (Pᵀ * G * P.map c) * Q.map c := by
  rw [transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
theorem exists_congr_symm {G H P : Matrix ι ι R} (hP : IsUnit P.det)
    (h : Pᵀ * G * P.map c = H) : ∃ Q : Matrix ι ι R, IsUnit Q.det ∧ G = Qᵀ * H * Q.map c := by
  refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det P hP, ?_⟩
  rw [← h, ← congr_mul, Matrix.mul_nonsing_inv P hP]
  simp
theorem mem_of_fixed_of_not_isUnit (hc : ∀ x, c (c x) = x)
    (hloc : ∀ x, c x = x → IsUnit x ∨ IsUnit (1 - x)) {x : R} (hx : c x = x) (hu : ¬ IsUnit x)
    (n : Ideal R) [hn : n.IsMaximal] : x ∈ n := by
  by_contra hxn
  obtain ⟨r, y, hy, hry⟩ := hn.exists_inv hxn
  have hfix : c (x * (r + c r - x * (r * c r))) = x * (r + c r - x * (r * c r)) := by
    simp only [map_mul, map_sub, map_add, hc, hx]; ring
  rcases hloc _ hfix with h | h
  · exact hu (isUnit_of_mul_isUnit_left h)
  · refine hn.ne_top (n.eq_top_of_isUnit_mem ?_ h)
    have hy' : y = 1 - r * x := by linear_combination hry
    have := n.mul_mem_right (c y) hy
    convert this using 1
    rw [hy']
    simp only [map_mul, map_sub, map_one, hx]
    ring
theorem mem_of_forall_trace_mem (hc : ∀ x, c (c x) = x) (hw : ∃ w, w + c w = 1)
    (n : Ideal R) [hn : n.IsMaximal] {g : R} (hg : ∀ t, t * g + c (t * g) ∈ n) : g ∈ n := by
  obtain ⟨w, hw⟩ := hw
  by_contra hgn
  have h1 : g * c g ∈ n := by
    convert hg (w * c g) using 1
    simp only [map_mul, hc]
    linear_combination (-(g * c g)) * hw
  have h2 : c g ∈ n := (hn.isPrime.mem_or_mem h1).resolve_left hgn
  have h3 := n.sub_mem (hg 1) h2
  apply hgn
  simpa using h3
theorem exists_congr_insert (hc : ∀ x, c (c x) = x)
    (hloc : ∀ x, c x = x → IsUnit x ∨ IsUnit (1 - x)) (hw : ∃ w, w + c w = 1)
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det)
    (s : Finset ι) (hs : ∀ a ∈ s, ∀ b, b ≠ a → G a b = 0) (hne : ∃ a, a ∉ s) :
    ∃ p ∉ s, ∃ P : Matrix ι ι R, IsUnit P.det ∧
      ∀ a ∈ insert p s, ∀ b, b ≠ a → (Pᵀ * G * P.map c) a b = 0 := by

  have clear : ∀ {G : Matrix ι ι R}, (∀ a b, c (G a b) = G b a) →
      (∀ a ∈ s, ∀ b, b ≠ a → G a b = 0) → ∀ p ∉ s, IsUnit (G p p) →
      ∃ P : Matrix ι ι R, IsUnit P.det ∧
        ∀ a ∈ insert p s, ∀ b, b ≠ a → (Pᵀ * G * P.map c) a b = 0 := by
    intro G hG hs p hp hu
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have hv' : c v * G p p = 1 := by
      have := congrArg c hv
      rwa [map_mul, hG, map_one] at this
    obtain ⟨P, hP, h⟩ := exists_shear c G p (fun x => if x = p then 0 else -(v * G x p)) (by simp)
    refine ⟨P, hP, fun a ha b hb => ?_⟩
    rw [h]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · simp only [if_true, if_neg hb, map_neg, map_mul, hG]
      linear_combination (-G a b) * hv'
    · have hap : p ≠ a := fun h => hp (h ▸ ha)
      simp [hs a ha b hb, hs a ha p hap]
  rcases subsingleton_or_nontrivial R with hR | hR
  · obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, 1, by simp, fun _ _ _ _ => Subsingleton.elim _ _⟩
  by_cases hd : ∃ p ∉ s, IsUnit (G p p)
  · obtain ⟨p, hp, hu⟩ := hd
    exact ⟨p, hp, clear hG hs p hp hu⟩
  push Not at hd
  obtain ⟨n, hn⟩ := Ideal.exists_maximal R
  have hdn : ∀ p ∉ s, G p p ∈ n := fun p hp =>
    mem_of_fixed_of_not_isUnit c hc hloc (hG p p) (hd p hp) n
  by_cases hx : ∃ p ∉ s, ∃ q ∉ s, p ≠ q ∧ ∃ t,
      IsUnit (G p p + t * G q p + c t * G p q + t * c t * G q q)
  · obtain ⟨p, hp, q, hq, hpq, t, hu⟩ := hx
    obtain ⟨P, hP, h⟩ := exists_shear c G q (Pi.single p t) (by simp [hpq])
    obtain ⟨Q, hQ, h'⟩ := clear (hermitian_congr c hc hG P) (fun a ha b hb => by
      have hap : p ≠ a := fun h => hp (h ▸ ha)
      have haq : q ≠ a := fun h => hq (h ▸ ha)
      rw [h]
      simp [hs a ha b hb, hs a ha q haq, hap.symm]) p hp (by rw [h]; simpa using hu)
    exact ⟨p, hp, P * Q, by rw [det_mul]; exact hP.mul hQ, by rwa [congr_mul]⟩
  exfalso
  push Not at hx
  obtain ⟨q, hq⟩ := hne
  have hrow : ∀ p, G q p ∈ n := by
    intro p
    by_cases hp : p ∈ s
    · have hqp : q ≠ p := fun h => hq (h ▸ hp)
      rw [← hG, hs p hp q hqp, map_zero]
      exact n.zero_mem
    by_cases hpq : p = q
    · rw [hpq]; exact hdn q hq
    refine mem_of_forall_trace_mem c hc hw n fun t => ?_
    have h1 := mem_of_fixed_of_not_isUnit c hc hloc (by
      simp only [map_add, map_mul, hc, hG]; ring) (hx p hp q hq hpq t) n
    have h2 := n.sub_mem (n.sub_mem h1 (hdn p hp)) (n.mul_mem_left (t * c t) (hdn q hq))
    convert h2 using 1
    rw [map_mul, hG]
    ring
  refine hn.ne_top (n.eq_top_of_isUnit_mem ?_ hdet)
  rw [Matrix.det_apply']
  refine n.sum_mem fun σ _ => n.mul_mem_left _ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (σ.symm q)), Equiv.apply_symm_apply]
  exact n.mul_mem_right _ (hrow _)
theorem exists_eq_diagonal_of_isUnit_or (hc : ∀ x, c (c x) = x)
    (hloc : ∀ x, c x = x → IsUnit x ∨ IsUnit (1 - x)) (hw : ∃ w, w + c w = 1)
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) :
    ∃ (P : Matrix ι ι R) (d : ι → R), IsUnit P.det ∧ (∀ a, IsUnit (d a)) ∧ (∀ a, c (d a) = d a) ∧
      G = Pᵀ * diagonal d * P.map c := by
  have hdet' : ∀ P : Matrix ι ι R, IsUnit P.det → IsUnit (Pᵀ * G * P.map c).det := fun P hP => by
    rw [det_congr]; exact (hP.mul (hP.map c)).mul hdet
  have key : ∀ k ≤ Fintype.card ι, ∃ s : Finset ι, s.card = k ∧ ∃ P : Matrix ι ι R, IsUnit P.det ∧
      ∀ a ∈ s, ∀ b, b ≠ a → (Pᵀ * G * P.map c) a b = 0 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨∅, rfl, 1, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨s, hsk, P, hP, h⟩ := ih (by omega)
      obtain ⟨p, hp, Q, hQ, h'⟩ := exists_congr_insert c hc hloc hw (hermitian_congr c hc hG P)
        (hdet' P hP) s h (by
          by_contra hcon
          push Not at hcon
          have := Finset.eq_univ_of_forall hcon
          rw [this, Finset.card_univ] at hsk
          omega)
      exact ⟨insert p s, by rw [Finset.card_insert_of_notMem hp, hsk], P * Q,
        by rw [det_mul]; exact hP.mul hQ, by rwa [congr_mul]⟩
  obtain ⟨s, hs, P, hP, h⟩ := key _ le_rfl
  rw [Finset.card_eq_iff_eq_univ] at hs
  subst hs
  have hdiag : Pᵀ * G * P.map c = diagonal fun a => (Pᵀ * G * P.map c) a a := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [diagonal_apply_ne _ hab, h a (Finset.mem_univ a) b (Ne.symm hab)]
  obtain ⟨Q, hQ, hGQ⟩ := exists_congr_symm c hP hdiag
  refine ⟨Q, _, hQ, fun a => ?_, fun a => hermitian_congr c hc hG P a a, hGQ⟩
  have := hdet' P hP
  rw [hdiag, det_diagonal] at this
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => (Pᵀ * G * P.map c) i i)
    (Finset.mem_univ a)) this
theorem exists_eq_transpose_mul_map_of_isUnit_or (hc : ∀ x, c (c x) = x)
    (hloc : ∀ x, c x = x → IsUnit x ∨ IsUnit (1 - x)) (hw : ∃ w, w + c w = 1)
    (hnorm : ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u)
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) :
    ∃ P : Matrix ι ι R, IsUnit P.det ∧ G = Pᵀ * P.map c := by
  obtain ⟨P, d, hP, hd, hcd, h⟩ := exists_eq_diagonal_of_isUnit_or c hc hloc hw hG hdet
  choose x hx using fun a => hnorm (d a) (hcd a) (hd a)
  have hGe : G = (diagonal x * P)ᵀ * (diagonal x * P).map c := by
    have := congr_mul c 1 (diagonal x) P
    rw [Matrix.mul_one, Matrix.mul_one, diagonal_transpose, diagonal_map (map_zero c),
      diagonal_mul_diagonal] at this
    rw [this, h]
    simp only [hx]
  refine ⟨diagonal x * P, ?_, hGe⟩
  rw [hGe, det_mul, det_transpose] at hdet
  exact isUnit_of_mul_isUnit_left hdet
end Diagonal
section Base
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R] (c : R →+* R)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem isUnit_or_of_fixed [IsLocalRing R₀]
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) (x : R) (hx : c x = x) :
    IsUnit x ∨ IsUnit (1 - x) := by
  obtain ⟨r, rfl⟩ := hfix x hx
  refine (isUnit_or_isUnit_one_sub_self r).imp (fun h => h.map _) fun h => ?_
  simpa using h.map (algebraMap R₀ R)
theorem exists_eq_transpose_mul_map [IsLocalRing R₀] (hc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) (hw : ∃ w, w + c w = 1)
    (hnorm : ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u)
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) :
    ∃ P : Matrix ι ι R, IsUnit P.det ∧ G = Pᵀ * P.map c :=
  exists_eq_transpose_mul_map_of_isUnit_or c hc (isUnit_or_of_fixed c hfix) hw hnorm hG hdet
end Base
section Split
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] (c : R →+* R)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
end Split
section Norm
open Polynomial
theorem exists_binary_eq_of_finite {k : Type*} [Field k] [Finite k] {a n : k}
    (hD : a ^ 2 - 4 * n ≠ 0) (u : k) : ∃ r s, r ^ 2 + a * r * s + n * s ^ 2 = u := by
  first
  | exact @_root_.GlobalTheory.BinaryFormUniversal.binary_form_universal
  | exact _root_.GlobalTheory.BinaryFormUniversal.binary_form_universal
  | (apply _root_.GlobalTheory.BinaryFormUniversal.binary_form_universal <;> assumption)
  | (intros; apply _root_.GlobalTheory.BinaryFormUniversal.binary_form_universal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BinaryFormUniversal.binary_form_universal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BinaryFormUniversal.binary_form_universal ..)
theorem exists_add_mul_sq_eq {R₀ : Type*} [CommRing R₀] (I : Ideal R₀) [HenselianRing R₀ I]
    (n : R₀) {e : R₀} (he : e ∈ I) : ∃ t, t + n * t ^ 2 = e := by
  obtain ⟨z, hz, hz1⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - X - C (n * e))
    (by monicity!) 1 (by simpa using I.mul_mem_left n he) (by
      simp only [derivative_sub, derivative_X_pow, derivative_X, derivative_C]
      norm_num)
  have hu : IsUnit z := by
    simpa using Ideal.mem_jacobson_bot.1 (HenselianRing.jac hz1) 1
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at hz
  refine ⟨e * y, ?_⟩
  linear_combination (-(e * y ^ 2)) * hz + e * (z * y + 1 - y) * hy
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R] [IsLocalRing R₀]
  [HenselianRing R₀ (maximalIdeal R₀)] [Finite (ResidueField R₀)]
theorem exists_norm_eq_of_henselian (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) (hgal : ∃ ω, IsUnit (ω - c ω))
    {u : R} (hcu : c u = u) (hu : IsUnit u) : ∃ x, x * c x = u := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  haveI := QuadraticEtale.isIntegral_of_involution c hc hfix
  have hunit : ∀ r : R₀, IsUnit (algebraMap R₀ R r) → IsUnit r := by
    intro r hr
    by_contra h
    obtain ⟨m, hm⟩ := Ideal.exists_maximal R
    exact hm.ne_top (m.eq_top_of_isUnit_mem (QuadraticEtale.algebraMap_mem_of_isMaximal m h) hr)
  obtain ⟨w, hw⟩ := QuadraticEtale.exists_add_eq_one c hc hgal
  obtain ⟨ω, hω⟩ := hgal
  obtain ⟨a, ha⟩ := hfix (ω + c ω) (by rw [map_add, hc, add_comm])
  obtain ⟨n, hn⟩ := hfix (ω * c ω) (by rw [map_mul, hc, mul_comm])
  obtain ⟨n', hn'⟩ := hfix (w * c w) (by rw [map_mul, hc, mul_comm])
  obtain ⟨u, rfl⟩ := hfix u hcu
  have hu' := hunit u hu
  have hD : IsUnit (a ^ 2 - 4 * n) := by
    refine hunit _ ?_
    convert hω.pow 2 using 1
    simp only [map_sub, map_mul, map_pow, map_ofNat, ha, hn]
    ring
  obtain ⟨r, s, hrs⟩ := exists_binary_eq_of_finite (a := residue R₀ a) (n := residue R₀ n)
    (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using (hD.map (residue R₀)).ne_zero)
    (residue R₀ u)
  obtain ⟨r, rfl⟩ := residue_surjective r
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hN : residue R₀ (r ^ 2 + a * r * s + n * s ^ 2) = residue R₀ u := by
    simpa only [map_add, map_mul, map_pow] using hrs
  have hNu : IsUnit (r ^ 2 + a * r * s + n * s ^ 2) := by
    rw [← residue_ne_zero_iff_isUnit, hN]
    exact (hu'.map _).ne_zero
  obtain ⟨v, hv⟩ := hNu.exists_right_inv
  have he : u * v - 1 ∈ maximalIdeal R₀ := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hN, ← map_mul, hv, sub_self]
  obtain ⟨t, ht⟩ := exists_add_mul_sq_eq (maximalIdeal R₀) n' he
  have hfinal : (r ^ 2 + a * r * s + n * s ^ 2) * (1 + (t + n' * t ^ 2)) = u := by
    rw [ht]; linear_combination u * hv
  refine ⟨(algebraMap R₀ R r + algebraMap R₀ R s * ω) * (1 + algebraMap R₀ R t * w), ?_⟩
  rw [← hfinal]
  simp only [map_add, map_mul, map_pow, map_one, hbase, ha, hn, hn']
  linear_combination (algebraMap R₀ R r + algebraMap R₀ R s * ω)
    * (algebraMap R₀ R r + algebraMap R₀ R s * c ω) * algebraMap R₀ R t * hw
theorem exists_eq_transpose_mul_map_of_henselian (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) (hgal : ∃ ω, IsUnit (ω - c ω))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι R} (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) :
    ∃ P : Matrix ι ι R, IsUnit P.det ∧ G = Pᵀ * P.map c :=
  exists_eq_transpose_mul_map (R₀ := R₀) c hc hfix (QuadraticEtale.exists_add_eq_one c hc hgal)
    (fun _ h1 h2 => exists_norm_eq_of_henselian (R₀ := R₀) c hc hbase hfix hgal h1 h2) hG hdet
variable [Module.Free R₀ R] [Algebra.FormallyUnramified R₀ R]
end Norm
example : ∃ P : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra ℤ_[2] (-1) 1), IsUnit P.det ∧
    !![0, 1; 1, 0] = Pᵀ * P.map (starRingEnd _) := by
  haveI : Finite (ResidueField ℤ_[2]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := 2)).symm.toEquiv
  refine exists_eq_transpose_mul_map_of_henselian (R₀ := ℤ_[2]) _ star_star (fun r => ?_)
    (fun x hx => ⟨x.re, ?_⟩) ⟨⟨0, 1⟩, ?_⟩ ?_ (by simp [Matrix.det_fin_two])
  · ext <;> simp [starRingEnd_apply]
  · have h := congrArg QuadraticAlgebra.re hx
    have h' : x.im = 0 := by simpa [starRingEnd_apply] using h
    ext <;> simp [h']
  · have h3 : IsUnit (3 : ℤ_[2]) := by
      rw [PadicInt.isUnit_iff]
      exact_mod_cast PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 3) |>.2 (by norm_num)
    refine isUnit_of_mul_isUnit_left (y := ⟨1, -2⟩) ?_
    convert h3.map (algebraMap ℤ_[2] (QuadraticAlgebra ℤ_[2] (-1) 1)) using 1
    ext <;> simp [starRingEnd_apply] <;> norm_num
  · intro a b
    fin_cases a <;> fin_cases b <;> simp
end GlobalTheory.UnramifiedHermitian


