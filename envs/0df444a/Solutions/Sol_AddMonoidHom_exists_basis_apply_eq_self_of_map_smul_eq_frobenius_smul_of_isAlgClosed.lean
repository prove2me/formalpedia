-- Prove2me | solution 1 for AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7b421fac-30b5-5c38-9b9a-602a2525c6ee

import Mathlib
import Theorems.Thm_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed

set_option autoImplicit false

noncomputable section

universe u v

namespace P2mKcWittLang

open Function

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k]

section ModP

variable [IsAlgClosed k] [CharP k p] {n : ℕ}

def frobMulVec (B : Matrix (Fin n) (Fin n) k) : (Fin n → k) →+ (Fin n → k) where
  toFun x := B.mulVec fun i => x i ^ p
  map_zero' := by
    have h : (fun i : Fin n => (0 : Fin n → k) i ^ p) = 0 := by
      funext i; simp [zero_pow hp.out.ne_zero]
    rw [h, Matrix.mulVec_zero]
  map_add' x y := by
    haveI : ExpChar k p := ExpChar.prime hp.out
    have h : (fun i : Fin n => (x + y) i ^ p) = (fun i => x i ^ p) + fun i => y i ^ p := by
      funext i; simp [add_pow_expChar]
    rw [h, Matrix.mulVec_add]

omit [IsAlgClosed k] in
@[scoped simp] theorem frobMulVec_apply (B : Matrix (Fin n) (Fin n) k) (x : Fin n → k) :
    frobMulVec (p := p) B x = B.mulVec fun i => x i ^ p := rfl

theorem exists_matrix_mul_frob_eq (B : Matrix (Fin n) (Fin n) k) (hB : IsUnit B) :
    ∃ Q : Matrix (Fin n) (Fin n) k, IsUnit Q ∧ B * Q.map (frobenius k p) = Q := by
  classical
  let φ := frobMulVec (p := p) B
  have hφ : ∀ (c : k) (x : Fin n → k), φ (c • x) = c ^ p • φ x := by
    intro c x
    simp only [φ, frobMulVec_apply]
    have h : (fun i : Fin n => (c • x) i ^ p) = c ^ p • fun i => x i ^ p := by
      funext i; simp [mul_pow]
    rw [h, Matrix.mulVec_smul]
  have hinj : Function.Injective φ := by
    intro x y hxy
    simp only [φ, frobMulVec_apply] at hxy
    have h1 := (Matrix.mulVec_injective_iff_isUnit.mpr hB) hxy
    funext i
    have h2 := congrFun h1 i
    exact frobenius_inj k p h2
  obtain ⟨b, hb⟩ :=
    AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed p k
      (Fin n → k) φ hφ hinj

  let e : Fin n ≃ Fin (Module.finrank k (Fin n → k)) := finCongr (Module.finrank_fin_fun (R := k) (n := n)).symm
  let Q : Matrix (Fin n) (Fin n) k := fun i j => b (e j) i
  have hcol : ∀ j, (fun i => Q i j) = b (e j) := fun j => rfl
  refine ⟨Q, ?_, ?_⟩
  ·
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have hli : LinearIndependent k (fun j => (b (e j) : Fin n → k)) :=
      b.linearIndependent.comp e e.injective
    exact hli
  · ext i j
    have hfix := congrFun (hb (e j)) i
    simp only [φ, frobMulVec_apply] at hfix
    rw [Matrix.mul_apply]
    rw [Matrix.mulVec, dotProduct] at hfix
    simpa [Matrix.map_apply, frobenius_def] using hfix

theorem exists_matrix_sub_mul_frob_eq (B : Matrix (Fin n) (Fin n) k) (hB : IsUnit B)
    (E : Matrix (Fin n) (Fin n) k) :
    ∃ X : Matrix (Fin n) (Fin n) k, X - B * X.map (frobenius k p) = E := by
  classical
  obtain ⟨Q, hQ, hBQ⟩ := exists_matrix_mul_frob_eq (p := p) B hB

  obtain ⟨Qi, hQi1⟩ := hQ.exists_left_inv
  let E' : Matrix (Fin n) (Fin n) k := Qi * E
  have has : ∀ c : k, ∃ y : k, y - y ^ p = c := by
    intro c

    have hdeg : (Polynomial.X ^ p - Polynomial.X + Polynomial.C c : Polynomial k).degree ≠ 0 := by
      have hne : (Polynomial.X ^ p - Polynomial.X : Polynomial k) ≠ 0 :=
        FiniteField.X_pow_card_sub_X_ne_zero k hp.out.one_lt
      have hnat : (Polynomial.X ^ p - Polynomial.X : Polynomial k).natDegree = p :=
        FiniteField.X_pow_card_sub_X_natDegree_eq k hp.out.one_lt
      have hdegX : (Polynomial.X ^ p - Polynomial.X : Polynomial k).degree = p := by
        rw [Polynomial.degree_eq_natDegree hne, hnat]
      have hlt : (Polynomial.C c : Polynomial k).degree <
          (Polynomial.X ^ p - Polynomial.X : Polynomial k).degree := by
        rw [hdegX]
        exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hp.out.pos)
      rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, hdegX]
      exact_mod_cast hp.out.ne_zero
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ?_⟩
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hy
    linear_combination (-1 : k) * hy
  choose y hy using has
  let Y : Matrix (Fin n) (Fin n) k := fun i j => y (E' i j)
  have hY : Y - Y.map (frobenius k p) = E' := by
    ext i j
    simp [Y, Matrix.map_apply, frobenius_def, hy]
  refine ⟨Q * Y, ?_⟩
  have hmap : (Q * Y).map (frobenius k p) = Q.map (frobenius k p) * Y.map (frobenius k p) :=
    Matrix.map_mul
  rw [hmap, ← Matrix.mul_assoc, hBQ, ← Matrix.mul_sub, hY]
  show Q * (Qi * E) = E
  rw [← Matrix.mul_assoc]

  have hQQi : Q * Qi = 1 := mul_eq_one_comm.mp hQi1
  rw [hQQi, Matrix.one_mul]

end ModP

section Witt

variable [CharP k p] {n : ℕ}

abbrev frobM (P : Matrix (Fin n) (Fin n) (WittVector p k)) : Matrix (Fin n) (Fin n) (WittVector p k) :=
  P.map WittVector.frobenius

abbrev truncM (m : ℕ) (P : Matrix (Fin n) (Fin n) (WittVector p k)) :
    Matrix (Fin n) (Fin n) (TruncatedWittVector p m k) :=
  P.map (WittVector.truncate m)

abbrev resM (P : Matrix (Fin n) (Fin n) (WittVector p k)) : Matrix (Fin n) (Fin n) k :=
  P.map WittVector.constantCoeff

omit [CharP k p] in
theorem truncate_eq_iff {m : ℕ} (x y : WittVector p k) :
    WittVector.truncate m x = WittVector.truncate m y ↔ ∀ i < m, x.coeff i = y.coeff i := by
  constructor
  · intro h i hi
    have := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
    rwa [WittVector.coeff_truncate, WittVector.coeff_truncate] at this
  · intro h
    refine TruncatedWittVector.ext fun i => ?_
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate]
    exact h i i.2

omit [CharP k p] in
theorem truncate_eq_zero_iff {m : ℕ} (x : WittVector p k) :
    WittVector.truncate m x = 0 ↔ ∀ i < m, x.coeff i = 0 := by
  rw [← map_zero (WittVector.truncate m), truncate_eq_iff]
  simp only [WittVector.zero_coeff]

theorem truncate_frobenius_congr {m : ℕ} {x y : WittVector p k}
    (h : WittVector.truncate m x = WittVector.truncate m y) :
    WittVector.truncate m (WittVector.frobenius x) = WittVector.truncate m (WittVector.frobenius y) := by
  rw [truncate_eq_iff] at h ⊢
  intro i hi
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, h i hi]

theorem truncM_frobM_congr {m : ℕ} {P P' : Matrix (Fin n) (Fin n) (WittVector p k)}
    (h : truncM m P = truncM m P') : truncM m (frobM P) = truncM m (frobM P') := by
  ext i j : 1
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij ⊢
  exact truncate_frobenius_congr hij

def vIter (m : ℕ) : WittVector p k →+ WittVector p k where
  toFun := WittVector.verschiebung^[m]
  map_zero' := iterate_map_zero (WittVector.verschiebung : WittVector p k →+ WittVector p k) m
  map_add' x y := by
    induction m with
    | zero => rfl
    | succ m ih => rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ih, map_add]

omit [CharP k p] in
@[scoped simp] theorem vIter_apply (m : ℕ) (x : WittVector p k) : vIter m x = WittVector.verschiebung^[m] x := rfl

omit [CharP k p] in

theorem eq_vIter_of_truncate_eq_zero {m : ℕ} {x : WittVector p k} (h : WittVector.truncate m x = 0) :
    x = vIter m (x.shift m) :=
  WittVector.eq_iterate_verschiebung ((truncate_eq_zero_iff x).mp h)

omit [CharP k p] in

theorem truncate_vIter (m : ℕ) (z : WittVector p k) : WittVector.truncate m (vIter m z) = 0 := by
  rw [truncate_eq_zero_iff]
  intro i hi
  exact WittVector.iterate_verschiebung_coeff_eq_zero z hi

omit [CharP k p] in

theorem truncate_succ_vIter {m : ℕ} {z : WittVector p k} (hz : z.coeff 0 = 0) :
    WittVector.truncate (m + 1) (vIter m z) = 0 := by
  rw [truncate_eq_zero_iff]
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
  · exact WittVector.iterate_verschiebung_coeff_eq_zero z hlt
  · rw [heq]
    have := WittVector.iterate_verschiebung_coeff z m 0
    rw [zero_add] at this
    rw [vIter_apply, this, hz]

omit [CharP k p] in

theorem mul_vIter (m : ℕ) (a z : WittVector p k) :
    a * vIter m z = vIter m (WittVector.frobenius^[m] a * z) := by
  rw [vIter_apply, vIter_apply, mul_comm, WittVector.iterate_verschiebung_mul_left, mul_comm]

theorem frobenius_vIter (m : ℕ) (z : WittVector p k) :
    WittVector.frobenius (vIter m z) = vIter m (WittVector.frobenius z) := by
  rw [vIter_apply, vIter_apply]
  exact ((WittVector.verschiebung_frobenius_comm (p := p) (R := k)).iterate_left m z).symm

theorem constantCoeff_iterate_frobenius (m : ℕ) (a : WittVector p k) :
    WittVector.constantCoeff (WittVector.frobenius^[m] a) = a.coeff 0 ^ p ^ m := by
  rw [WittVector.constantCoeff_apply, WittVector.iterate_frobenius_coeff]

omit [CharP k p] in
theorem constantCoeff_teichmuller (d : k) :
    WittVector.constantCoeff (WittVector.teichmuller p d) = d := by
  rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem constantCoeff_frobenius_teichmuller (d : k) :
    WittVector.constantCoeff (WittVector.frobenius (WittVector.teichmuller p d)) = d ^ p := by
  rw [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP, WittVector.teichmuller_coeff_zero]

variable [IsAlgClosed k]

theorem step (A : Matrix (Fin n) (Fin n) (WittVector p k)) (hA : IsUnit (resM A)) (m : ℕ)
    (P : Matrix (Fin n) (Fin n) (WittVector p k))
    (hP : truncM (m + 1) (A * frobM P) = truncM (m + 1) P) :
    ∃ D : Matrix (Fin n) (Fin n) (WittVector p k), truncM (m + 1) D = 0 ∧
      truncM (m + 2) (A * frobM (P + D)) = truncM (m + 2) (P + D) := by
  classical

  set E : Matrix (Fin n) (Fin n) (WittVector p k) := A * frobM P - P with hE
  have hE0 : ∀ i j, WittVector.truncate (m + 1) (E i j) = 0 := by
    intro i j
    have h := congrFun (congrFun hP i) j
    simp only [Matrix.map_apply] at h
    rw [hE, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact h
  let E' : Matrix (Fin n) (Fin n) (WittVector p k) := fun i j => (E i j).shift (m + 1)
  have hEE' : ∀ i j, E i j = vIter (m + 1) (E' i j) := fun i j => eq_vIter_of_truncate_eq_zero (hE0 i j)

  let Bk : Matrix (Fin n) (Fin n) k := (resM A).map (iterateFrobenius k p (m + 1))
  have hBk : IsUnit Bk := hA.map (RingHom.mapMatrix (iterateFrobenius k p (m + 1)))
  let Ek : Matrix (Fin n) (Fin n) k := fun i j => (E' i j).coeff 0
  obtain ⟨d, hd⟩ := exists_matrix_sub_mul_frob_eq (p := p) Bk hBk Ek

  let D : Matrix (Fin n) (Fin n) (WittVector p k) :=
    fun i j => vIter (m + 1) (WittVector.teichmuller p (d i j))
  refine ⟨D, ?_, ?_⟩
  · ext i j : 1
    simp only [Matrix.map_apply, Matrix.zero_apply]
    exact truncate_vIter (m + 1) _
  ·
    have hnew : A * frobM (P + D) - (P + D) = E + (A * frobM D - D) := by
      rw [hE]
      have : frobM (P + D) = frobM P + frobM D :=
        Matrix.map_add _ (map_add WittVector.frobenius) P D
      rw [this, Matrix.mul_add]
      abel
    suffices h : truncM (m + 2) (A * frobM (P + D) - (P + D)) = 0 by
      have h' : truncM (m + 2) (A * frobM (P + D)) - truncM (m + 2) (P + D) = 0 := by
        rw [← h]
        exact (Matrix.map_sub _ (map_sub (WittVector.truncate (m + 2))) _ _).symm
      exact sub_eq_zero.mp h'
    rw [hnew]
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.mul_apply]

    have hentry : E i j + (∑ l, A i l * WittVector.frobenius (D l j) - D i j) =
        vIter (m + 1) (E' i j + (∑ l, WittVector.frobenius^[m + 1] (A i l) *
          WittVector.frobenius (WittVector.teichmuller p (d l j)) - WittVector.teichmuller p (d i j))) := by
      rw [map_add, map_sub, map_sum, hEE' i j]
      congr 2
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [show D l j = vIter (m + 1) (WittVector.teichmuller p (d l j)) from rfl, frobenius_vIter,
        mul_vIter]
    rw [hentry]
    apply truncate_succ_vIter

    have hd' := congrFun (congrFun hd i) j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply] at hd'
    rw [← WittVector.constantCoeff_apply, map_add, map_sub, map_sum]
    simp only [map_mul, constantCoeff_iterate_frobenius, constantCoeff_frobenius_teichmuller,
      constantCoeff_teichmuller]
    have hEk : WittVector.constantCoeff (E' i j) = Ek i j := rfl
    rw [hEk, ← hd']
    have hB : ∀ l, (A i l).coeff 0 ^ p ^ (m + 1) = Bk i l := by
      intro l
      simp [Bk, Matrix.map_apply, iterateFrobenius_def, WittVector.constantCoeff_apply]
    simp only [hB, frobenius_def]
    ring

theorem base (A : Matrix (Fin n) (Fin n) (WittVector p k)) (hA : IsUnit (resM A)) :
    ∃ P : Matrix (Fin n) (Fin n) (WittVector p k), IsUnit (resM P) ∧
      truncM 1 (A * frobM P) = truncM 1 P := by
  classical
  obtain ⟨Q, hQ, hBQ⟩ := exists_matrix_mul_frob_eq (p := p) (resM A) hA
  refine ⟨Q.map (WittVector.teichmuller p), ?_, ?_⟩
  · have : resM (Q.map (WittVector.teichmuller p)) = Q := by
      ext i j : 1
      simp only [Matrix.map_apply]
      exact constantCoeff_teichmuller (p := p) _
    rw [this]; exact hQ
  · ext i j : 1
    simp only [Matrix.map_apply]
    rw [truncate_eq_iff]
    intro t ht
    have ht0 : t = 0 := by omega
    subst ht0
    have h := congrFun (congrFun hBQ i) j
    simp only [Matrix.mul_apply, Matrix.map_apply] at h
    rw [← WittVector.constantCoeff_apply, ← WittVector.constantCoeff_apply, Matrix.mul_apply, map_sum]
    simp only [map_mul, Matrix.map_apply, constantCoeff_frobenius_teichmuller, constantCoeff_teichmuller]
    simpa [frobenius_def, WittVector.constantCoeff_apply] using h

theorem exists_matrix_mul_frobM_eq (A : Matrix (Fin n) (Fin n) (WittVector p k)) (hA : IsUnit (resM A)) :
    ∃ P : Matrix (Fin n) (Fin n) (WittVector p k), IsUnit P.det ∧ A * frobM P = P := by
  classical
  obtain ⟨P₀, hP₀u, hP₀⟩ := base A hA

  let T : ℕ → Type u := fun m =>
    {P : Matrix (Fin n) (Fin n) (WittVector p k) // truncM (m + 1) (A * frobM P) = truncM (m + 1) P}
  let sq : ∀ m, T m := fun m => Nat.rec (motive := T) ⟨P₀, hP₀⟩
    (fun m Pm => ⟨Pm.1 + Classical.choose (step A hA m Pm.1 Pm.2),
      (Classical.choose_spec (step A hA m Pm.1 Pm.2)).2⟩) m
  have sq_zero : (sq 0).1 = P₀ := rfl
  have sq_succ : ∀ m, truncM (m + 1) (sq (m + 1)).1 = truncM (m + 1) (sq m).1 := by
    intro m
    show truncM (m + 1) ((sq m).1 + Classical.choose (step A hA m (sq m).1 (sq m).2)) = _
    have hD := (Classical.choose_spec (step A hA m (sq m).1 (sq m).2)).1
    have : truncM (m + 1) ((sq m).1 + Classical.choose (step A hA m (sq m).1 (sq m).2)) =
        truncM (m + 1) (sq m).1 + truncM (m + 1) (Classical.choose (step A hA m (sq m).1 (sq m).2)) :=
      Matrix.map_add _ (map_add (WittVector.truncate (m + 1))) _ _
    rw [this, hD, add_zero]

  have chain : ∀ t m, t ≤ m → truncM (t + 1) (sq m).1 = truncM (t + 1) (sq t).1 := by
    intro t m htm
    induction m with
    | zero =>
      have : t = 0 := by omega
      subst this; rfl
    | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_iff.mpr htm) with hlt | heq
      · have hle : t + 1 ≤ m + 1 := by omega
        have key : ∀ P : Matrix (Fin n) (Fin n) (WittVector p k), truncM (t + 1) P =
            (truncM (m + 1) P).map (TruncatedWittVector.truncate hle) := by
          intro P
          ext i j : 1
          simp only [Matrix.map_apply]
          exact (TruncatedWittVector.truncate_wittVector_truncate hle _).symm
        rw [key, sq_succ m, ← key]
        exact ih (by omega)
      · subst heq; rfl

  let P : Matrix (Fin n) (Fin n) (WittVector p k) :=
    fun i j => WittVector.mk p fun t => ((sq t).1 i j).coeff t
  have hlim : ∀ m, truncM (m + 1) P = truncM (m + 1) (sq m).1 := by
    intro m
    ext i j : 1
    simp only [Matrix.map_apply]
    rw [truncate_eq_iff]
    intro t ht
    show ((sq t).1 i j).coeff t = ((sq m).1 i j).coeff t
    have hc := congrFun (congrFun (chain t m (by omega)) i) j
    simp only [Matrix.map_apply] at hc
    rw [truncate_eq_iff] at hc
    exact (hc t (Nat.lt_succ_self t)).symm
  refine ⟨P, ?_, ?_⟩
  ·
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, RingHom.map_det]
    have hres : (WittVector.constantCoeff (p := p) (R := k)).mapMatrix P = resM P₀ := by
      ext i j : 1
      show WittVector.constantCoeff (P i j) = WittVector.constantCoeff (P₀ i j)
      have h := congrFun (congrFun (hlim 0) i) j
      simp only [Matrix.map_apply] at h
      rw [truncate_eq_iff] at h
      rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, h 0 Nat.zero_lt_one, sq_zero]
    rw [hres]
    exact (hP₀u.map Matrix.detMonoidHom).ne_zero
  · ext i j : 1
    refine WittVector.ext fun t => ?_
    have h1 : truncM (t + 1) (A * frobM P) = truncM (t + 1) P := by
      have hmul : ∀ X : Matrix (Fin n) (Fin n) (WittVector p k), truncM (t + 1) (A * frobM X) =
          truncM (t + 1) A * truncM (t + 1) (frobM X) := fun X => Matrix.map_mul
      rw [hmul, truncM_frobM_congr (hlim t), ← hmul, (sq t).2, hlim t]
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.map_apply] at h2
    rw [truncate_eq_iff] at h2
    exact h2 t (Nat.lt_succ_self t)

end Witt

section Module

variable [IsAlgClosed k] [CharP k p]
variable {M : Type v} [AddCommGroup M] [Module (WittVector p k) M]

omit [IsAlgClosed k] [CharP k p] in

theorem apply_sum_smul {ι : Type*} (s : Finset ι) (U : M →+ M)
    (hU : ∀ (w : WittVector p k) (x : M), U (w • x) = WittVector.frobenius w • U x)
    (c : ι → WittVector p k) (v : ι → M) :
    U (∑ i ∈ s, c i • v i) = ∑ i ∈ s, WittVector.frobenius (c i) • U (v i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => hU _ _

end Module

end P2mKcWittLang
p2m_reactivate "P2MW.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed.P2mKcWittLang"

open P2mKcWittLang in

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (M : Type v) [AddCommGroup M] [Module (WittVector p k) M]
    [Module.Free (WittVector p k) M] [Module.Finite (WittVector p k) M]
    (U : M →+ M) (hU : ∀ (w : WittVector p k) (x : M), U (w • x) = WittVector.frobenius w • U x)
    (hbij : Function.Bijective U) :
    ∃ b : Module.Basis (Fin (Module.finrank (WittVector p k) M)) (WittVector p k) M,
      ∀ i, U (b i) = b i := by
  classical
  set n := Module.finrank (WittVector p k) M with hn
  let e : Module.Basis (Fin n) (WittVector p k) M := Module.finBasis (WittVector p k) M

  let A : Matrix (Fin n) (Fin n) (WittVector p k) := fun i j => e.repr (U (e j)) i
  have hUe : ∀ j, U (e j) = ∑ i, A i j • e i := by
    intro j
    conv_lhs => rw [← e.sum_repr (U (e j))]
  have hUsum : ∀ c : Fin n → WittVector p k,
      U (∑ j, c j • e j) = ∑ i, (A.mulVec fun j => WittVector.frobenius (c j)) i • e i := by
    intro c
    rw [apply_sum_smul _ U hU]
    simp_rw [hUe, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]

  have hA : IsUnit A := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro y
    obtain ⟨x, hx⟩ := hbij.2 (∑ i, y i • e i)
    refine ⟨fun j => WittVector.frobenius (e.repr x j), ?_⟩
    have hx' : U (∑ j, e.repr x j • e j) = ∑ i, y i • e i := by rw [e.sum_repr]; exact hx
    rw [hUsum] at hx'
    have h1 : e.equivFun.symm (A.mulVec fun j => WittVector.frobenius (e.repr x j)) =
        e.equivFun.symm y := by
      rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply]; exact hx'
    exact e.equivFun.symm.injective h1
  have hAres : IsUnit (resM A) := hA.map (RingHom.mapMatrix WittVector.constantCoeff)
  obtain ⟨P, hPdet, hAP⟩ := exists_matrix_mul_frobM_eq A hAres

  let f : M ≃ₗ[WittVector p k] M := Matrix.toLinearEquiv e P hPdet
  refine ⟨e.map f, fun j => ?_⟩
  have hb : (e.map f) j = ∑ i, P i j • e i := by
    rw [Module.Basis.map_apply]
    show Matrix.toLin e e P (e j) = _
    exact Matrix.toLin_self e e P j
  rw [hb, hUsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h := congrFun (congrFun hAP i) j
  rw [Matrix.mul_apply] at h
  rw [Matrix.mulVec, dotProduct]
  simpa [Matrix.map_apply] using h

end
p2m_reactivate "P2MW.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed.P2mKcWittLang"

end S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed
end P2MW
export P2MW.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed (solution)
