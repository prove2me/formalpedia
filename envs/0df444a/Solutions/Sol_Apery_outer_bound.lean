-- Prove2me | solution 1 for Apery.outer_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T21:59:16.239507+00:00
-- url     : https://prove2.me/submissions/b2207999-2d75-47bc-9f8e-110bf50d3f92

/-
# The outer-range bound (source `Apery/Arith/OuterEntryMain.lean`)

For $p \\ge 7$, $n$ with $40n < 3p$, $2 \\cdot 40n < p^2$ and $3n < p$, the determinant satisfies
$v_p^G(\\Delta_n) \\ge 2\\sum_{c} \\sum_{i < Lo(c)} wO(c,i) - (37n - (2p + 22n - 3 - (37n-1)))$,
the last term being the low-rank correction of the outer framework. The file ports the outer
basis lemmas of `Apery/Arith/OuterBasis.lean` (`sum_LoC`, `card_rootsO`, the mod-$p$
factorisation `rootsO_map_ZMod` of the rows), the pulling-back identity `entryO_eq` and the
weight bound `wO_nonpos` of `Apery/Arith/OuterEntryMain.lean`, and the theorem itself, importing
the proved platform theorems `Apery.outer_frame` and `Apery.outer_entry`, faithful to
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0. With `Apery.small_prime_bound` and
`Apery.inner_bound_cap` it closes `Apery.integral_mN`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourceOuter
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit
import Theorems.Thm_Apery_outer_frame
import Theorems.Thm_Apery_outer_entry

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Finset Polynomial Matrix

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}


variable (hm : 2 * m + 1 = p) (n : ℕ)

lemma sq_injective {p m : ℕ} [hp : Fact p.Prime] (hm : 2 * m + 1 = p) :
    Function.Injective fun c : Fin (m + 1) => -(((c : ℕ) : ZMod p) ^ 2) := by
  intro c c' h
  simp only [neg_inj] at h
  have h2 : (p : ℤ) ∣ ((c : ℕ) - (c' : ℕ) : ℤ) * ((c : ℕ) + (c' : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
    linear_combination h
  have hc := c.isLt; have hc' := c'.isLt
  rcases (Int.Prime.dvd_mul' hp.out h2) with h3 | h3
  · have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> push_cast <;> omega)
    exact Fin.ext (by omega)
  · have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> push_cast <;> omega)
    exact Fin.ext (by omega)

lemma ccls_spec (hm : 2 * m + 1 = p) (c : ZMod p) :
    (((ccls hm c : ℕ) : ℤ) : ZMod p) = c ∨ (((ccls hm c : ℕ) : ℤ) : ZMod p) = -c := by
  have hp0 : NeZero p := ⟨hp.out.ne_zero⟩
  unfold ccls
  split_ifs with h
  · left; simp
  · right
    have hv := c.val_lt
    simp only [Fin.val_mk]
    rw [show ((p - c.val : ℕ) : ℤ) = (p : ℤ) - (c.val : ℤ) by push_cast [Nat.cast_sub hv.le]; ring]
    push_cast
    rw [ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]

lemma ccls_unique (hm : 2 * m + 1 = p) (c : ZMod p) (a : Fin (m + 1))
    (h : (((a : ℕ) : ℤ) : ZMod p) = c ∨ (((a : ℕ) : ℤ) : ZMod p) = -c) : a = ccls hm c := by
  have h1 := ccls_spec hm c
  apply sq_injective hm
  simp only
  have e : ∀ x : ZMod p, x = c ∨ x = -c → x ^ 2 = c ^ 2 := by
    rintro x (rfl | rfl) <;> ring
  have ha := e _ h
  have hc := e _ h1
  push_cast at ha hc
  rw [ha, hc]

lemma sq_eq_iff_ccls (hm : 2 * m + 1 = p) (x y : ZMod p) :
    x ^ 2 = y ^ 2 ↔ ccls hm x = ccls hm y := by
  constructor
  · intro h
    have h2 : (x - y) * (x + y) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [sub_eq_zero.mp h3]
    · have : x = -y := by linear_combination h3
      rw [this]
      exact (ccls_unique hm (-y) (ccls hm y) (by
        rcases ccls_spec hm y with h4 | h4
        · right; rw [h4, neg_neg]
        · left; rw [h4])).symm
  · intro h
    have e : ∀ z : ZMod p, z ^ 2 = ((((ccls hm z : ℕ) : ℤ) : ZMod p)) ^ 2 := by
      intro z
      rcases ccls_spec hm z with h4 | h4 <;> rw [h4]; ring
    rw [e x, e y, h]

lemma ccls_self (c : Fin (m + 1)) : ccls hm ((((c : ℕ) : ℤ) : ZMod p)) = c :=
  (ccls_unique hm _ c (Or.inl rfl)).symm

lemma sq_jc (j : ℕ) : (((j : ℤ) : ZMod p)) ^ 2 = ((((jc hm j : ℕ) : ℤ) : ZMod p)) ^ 2 := by
  rw [sq_eq_iff_ccls hm, ccls_self]; rfl

lemma map_factor (γ : ℤ) :
    (X + C (γ ^ 2) : ℤ[X]).map (Int.castRingHom (ZMod p)) = X - C (-((γ : ZMod p)) ^ 2) := by
  simp [sub_eq_add_neg]

lemma prod_map_const_pow {s : Finset ℕ} {f : ℕ → (ZMod p)[X]} {q : (ZMod p)[X]}
    (h : ∀ j ∈ s, f j = q) : ∏ j ∈ s, f j = q ^ s.card := by
  rw [Finset.prod_congr rfl h, Finset.prod_const]

lemma sum_LoC : ∑ c, LoC hm n c = 37 * n := by
  have := Finset.card_eq_sum_card_fiberwise (f := jc hm) (s := tailO n) (t := Finset.univ)
    (fun j _ => Finset.mem_univ _)
  unfold LoC tailC
  rw [← this, tailO, Nat.card_Icc]; omega

lemma card_rootsO (c : Fin (m + 1)) {i : ℕ} (hi : i < LoC hm n c) :
    (rootsO hm n c i).card < 37 * n := by
  unfold rootsO
  have hsplit := Finset.card_filter_add_card_filter_not (s := tailO n) (fun j => jc hm j = c)
  have htail : (tailO n).card = 37 * n := by rw [tailO, Nat.card_Icc]; omega
  have hnb : nbC hm n c ≤ LoC hm n c := Finset.card_filter_le _ _
  have hLo : LoC hm n c = ((tailO n).filter fun j => jc hm j = c).card := rfl
  have hother : ((tailO n).filter fun j => jc hm j ≠ c).card = 37 * n - LoC hm n c := by
    have : ((tailO n).filter fun j => jc hm j ≠ c).card =
        ((tailO n).filter fun a => ¬ (jc hm a = c)).card := rfl
    omega
  split_ifs with h
  · simp only [Multiset.card_add, Multiset.card_map, Finset.card_val, Multiset.card_replicate]
    omega
  · simp only [Multiset.card_add, Multiset.card_map, Finset.card_val, Multiset.card_replicate]
    have : nbC hm n c = (bigC hm n c).card := rfl
    omega

theorem rootsO_map_ZMod (c : Fin (m + 1)) (i : ℕ) :
    (tpolZ (rootsO hm n c i)).map (Int.castRingHom (ZMod p)) =
      (∏ c' ∈ Finset.univ.erase c, (X - C (γO (p := p) c')) ^ LoC hm n c') * (X - C (γO (p := p) c)) ^ i := by
  have hfac : ∀ j : ℕ, ((X + C (((j : ℤ)) ^ 2) : ℤ[X]).map (Int.castRingHom (ZMod p))) =
      X - C (γO (p := p) (jc hm j)) := by
    intro j; rw [map_factor, γO]; congr 2; exact congrArg Neg.neg (sq_jc hm j)
  have hcc : ((X + C ((((c : ℕ) : ℤ)) ^ 2) : ℤ[X]).map (Int.castRingHom (ZMod p))) = X - C (γO (p := p) c) := by
    rw [map_factor]; rfl
  unfold tpolZ rootsO
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_add, Multiset.prod_add]
  have h1 : ((((tailO n).filter fun j => jc hm j ≠ c).val.map (fun j : ℕ => (j : ℤ))).map
      ((Polynomial.map (Int.castRingHom (ZMod p))) ∘ fun γ : ℤ => X + C (γ ^ 2))).prod =
      ∏ c' ∈ Finset.univ.erase c, (X - C (γO (p := p) c')) ^ LoC hm n c' := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    simp only [Function.comp, hfac]
    rw [← Finset.prod_fiberwise_of_maps_to (g := jc hm) (t := Finset.univ.erase c)
      (fun j hj => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2, Finset.mem_univ _⟩)]
    refine Finset.prod_congr rfl fun c' hc' => ?_
    rw [prod_map_const_pow (q := X - C (γO (p := p) c')) (fun j hj => by
      rw [(Finset.mem_filter.mp hj).2])]
    congr 1
    unfold LoC tailC
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ (Finset.mem_erase.mp hc').1⟩, h3⟩
  rw [h1]
  congr 1
  split_ifs with h
  · rw [Multiset.map_replicate, Multiset.prod_replicate]; simp only [Function.comp, hcc]
  · rw [Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_replicate,
      Multiset.prod_replicate, ← Finset.prod_eq_multiset_prod]
    simp only [Function.comp, hfac, hcc]
    rw [show jc hm ((c : ℕ)) = c from ccls_self hm c]
    rw [prod_map_const_pow (q := X - C (γO (p := p) c)) (fun j hj => by
      rw [(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2]), ← pow_add]
    have : nbC hm n c = (bigC hm n c).card := rfl
    congr 1; omega

lemma tpolZ_map_Q (M : Multiset ℤ) : (tpolZ M).map (Int.castRingHom ℚ) = tpol M := by
  simp [tpolZ, tpol, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp]

lemma D_eq_tpol (m : ℕ) : D m = tpol ((Icc 1 m).val.map fun j : ℕ => (j : ℤ)) := by
  unfold D tpol
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1

lemma natDegree_tpolZ (M : Multiset ℤ) : (tpolZ M).natDegree ≤ M.card := by
  unfold tpolZ
  refine (natDegree_multiset_prod_le _).trans ?_
  rw [Multiset.map_map]
  have : ∀ γ ∈ M, (natDegree ∘ fun γ : ℤ => X + C (γ ^ 2)) γ = 1 := fun γ _ =>
    natDegree_X_add_C _
  rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]

lemma tpol_add (M M' : Multiset ℤ) : tpol (M + M') = tpol M * tpol M' := by
  simp [tpol, Multiset.map_add, Multiset.prod_add]

lemma tpol_nsmul (k : ℕ) (M : Multiset ℤ) : tpol (k • M) = tpol M ^ k := by
  induction k with
  | zero => simp [tpol]
  | succ k ih => rw [succ_nsmul, tpol_add, ih, pow_succ]


lemma entryO_eq (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    D (3 * n) ^ 6 * (tpolZ (rootsO hm n cs is)).map (Int.castRingHom ℚ) *
      (tpolZ (rootsO hm n ct it)).map (Int.castRingHom ℚ) = tpol (entryO hm n cs is ct it) := by
  rw [tpolZ_map_Q, tpolZ_map_Q, D_eq_tpol, ← tpol_nsmul, ← tpol_add, ← tpol_add]; rfl

lemma wO_nonpos (c : Fin (m + 1)) (i : ℕ) : wO hm n c i ≤ 0 := by
  unfold wO; split_ifs <;> first | exact min_le_left _ _ | norm_num


theorem outer_bound_aux (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) :
    GV p (Δ n) (2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
      ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) := by
  classical
  have hcard : Fintype.card (Σ c : Fin (m + 1), Fin (LoC hm n c)) = 37 * n := by
    rw [Fintype.card_sigma]; simpa using sum_LoC hm n
  set e : (Σ c : Fin (m + 1), Fin (LoC hm n c)) ≃ Fin (37 * n) := Fintype.equivFinOfCardEq hcard
  have h := outer_frame (p := p) (by omega) n (fun a => tpolZ (rootsO hm n (e.symm a).1 (e.symm a).2))
    (fun a => (natDegree_tpolZ _).trans_lt (card_rootsO hm n _ (e.symm a).2.isLt))
    (fun c : Fin (m + 1) => γO (p := p) c) (fun a b hab => sq_injective hm (by
      simpa [γO] using hab)) (LoC hm n) (fun a => (e.symm a).1)
    (fun a => (e.symm a).2) (fun a => (e.symm a).2.isLt)
    (fun a b h1 h2 => by
      apply e.symm.injective
      exact Sigma.ext h1 (by rw [Fin.heq_ext_iff (by rw [h1])]; exact h2))
    (fun a => rootsO_map_ZMod hm n _ _)
    (fun a => wO hm n (e.symm a).1 (e.symm a).2) (fun a => wO_nonpos hm n _ _)
    (fun a b => by
      rw [entryO_eq]
      exact outer_entry hm n hp7 hK3 hK hpN _ _ _ _)
  have hsum : ∑ a, wO hm n (e.symm a).1 (e.symm a).2 = ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i := by
    rw [Equiv.sum_comp e.symm (fun s => wO hm n s.1 s.2), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun i => wO hm n c i) _
  rw [hsum] at h
  exact h

end Apery

end Port0

open Finset Polynomial Matrix in
theorem solution {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (n : ℕ)
    (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2) (hpN : 3 * n < p) :
    Apery.GV p (Apery.Δ n) (2 * ∑ c, ∑ i ∈ range (Apery.LoC hm n c), Apery.wO hm n c i -
      ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) :=
  Apery.outer_bound_aux hm n hp7 hK3 hK hpN
