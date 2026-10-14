-- Prove2me | solution 1 for Apery.muX_tpol_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T20:27:48.422097+00:00
-- url     : https://prove2.me/submissions/63921547-225f-49dd-975f-86d8418c9eda

/-
# The entry bound for `μ_X(tpol M / D_K)` (source `Apery/Arith/TEntry.lean`)

For $p \\ge 5$, $K < p^2$, and a multiset $M$ of integers with $5 + 2|M| - 2K + 1 < p^2$, if
$\\beta \\le e_c - \\ell_c$ for every residue class $c \\bmod p$ (zeros vs. poles in the class),
then $v_p^G(\\mu_X(tpol\\,M / D_K)) \\ge \\beta - 4$. The file ports the direct-bound chain
`Apery/Arith/DirectBound.lean` (`Sep`, `VG_H5`, `VG_res`, `padicValRat_denom_le`, ...),
`Apery/Arith/DirectPoly.lean` (`VG_polyPart_eval`, `tauX_direct`) and `Apery/Arith/TEntry.lean`
(`tpol`, `xroots`, `pull_tpol`, `cnt_xroots`, `μX_tpol_bound`), importing the already-proved
`Apery.tau_bound` and `Apery.muX_eq_tauX`. Faithful port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit
import Theorems.Thm_Apery_muX_eq_tauX
import Theorems.Thm_Apery_tau_bound

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Finset Polynomial

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

lemma GV.pow {F : ℚ[X]} {r : ℚ} (h : GV p F r) (n : ℕ) : GV p (F ^ n) (n * r) := by
  induction n with
  | zero => simpa using GV.C (p := p) (VG.one (p := p))
  | succ n ih => rw [pow_succ]; convert ih.mul h using 1; push_cast; ring

lemma GV.comp {F G : ℚ[X]} (hF : GV p F 0) (hG : GV p G 0) : GV p (F.comp G) 0 := by
  rw [comp_eq_sum_left, Polynomial.sum]
  refine GV.sum _ fun n _ => ?_
  have := GV.C_mul (hF n) (hG.pow n)
  simpa using this

lemma VG.eval {F : ℚ[X]} {z : ℚ} (hF : GV p F 0) (hz : VG p z 0) : VG p (F.eval z) 0 := by
  rw [eval_eq_sum, Polynomial.sum]
  refine VG.sum _ fun n _ => ?_
  have := (hF n).mul (hz.pow n)
  simpa using this

lemma VG.eval_zero {F : ℚ[X]} {r : ℚ} (hF : GV p F r) : VG p (F.eval 0) r := by
  rw [← coeff_zero_eq_eval_zero]; exact hF 0

lemma GV.divByMonic_X_sub_C {F : ℚ[X]} {a : ℚ} (hF : GV p F 0) (ha : VG p a 0) :
    GV p (F /ₘ (Polynomial.X - Polynomial.C a)) 0 := fun n => by
  rw [coeff_divByMonic_X_sub_C]
  refine VG.sum _ fun i _ => ?_
  have := (ha.pow (i - (n + 1))).mul (hF i)
  simpa using this

/-- An integral polynomial vanishing at `p`-integral distinct points is divisible by
`∏ (X - ρ)` with an integral quotient. -/
theorem factor_roots (ρs : Finset ℚ) (hρ : ∀ ρ ∈ ρs, VG p ρ 0) {F : ℚ[X]} (hF : GV p F 0)
    (hroot : ∀ ρ ∈ ρs, F.eval ρ = 0) :
    ∃ S : ℚ[X], GV p S 0 ∧ F = (∏ ρ ∈ ρs, (X - C ρ)) * S := by
  classical
  induction ρs using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hF, by simp⟩
  | insert a ρs ha ih =>
    have hra : F.IsRoot a := hroot a (Finset.mem_insert_self _ _)
    set F1 := F /ₘ (X - C a) with hF1
    have hFeq : F = (X - C a) * F1 := ((mul_divByMonic_eq_iff_isRoot).mpr hra).symm
    have hF1int : GV p F1 0 := GV.divByMonic_X_sub_C hF (hρ a (Finset.mem_insert_self _ _))
    have hF1root : ∀ ρ ∈ ρs, F1.eval ρ = 0 := by
      intro ρ hρs
      have h1 := hroot ρ (Finset.mem_insert_of_mem hρs)
      rw [hFeq, eval_mul, eval_sub, eval_X, eval_C] at h1
      have hne : ρ - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hρs)
      exact (mul_eq_zero.mp h1).resolve_left hne
    obtain ⟨S, hS, hSeq⟩ := ih (fun ρ h => hρ ρ (Finset.mem_insert_of_mem h)) hF1int hF1root
    exact ⟨S, hS, by rw [hFeq, hSeq, Finset.prod_insert ha, mul_assoc]⟩

/-- Multiset products. -/
lemma GV.multiset_prod (s : Multiset ℚ[X]) (b : ℚ[X] → ℚ) (h : ∀ f ∈ s, GV p f (b f)) :
    GV p s.prod (s.map b).sum := by
  induction s using Multiset.induction_on with
  | empty => simpa using GV.C (p := p) (VG.one (p := p))
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    exact (h a (Multiset.mem_cons_self _ _)).mul (ih fun f hf => h f (Multiset.mem_cons_of_mem hf))

lemma piPl_monic (Pl : Finset ℤ) : (piPl Pl).Monic :=
  monic_prod_of_monic _ _ fun r _ => monic_X_sub_C _

lemma natDegree_piPl (Pl : Finset ℤ) : (piPl Pl).natDegree = Pl.card := by
  unfold piPl
  rw [natDegree_prod_of_monic _ _ fun r _ => monic_X_sub_C _]
  rw [Finset.sum_congr rfl fun (r : ℤ) _ => natDegree_X_sub_C ((r : ℤ) : ℚ)]
  simp

lemma lagrange_basis_eq (Pl : Finset ℤ) (r : ℤ) :
    Lagrange.basis Pl (fun s : ℤ => (s : ℚ)) r =
      C (∏ s ∈ Pl.erase r, ((r : ℚ) - s))⁻¹ * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) := by
  unfold Lagrange.basis Lagrange.basisDivisor
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]

theorem partial_fractionsP (A : ℚ[X]) (Pl : Finset ℤ) :
    A = polyPart A Pl * piPl Pl +
      ∑ r ∈ Pl, C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) := by
  have hinj : Set.InjOn (fun s : ℤ => (s : ℚ)) Pl := fun a _ b _ h => by
    simpa using h
  have hmod : A %ₘ piPl Pl = ∑ r ∈ Pl, C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) := by
    rw [Lagrange.eq_interpolate_of_eval_eq (f := A %ₘ piPl Pl) (fun r : ℤ => A.eval (r : ℚ)) hinj
      (by
        have := degree_modByMonic_lt A (piPl_monic Pl)
        rwa [degree_eq_natDegree (piPl_monic Pl).ne_zero, natDegree_piPl] at this)
      (fun r hr => by
        have h1 := modByMonic_add_div A (piPl Pl)
        have h2 : (piPl Pl).eval (r : ℚ) = 0 := by
          unfold piPl; rw [eval_prod]
          exact Finset.prod_eq_zero hr (by simp)
        conv_rhs => rw [← h1]
        rw [eval_add, eval_mul, h2, zero_mul, add_zero])]
    simp only [Lagrange.interpolate_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [lagrange_basis_eq, resP, div_eq_mul_inv, C_mul, mul_assoc]
  conv_lhs => rw [← modByMonic_add_div A (piPl Pl)]
  rw [hmod, polyPart, add_comm, mul_comm]

lemma natDegree_polyPart_le (A : ℚ[X]) (Pl : Finset ℤ) :
    (polyPart A Pl).natDegree ≤ A.natDegree - Pl.card := by
  unfold polyPart
  rw [natDegree_divByMonic A (piPl_monic Pl), natDegree_piPl]

lemma PlK_disjoint (K : ℕ) :
    Disjoint ((Icc 1 K).image (fun j : ℕ => (j : ℤ))) ((Icc 1 K).image (fun j : ℕ => -(j : ℤ))) := by
  rw [Finset.disjoint_left]
  intro r h1 h2
  rw [Finset.mem_image] at h1 h2
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, hab⟩ := h2
  rw [Finset.mem_Icc] at ha hb
  omega

lemma prod_PlK {M : Type*} [CommMonoid M] (K : ℕ) (f : ℤ → M) :
    ∏ r ∈ PlK K, f r = ∏ j ∈ Icc 1 K, (f j * f (-j)) := by
  rw [PlK, Finset.prod_union (PlK_disjoint K), Finset.prod_image (fun a _ b _ h => by exact_mod_cast h),
    Finset.prod_image (fun a _ b _ h => by simpa using h), Finset.prod_mul_distrib]

lemma card_PlK (K : ℕ) : (PlK K).card = 2 * K := by
  rw [PlK, Finset.card_union_of_disjoint (PlK_disjoint K),
    Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp; ring

lemma dd_nat (j : ℕ) : dd (j : ℤ) = j := by simp [dd]

lemma dd_neg {j : ℕ} (hj : 1 ≤ j) : dd (-(j : ℤ)) = j - 1 := by
  unfold dd
  rw [if_neg (by omega)]
  omega

lemma zmod_eq_iff_dvd {a b : ℤ} : (a : ZMod p) = b ↔ (p : ℤ) ∣ a - b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact sub_eq_zero.symm

lemma VG_int_one {z : ℤ} (h : (p : ℤ) ∣ z) : VG p (z : ℚ) 1 := by
  by_cases hz : z = 0
  · left; simp [hz]
  right
  rw [padicValRat.of_int]
  have := (padicValInt_dvd_iff (p := p) 1 z).mp (by simpa using h)
  rcases this with h | h
  · exact absurd h hz
  · exact_mod_cast h

lemma padicValRat_int_eq_zero {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  have hz : z ≠ 0 := fun h' => h (h' ▸ dvd_zero _)
  by_contra hne
  have h1 : 1 ≤ padicValInt p z := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
  exact h (by simpa using (padicValInt_dvd_iff (p := p) 1 z).mpr (Or.inr h1))

lemma padicValRat_int_le_one {z : ℤ} (h2 : ¬ (p : ℤ) ^ 2 ∣ z) : padicValRat p (z : ℚ) ≤ 1 := by
  rw [padicValRat.of_int]
  by_contra hne
  rw [not_le] at hne
  have : 2 ≤ padicValInt p z := by exact_mod_cast hne
  have hz : z ≠ 0 := by rintro rfl; simp at hne
  exact h2 ((padicValInt_dvd_iff (p := p) 2 z).mpr (Or.inr this))

lemma padicValRat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValRat.mul (hf a (mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

lemma VG.multiset_prod (s : Multiset ℚ) (b : ℚ → ℚ) (h : ∀ q ∈ s, VG p q (b q)) :
    VG p s.prod (s.map b).sum := by
  induction s using Multiset.induction_on with
  | empty => right; simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    exact (h a (Multiset.mem_cons_self _ _)).mul (ih fun q hq => h q (Multiset.mem_cons_of_mem hq))

/-! ### The harmonic numbers -/

lemma VG_H5 {m : ℕ} (hm : m < p ^ 2) : VG p (H5 m) (-5) := by
  unfold H5
  refine VG.sum _ fun v hv => ?_
  rw [Finset.mem_Icc] at hv
  rw [one_div]
  apply VG.inv (pow_ne_zero _ (by exact_mod_cast (by omega : v ≠ 0)))
  rw [show ((v : ℚ) ^ 5) = ((v ^ 5 : ℕ) : ℚ) by push_cast; ring, padicValRat.of_nat,
    padicValNat.pow (p := p) v 5]
  have : padicValNat p v ≤ 1 := by
    by_contra hne
    rw [not_le] at hne
    have h2 : p ^ 2 ∣ v := (padicValNat_dvd_iff_le (by omega)).mpr hne
    exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
  push_cast
  have h3 : (padicValRat p (v : ℚ) : ℚ) ≤ 1 := by rw [padicValRat.of_nat]; exact_mod_cast this
  linarith

/-! ### Residues -/

lemma eval_numOf (κ : ℚ) (Z : Multiset ℤ) (x : ℚ) :
    (numOf κ Z).eval x = κ * (Z.map fun ζ : ℤ => x - (ζ : ℚ)).prod := by
  unfold numOf
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun ζ _ => by simp

lemma VG_prod_sub (Z : Multiset ℤ) (x : ℤ) :
    VG p ((Z.map fun ζ : ℤ => (x : ℚ) - (ζ : ℚ)).prod) (cnt p Z (x : ZMod p)) := by
  induction Z using Multiset.induction_on with
  | empty => right; simp [cnt]
  | cons a Z ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    unfold cnt at ih ⊢
    rw [Multiset.filter_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      have h1 : VG p ((x : ℚ) - (a : ℚ)) 1 := by
        have := VG_int_one (p := p) ((zmod_eq_iff_dvd (p := p)).mp h.symm)
        simpa using this
      convert h1.mul ih using 1; push_cast; ring
    · rw [zero_add]
      have h1 : VG p ((x : ℚ) - (a : ℚ)) 0 := by simpa using VG.intCast (p := p) (x - a)
      simpa using h1.mul ih

lemma VG_eval_numOf (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (x : ℤ) :
    VG p ((numOf κ Z).eval (x : ℚ)) (cnt p Z (x : ZMod p)) := by
  rw [eval_numOf]
  simpa using hκ.mul (VG_prod_sub Z x)

lemma padicValRat_denom_le (Pl : Finset ℤ) (hsep : Sep p Pl) {r : ℤ} (hr : r ∈ Pl) :
    (padicValRat p (∏ s ∈ Pl.erase r, ((r : ℚ) - s)) : ℚ) ≤ (plc p Pl r).card - 1 := by
  rw [padicValRat_finset_prod _ _ (fun s hs => by
    rw [Finset.mem_erase] at hs
    exact sub_ne_zero.mpr (by exact_mod_cast hs.1.symm))]
  have hterm : ∀ s ∈ Pl.erase r, (padicValRat p ((r : ℚ) - s) : ℚ) ≤
      if (s : ZMod p) = r then 1 else 0 := by
    intro s hs
    rw [Finset.mem_erase] at hs
    have e : ((r : ℚ) - s) = ((r - s : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    split_ifs with h
    · exact_mod_cast padicValRat_int_le_one (hsep r hr s hs.2 (Ne.symm hs.1) h.symm)
    · rw [padicValRat_int_eq_zero (fun hd => h ((zmod_eq_iff_dvd (p := p)).mpr
        (by rw [← neg_sub]; exact (dvd_neg).mpr hd)))]
      simp
  push_cast
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  have hcard : ((Pl.erase r).filter fun s : ℤ => (s : ZMod p) = r) = (plc p Pl r).erase r := by
    unfold plc; rw [Finset.filter_erase]
  rw [hcard, Finset.card_erase_of_mem (by unfold plc; simp [hr])]
  have : 1 ≤ (plc p Pl r).card := Finset.card_pos.mpr ⟨r, by unfold plc; simp [hr]⟩
  push_cast [this]
  linarith

/-- **Residue bound**: `v_p(res_r) ≥ e_c - ℓ_c + 1` for the class `c` of `r`. -/
theorem VG_res (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (Pl : Finset ℤ) (hsep : Sep p Pl)
    {r : ℤ} (hr : r ∈ Pl) :
    VG p (resP (numOf κ Z) Pl r) ((cnt p Z r : ℚ) - (plc p Pl r).card + 1) := by
  unfold resP
  rw [div_eq_mul_inv]
  have hD : ∏ s ∈ Pl.erase r, ((r : ℚ) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s hs => by
    rw [Finset.mem_erase] at hs
    exact sub_ne_zero.mpr (by exact_mod_cast hs.1.symm)
  have h1 := VG_eval_numOf κ hκ Z r
  have h2 := VG.inv (p := p) hD (padicValRat_denom_le Pl hsep hr)
  convert h1.mul h2 using 1
  ring
lemma prod_erase_split {f : ℤ → ℚ[X]} (S : Finset ℤ) (q : ℤ → Prop) [DecidablePred q] (r : ℤ) :
    ∏ s ∈ S.erase r, f s = (∏ s ∈ (S.filter q).erase r, f s) * ∏ s ∈ (S.filter (¬ q ·)).erase r, f s := by
  rw [← Finset.filter_erase, ← Finset.filter_erase, Finset.prod_filter_mul_prod_filter_not]

lemma GV_lin_comp_class (m ζ : ℤ) (h : (ζ : ZMod p) = m) :
    GV p ((X - C (ζ : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X)) 1 := by
  rw [sub_comp, X_comp, C_comp, show C (m : ℚ) + C (p : ℚ) * X - C (ζ : ℚ) =
    C (((m - ζ : ℤ) : ℚ)) + C (p : ℚ) * X by push_cast; rw [C_sub]; ring]
  have h1 : VG p (((m - ζ : ℤ) : ℚ)) 1 := VG_int_one ((zmod_eq_iff_dvd (p := p)).mp h.symm)
  have h2 : VG p (p : ℚ) 1 := by simpa using VG.primePow (p := p) 1
  exact (GV.C h1).add (by simpa using GV.C_mul h2 GV.X)

lemma GV_lin_comp (m ζ : ℤ) : GV p ((X - C (ζ : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X)) 0 := by
  rw [sub_comp, X_comp, C_comp, show C (m : ℚ) + C (p : ℚ) * X - C (ζ : ℚ) =
    C (((m - ζ : ℤ) : ℚ)) + C (p : ℚ) * X by push_cast; rw [C_sub]; ring]
  exact (GV.C (VG.intCast _)).add (by simpa using GV.C_mul (VG.natCast (p := p) p) GV.X)

lemma GV_numOf_comp (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (m : ℤ) :
    GV p ((numOf κ Z).comp (C (m : ℚ) + C (p : ℚ) * X)) (cnt p Z (m : ZMod p)) := by
  unfold numOf
  rw [mul_comp, C_comp, multiset_prod_comp, Multiset.map_map]
  suffices h : GV p ((Z.map ((fun q => q.comp (C (m : ℚ) + C (p : ℚ) * X)) ∘
      fun ζ : ℤ => X - C (ζ : ℚ))).prod) (cnt p Z (m : ZMod p)) by
    simpa using GV.C_mul hκ h
  induction Z using Multiset.induction_on with
  | empty => simpa [cnt] using GV.C (p := p) (VG.one (p := p))
  | cons a Z ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    unfold cnt at ih ⊢
    rw [Multiset.filter_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      have := (GV_lin_comp_class m a h).mul ih
      convert this using 1
      · simp [Function.comp]
      · push_cast; ring
    · rw [zero_add]
      simpa using (GV_lin_comp m a).mul ih

/-- `(x - r)(m + p z) = p (z - ρ)` with `ρ = (r - m)/p`, for `r ≡ m`. -/
lemma lin_comp_eq {m r : ℤ} (h : (p : ℤ) ∣ r - m) :
    (X - C (r : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X) =
      C (p : ℚ) * (X - C (((r - m) / p : ℤ) : ℚ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e : (p : ℚ) * (((r - m) / p : ℤ) : ℚ) = (r : ℚ) - m := by
    have := Int.mul_ediv_cancel' h
    exact_mod_cast this
  rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, e, C_sub]; ring

/-- **Class-wise bound for the polynomial part.** -/
theorem VG_polyPart_eval (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (Pl : Finset ℤ)
    (hsep : Sep p Pl) (β : ℚ) (hβ : ∀ c : ZMod p, β ≤ (cnt p Z c : ℚ) - (plc p Pl c).card)
    (m : ℤ) : VG p ((polyPart (numOf κ Z) Pl).eval (m : ℚ)) β := by
  classical
  set A := numOf κ Z with hA
  set P := polyPart A Pl with hP
  set c : ZMod p := (m : ZMod p) with hc
  set Plc := plc p Pl c with hPlc
  set Plo := Pl.filter fun r : ℤ => ¬ (r : ZMod p) = c with hPlo
  set PiC := ∏ r ∈ Plc, (X - C (r : ℚ)) with hPiC
  set PiO := ∏ r ∈ Plo, (X - C (r : ℚ)) with hPiO
  have hPi : piPl Pl = PiC * PiO := by
    unfold piPl; rw [hPiC, hPiO, hPlc, plc, Finset.prod_filter_mul_prod_filter_not]
  set H := P * PiO + ∑ r ∈ Plo, C (resP A Pl r) * ∏ s ∈ Plo.erase r, (X - C (s : ℚ)) with hH
  set I := ∑ r ∈ Plc, C (resP A Pl r) * ∏ s ∈ Plc.erase r, (X - C (s : ℚ)) with hI
  -- the splitting identity
  have hAHI : A = PiC * H + PiO * I := by
    have hpf := partial_fractionsP A Pl
    rw [← Finset.sum_filter_add_sum_filter_not Pl (fun r : ℤ => (r : ZMod p) = c)] at hpf
    have h1 : ∀ r ∈ Pl.filter (fun r : ℤ => (r : ZMod p) = c),
        C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) =
          PiO * (C (resP A Pl r) * ∏ s ∈ Plc.erase r, (X - C (s : ℚ))) := by
      intro r hr
      rw [prod_erase_split Pl (fun s : ℤ => (s : ZMod p) = c) r]
      have hro : r ∉ Plo := by
        rw [hPlo, Finset.mem_filter]; rw [Finset.mem_filter] at hr; tauto
      rw [Finset.erase_eq_of_notMem hro]
      rw [hPlc, plc]; ring
    have h2 : ∀ r ∈ Pl.filter (fun r : ℤ => ¬ (r : ZMod p) = c),
        C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) =
          PiC * (C (resP A Pl r) * ∏ s ∈ Plo.erase r, (X - C (s : ℚ))) := by
      intro r hr
      rw [prod_erase_split Pl (fun s : ℤ => (s : ZMod p) = c) r]
      have hrc : r ∉ Plc := by
        rw [hPlc, plc, Finset.mem_filter]; rw [Finset.mem_filter] at hr; tauto
      rw [show (Pl.filter fun s : ℤ => (s : ZMod p) = c).erase r = Plc by
        rw [hPlc, plc]; exact Finset.erase_eq_of_notMem hrc]
      rw [hPiC]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
      hPi] at hpf
    have e1 : (Pl.filter fun r : ℤ => (r : ZMod p) = c) = Plc := by rw [hPlc, plc]
    have e2 : (Pl.filter fun r : ℤ => ¬ (r : ZMod p) = c) = Plo := by rw [hPlo]
    rw [e1, e2] at hpf
    conv_lhs => rw [hpf]
    rw [hH, hI, hP]; ring
  -- membership facts
  have hmemc : ∀ r ∈ Plc, r ∈ Pl ∧ (r : ZMod p) = c := fun r hr => by
    rw [hPlc, plc, Finset.mem_filter] at hr; exact hr
  have hmemo : ∀ r ∈ Plo, r ∈ Pl ∧ ¬ (r : ZMod p) = c := fun r hr => by
    rw [hPlo, Finset.mem_filter] at hr; exact hr
  have hdiv : ∀ r ∈ Plc, (p : ℤ) ∣ r - m := fun r hr =>
    (zmod_eq_iff_dvd (p := p)).mp (by rw [(hmemc r hr).2, hc])
  have hndiv : ∀ r ∈ Plo, ¬ (p : ℤ) ∣ m - r := fun r hr hd =>
    (hmemo r hr).2 (by rw [hc]; exact ((zmod_eq_iff_dvd (p := p)).mpr hd).symm)
  -- Part A: `P(m) = H(m)/PiO(m) - ∑ res_r/(m - r)`
  have hfac : ∀ r ∈ Plo, ((m : ℚ) - r) ≠ 0 := fun r hr h => hndiv r hr (by
    have : m - r = 0 := by exact_mod_cast h
    rw [this]; exact dvd_zero _)
  have hPiOm : PiO.eval (m : ℚ) = ∏ r ∈ Plo, ((m : ℚ) - r) := by
    rw [hPiO, eval_prod]; simp
  have hPiOne : PiO.eval (m : ℚ) ≠ 0 := by
    rw [hPiOm]; exact Finset.prod_ne_zero_iff.mpr hfac
  have hVGinv : ∀ r ∈ Plo, VG p ((m : ℚ) - r)⁻¹ 0 := fun r hr => by
    refine (VG.inv (p := p) (r := 0) (hfac r hr) ?_).mono (by norm_num)
    rw [show ((m : ℚ) - r) = ((m - r : ℤ) : ℚ) by push_cast; ring,
      padicValRat_int_eq_zero (hndiv r hr)]; simp
  have hVGinvPiO : VG p (PiO.eval (m : ℚ))⁻¹ 0 := by
    refine (VG.inv (p := p) (r := 0) hPiOne ?_).mono (by norm_num)
    rw [hPiOm, padicValRat_finset_prod _ _ hfac]
    push_cast
    rw [Finset.sum_eq_zero fun r hr => by
      rw [show ((m : ℚ) - r) = ((m - r : ℤ) : ℚ) by push_cast; ring,
        padicValRat_int_eq_zero (hndiv r hr)]; simp]
  have hEo : ∀ r ∈ Plo, (∏ s ∈ Plo.erase r, (X - C (s : ℚ))).eval (m : ℚ) =
      PiO.eval (m : ℚ) * ((m : ℚ) - r)⁻¹ := by
    intro r hr
    have h := Finset.mul_prod_erase Plo (fun s : ℤ => X - C (s : ℚ)) hr
    rw [← hPiO] at h
    have h2 := congrArg (eval (m : ℚ)) h
    rw [eval_mul, eval_sub, eval_X, eval_C] at h2
    rw [← h2]; field_simp [hfac r hr]
  have hPm : P.eval (m : ℚ) = H.eval (m : ℚ) * (PiO.eval (m : ℚ))⁻¹ -
      ∑ r ∈ Plo, resP A Pl r * ((m : ℚ) - r)⁻¹ := by
    rw [hH, eval_add, eval_mul, eval_finsetSum]
    simp only [eval_mul, eval_C]
    rw [Finset.sum_congr rfl fun r hr => by rw [hEo r hr]]
    rw [add_mul, Finset.sum_mul]
    field_simp
    ring_nf
  -- Part B: the substitution `x = m + p z`
  set G : ℚ[X] := C (m : ℚ) + C (p : ℚ) * X with hG
  set e : ℕ := cnt p Z c with he
  set ℓ : ℕ := Plc.card with hℓ
  set ρ : ℤ → ℚ := fun r => (((r - m) / p : ℤ) : ℚ) with hρ
  set T : ℚ[X] := ∏ r ∈ Plc, (X - C (ρ r)) with hT
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hPiCcomp : PiC.comp G = C ((p : ℚ) ^ ℓ) * T := by
    rw [hPiC, Polynomial.prod_comp, Finset.prod_congr rfl fun r hr => lin_comp_eq (hdiv r hr),
      Finset.prod_mul_distrib, Finset.prod_const, ← C_pow]
  have hAcomp : A.comp G = PiC.comp G * H.comp G + PiO.comp G * I.comp G := by
    conv_lhs => rw [hAHI]
    rw [add_comp, mul_comp, mul_comp]
  have hGA : GV p (A.comp G) e := by rw [hA, he, hc]; exact GV_numOf_comp κ hκ Z m
  have hGPiO : GV p (PiO.comp G) 0 := by
    rw [hPiO, Polynomial.prod_comp]
    exact (GV.prod (p := p) Plo (r := fun _ => (0 : ℚ)) fun r _ => GV_lin_comp m r).mono (by simp)
  have hGI : GV p (I.comp G) e := by
    rw [hI, Polynomial.sum_comp]
    refine GV.sum _ fun r hr => ?_
    rw [mul_comp, C_comp, Polynomial.prod_comp]
    have hprod : GV p (∏ s ∈ Plc.erase r, (X - C (s : ℚ)).comp G) ((Plc.erase r).card) := by
      exact (GV.prod (p := p) (Plc.erase r) (r := fun _ => (1 : ℚ)) fun s hs =>
        GV_lin_comp_class m s (by rw [(hmemc s (Finset.mem_of_mem_erase hs)).2, hc])).mono
        (by simp)
    have hres := VG_res κ hκ Z Pl hsep (hmemc r hr).1
    have hrc : (r : ZMod p) = c := (hmemc r hr).2
    rw [hrc, ← hPlc, ← he] at hres
    have := GV.C_mul hres hprod
    refine this.mono (le_of_eq ?_)
    rw [Finset.card_erase_of_mem hr]
    have : 1 ≤ Plc.card := Finset.card_pos.mpr ⟨r, hr⟩
    push_cast [this]; ring
  have hRHS : GV p (A.comp G - PiO.comp G * I.comp G) e :=
    hGA.sub ((hGPiO.mul hGI).mono (by simp))
  set F : ℚ[X] := C ((p : ℚ) ^ (-(e : ℤ))) * (A.comp G - PiO.comp G * I.comp G) with hF
  have hFint : GV p F 0 := by
    have := GV.C_mul (VG.primePow (p := p) (-(e : ℤ))) hRHS
    refine this.mono (le_of_eq ?_); push_cast; ring
  have hFeq : F = T * (C ((p : ℚ) ^ ((ℓ : ℤ) - e)) * H.comp G) := by
    rw [hF, show A.comp G - PiO.comp G * I.comp G = PiC.comp G * H.comp G by rw [hAcomp]; ring,
      hPiCcomp]
    have hz : (p : ℚ) ^ (-(e : ℤ)) * (p : ℚ) ^ ℓ = (p : ℚ) ^ ((ℓ : ℤ) - e) := by
      rw [← zpow_natCast, ← zpow_add₀ hp0]; ring_nf
    rw [← hz, C_mul]; ring
  have hroot : ∀ x ∈ Plc.image ρ, F.eval x = 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [hFeq, eval_mul, hT, eval_prod]
    rw [Finset.prod_eq_zero hr (by simp), zero_mul]
  have hρint : ∀ x ∈ Plc.image ρ, VG p x 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨r, _, rfl⟩ := hx
    exact VG.intCast _
  obtain ⟨S, hS, hFS⟩ := factor_roots (Plc.image ρ) hρint hFint hroot
  have hinj : Set.InjOn ρ Plc := by
    intro r hr s hs h
    have h1 : ((r - m) / p : ℤ) = (s - m) / p := by
      have h' : ((((r - m) / p : ℤ) : ℚ)) = (((s - m) / p : ℤ) : ℚ) := h
      exact_mod_cast h'
    have h2 := Int.ediv_mul_cancel (hdiv r hr)
    have h3 := Int.ediv_mul_cancel (hdiv s hs)
    have : r - m = s - m := by rw [← h2, ← h3, h1]
    omega
  rw [Finset.prod_image hinj, ← hT] at hFS
  have hT0 : T ≠ 0 := (monic_prod_of_monic _ _ fun r _ => monic_X_sub_C _).ne_zero
  have hcancel : C ((p : ℚ) ^ ((ℓ : ℤ) - e)) * H.comp G = S :=
    mul_left_cancel₀ hT0 (hFeq.symm.trans hFS)
  have hGm : G.eval 0 = (m : ℚ) := by rw [hG]; simp
  have hHm : H.eval (m : ℚ) = (p : ℚ) ^ ((e : ℤ) - ℓ) * S.eval 0 := by
    have := congrArg (eval 0) hcancel
    rw [eval_mul, eval_C, eval_comp, hGm] at this
    rw [← this, ← mul_assoc, ← zpow_add₀ hp0]; ring_nf; simp
  have hVGH : VG p (H.eval (m : ℚ)) ((e : ℚ) - ℓ) := by
    rw [hHm]
    have := (VG.primePow (p := p) ((e : ℤ) - ℓ)).mul (VG.eval_zero hS)
    simpa using this
  -- Part C: combine
  rw [hPm]
  have hβc : β ≤ (e : ℚ) - ℓ := hβ c
  refine VG.sub ((hVGH.mul hVGinvPiO).mono (by linarith)) (VG.sum _ fun r hr => ?_)
  have hres := VG_res κ hκ Z Pl hsep (hmemo r hr).1
  have := hres.mul (hVGinv r hr)
  refine this.mono ?_
  have := hβ (r : ZMod p)
  linarith



lemma natDegree_numOf_le (κ : ℚ) (Z : Multiset ℤ) : (numOf κ Z).natDegree ≤ Z.card := by
  unfold numOf
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_multiset_prod_le (t := Z.map fun ζ : ℤ => X - C (ζ : ℚ))).trans ?_
  rw [Multiset.map_map]
  have : ∀ ζ ∈ Z, ((natDegree ∘ fun ζ : ℤ => X - C (ζ : ℚ)) ζ) = 1 := fun ζ _ =>
    natDegree_X_sub_C ((ζ : ℤ) : ℚ)
  rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]

lemma padicValNat_24 (hp5 : 5 ≤ p) : padicValNat p 24 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have h1 : p ≤ 24 := Nat.le_of_dvd (by norm_num) h
  have hpr := hp.out
  interval_cases p <;> first | omega | (norm_num at hpr) | (norm_num at h)

/-- **The direct bound** `v_p^G(τ_X(g)) ≥ min_c (e_c - ℓ_c) - 4`. -/
theorem tauX_direct (hp5 : 5 ≤ p) (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (Pl : Finset ℤ)
    (hsep : Sep p Pl) (hH : ∀ r ∈ Pl, dd r < p ^ 2) (hdeg : Z.card - Pl.card + 1 < p ^ 2)
    (β : ℚ) (hβ : ∀ c : ZMod p, β ≤ (cnt p Z c : ℚ) - (plc p Pl c).card) :
    GV p (tauX (numOf κ Z) Pl) (β - 4) := by
  unfold tauX
  refine GV.add (GV.C ?_) (GV.sum _ fun r hr => ?_)
  · have hd : (polyPart (numOf κ Z) Pl).natDegree ≤ Z.card - Pl.card :=
      (natDegree_polyPart_le _ _).trans (Nat.sub_le_sub_right (natDegree_numOf_le κ Z) _)
    have h := tau_bound (p := p) hd (β := β) (fun m _ => by
      have := VG_polyPart_eval κ hκ Z Pl hsep β hβ (m : ℤ)
      simpa using this)
    have hlog : Nat.log p (Z.card - Pl.card + 1) ≤ 1 :=
      Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hdeg)
    rw [padicValNat_24 hp5] at h
    refine h.mono ?_
    have : (Nat.log p (Z.card - Pl.card + 1) : ℚ) ≤ 1 := by exact_mod_cast hlog
    push_cast; linarith
  · have hres := VG_res κ hκ Z Pl hsep hr
    have hH5 : GV p (C (H5 (dd r)) - X) (-5) :=
      (GV.C (VG_H5 (hH r hr))).sub (GV.X.mono (by norm_num))
    refine (GV.C_mul hres hH5).mono ?_
    have := hβ (r : ZMod p)
    linarith

lemma tpol_add (M M' : Multiset ℤ) : tpol (M + M') = tpol M * tpol M' := by
  simp [tpol, Multiset.map_add, Multiset.prod_add]

lemma pull_tpol (K : ℕ) (M : Multiset ℤ) :
    pull K (tpol M) = numOf ((-1 : ℚ) ^ (K + M.card)) (xroots M) := by
  unfold pull tpol numOf xroots
  rw [multiset_prod_comp, Multiset.map_map]
  simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
  have h1 : ∀ γ : ℤ, ((fun q : ℚ[X] => q.comp (-X ^ 2)) ∘ fun γ : ℤ => X + C ((γ : ℚ) ^ 2)) γ =
      C (-1 : ℚ) * ((X - C (γ : ℚ)) * (X - C ((-γ : ℤ) : ℚ))) := by
    intro γ
    simp only [Function.comp, add_comp, X_comp, C_comp]
    push_cast
    rw [map_neg, map_one, C_neg, C_pow]; ring
  rw [Multiset.map_congr rfl fun γ _ => h1 γ, Multiset.prod_map_mul, Multiset.prod_map_mul]
  simp only [Multiset.map_const', Multiset.prod_replicate, Multiset.map_map, Function.comp]
  simp only [Int.cast_zero, map_zero, sub_zero]
  rw [pow_add, map_mul, map_pow, map_pow]
  ring

/-- Number of `x`-roots in the class `c`. -/
lemma cnt_xroots (p : ℕ) (M : Multiset ℤ) (c : ZMod p) :
    cnt p (xroots M) c = (if c = 0 then 5 else 0) +
      (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
      (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card := by
  unfold cnt xroots
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add]
  congr 1
  · congr 1
    by_cases h : (0 : ZMod p) = c
    · rw [if_pos h.symm, Multiset.filter_eq_self.mpr (fun a ha => by
        rw [Multiset.eq_of_mem_replicate ha]; simpa using h)]
      simp
    · rw [if_neg (Ne.symm h), Multiset.filter_eq_nil.mpr (fun a ha => by
        rw [Multiset.eq_of_mem_replicate ha]; simpa using h)]
      simp
  · rw [Multiset.filter_map, Multiset.card_map]
    congr 1
    refine Multiset.filter_congr fun γ _ => ?_
    simp only [Function.comp, Int.cast_neg]
    constructor <;> intro h <;> [rw [← h]; rw [h]] <;> ring

/-- **Entry bound** for `μ_X(tpol M / D_K)`. -/
theorem μX_tpol_bound {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (K : ℕ) (M : Multiset ℤ)
    (hsep : Sep p (PlK K)) (hK : K < p ^ 2) (hdeg : 5 + 2 * M.card - 2 * K + 1 < p ^ 2) (β : ℚ)
    (hβ : ∀ c : ZMod p, β ≤ ((if c = 0 then 5 else 0) +
      (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
      (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card : ℕ) - (plc p (PlK K) c).card) :
    GV p (μX K (tpol M)) (β - 4) := by
  rw [muX_eq_tauX, pull_tpol]
  have hκ : VG p ((-1 : ℚ) ^ (K + M.card)) 0 := by
    rcases neg_one_pow_eq_or ℚ (K + M.card) with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  refine tauX_direct hp5 _ hκ _ _ hsep ?_ ?_ β ?_
  · intro r hr
    rw [PlK, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hr
    rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [dd_nat]; have := (Finset.mem_Icc.mp hj).2; omega
    · rw [dd_neg (Finset.mem_Icc.mp hj).1]; have := (Finset.mem_Icc.mp hj).2; omega
  · have : (xroots M).card = 5 + 2 * M.card := by
      simp [xroots]; ring
    rw [this, card_PlK]; exact hdeg
  · intro c
    rw [cnt_xroots]; exact hβ c
end Apery

end Port0

open Finset Polynomial in
/-- The platform target `Apery.muX_tpol_bound`, restated at top level as `solution`. -/
theorem solution {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (K : ℕ) (M : Multiset ℤ)
    (hsep : Apery.Sep p (Apery.PlK K)) (hK : K < p ^ 2) (hdeg : 5 + 2 * M.card - 2 * K + 1 < p ^ 2)
    (β : ℚ)
    (hβ : ∀ c : ZMod p, β ≤ ((if c = 0 then 5 else 0) +
      (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
      (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card : ℕ) - (Apery.plc p (Apery.PlK K) c).card) :
    Apery.GV p (Apery.μX K (Apery.tpol M)) (β - 4) :=
  Apery.μX_tpol_bound hp5 K M hsep hK hdeg β hβ
