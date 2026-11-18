-- Prove2me | solution 1 for AaronsonAmbainis.Short.certificate_influence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-17T15:33:38.357375+00:00
-- url     : https://prove2.me/submissions/4534e960-48bf-44cc-aa20-1d80ffa36f47

import Mathlib
import Definitions.Def_AaronsonAmbainis_Short
import Theorems.Thm_AaronsonAmbainis_Short_det_core
open AaronsonAmbainis
open Finset

namespace AASolCert

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Point of the subcube through `a` with free coordinates `J`. -/
def glue (J : Finset ι) (a : Cube ι) (u : Cube ↥J) : Cube ι :=
  fun i => if h : i ∈ J then u ⟨i, h⟩ else a i

def restr (J : Finset ι) (a : Cube ι) : Cube ↥J := fun i => a i.1

omit [Fintype ι] in
lemma glue_glue_restr (J : Finset ι) (a : Cube ι) (u : Cube ↥J) :
    glue J (glue J a u) (restr J a) = a := by
  funext i
  by_cases h : i ∈ J <;> simp [glue, restr, h]

omit [Fintype ι] in
lemma restr_glue (J : Finset ι) (a : Cube ι) (u : Cube ↥J) :
    restr J (glue J a u) = u := by
  funext i
  obtain ⟨i, h⟩ := i
  simp [glue, restr, h]

omit [Fintype ι] in
lemma glue_flip (J : Finset ι) (a : Cube ι) (u : Cube ↥J) (S : Finset ↥J) :
    glue J a (flipSet u S)
      = flipSet (glue J a u) (S.map (Function.Embedding.subtype _)) := by
  funext i
  by_cases h : i ∈ J <;> simp [glue, flipSet, h]

omit [Fintype ι] in
lemma glue_flip_single (J : Finset ι) (a : Cube ι) (u : Cube ↥J) (i : ↥J) :
    glue J a (flipSet u {i}) = flipSet (glue J a u) {i.1} := by
  rw [glue_flip, Finset.map_singleton]
  rfl

omit [Fintype ι] in
lemma glue_antipode (J : Finset ι) (a : Cube ι) (u : Cube ↥J) :
    glue J a (antipode u) = flipSet (glue J a u) J := by
  funext i
  by_cases h : i ∈ J <;> simp [glue, flipSet, antipode, h]

lemma diff_flip (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [diffSet, flipSet, h]

lemma flip_diff {κ : Type} [Fintype κ] [DecidableEq κ] (x y : Cube κ) :
    flipSet x (diffSet x y) = y := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [flipSet, diffSet, hx, hy]

lemma flip_bij (x : Cube ι) : Function.Bijective (fun J : Finset ι => flipSet x J) :=
  Function.bijective_iff_has_inverse.2
    ⟨fun y => diffSet x y, fun J => diff_flip x J, fun y => flip_diff x y⟩

omit [Fintype ι] in
lemma flip_flip (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by
  funext i
  by_cases h : i ∈ S <;> simp [flipSet, h]

/-- Averaging over all subcubes with free coordinates `J`. -/
lemma sum_glue (J : Finset ι) (F : Cube ι → ℝ) :
    ∑ a : Cube ι, ∑ u : Cube ↥J, F (glue J a u) = 2 ^ J.card * ∑ x, F x := by
  let e : (Cube ι × Cube ↥J) ≃ (Cube ι × Cube ↥J) :=
    { toFun := fun p => (glue J p.1 p.2, restr J p.1)
      invFun := fun p => (glue J p.1 p.2, restr J p.1)
      left_inv := fun p => Prod.ext (glue_glue_restr J p.1 p.2) (restr_glue J p.1 p.2)
      right_inv := fun p => Prod.ext (glue_glue_restr J p.1 p.2) (restr_glue J p.1 p.2) }
  have hc : Fintype.card (Cube ↥J) = 2 ^ J.card := by simp [Cube]
  calc ∑ a : Cube ι, ∑ u : Cube ↥J, F (glue J a u)
      = ∑ p : Cube ι × Cube ↥J, F (e p).1 :=
        (Fintype.sum_prod_type' (fun a u => F (glue J a u))).symm
    _ = ∑ p : Cube ι × Cube ↥J, F p.1 := Equiv.sum_comp e (fun p => F p.1)
    _ = ∑ x : Cube ι, ∑ _v : Cube ↥J, F x := Fintype.sum_prod_type' (fun x _ => F x)
    _ = 2 ^ J.card * ∑ x, F x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
        push_cast
        ring

lemma sum_powerset (f : ι → ℝ) :
    2 * ∑ J : Finset ι, ∑ i ∈ J, f i = 2 ^ Fintype.card ι * ∑ i, f i := by
  have h : ∑ J : Finset ι, ∑ i ∈ Jᶜ, f i = ∑ J : Finset ι, ∑ i ∈ J, f i :=
    Fintype.sum_bijective (fun J : Finset ι => Jᶜ) compl_bijective
      (fun J => ∑ i ∈ Jᶜ, f i) (fun J => ∑ i ∈ J, f i) (fun _ => rfl)
  have h2 : ∑ J : Finset ι, (∑ i ∈ J, f i + ∑ i ∈ Jᶜ, f i) = ∑ _J : Finset ι, ∑ i, f i :=
    Finset.sum_congr rfl fun J _ => Finset.sum_add_sum_compl J f
  rw [Finset.sum_add_distrib, h] at h2
  rw [two_mul, h2, Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]
  push_cast
  ring

lemma card_sens (G : Cube ι → Bool) (i : ι) :
    ((univ.filter fun x : Cube ι => G (flipSet x {i}) ≠ G x).card : ℝ)
      = 2 * (bdry G i : ℝ) := by
  rw [bdry, Finset.natCast_card_filter, Finset.natCast_card_filter]
  have pt : ∀ x : Cube ι, (if G (flipSet x {i}) ≠ G x then (1 : ℝ) else 0)
      = (if G x = true ∧ G (flipSet x {i}) = false then (1 : ℝ) else 0)
        + (if G (flipSet x {i}) = true ∧ G (flipSet (flipSet x {i}) {i}) = false
            then (1 : ℝ) else 0) := by
    intro x
    rw [flip_flip]
    cases h1 : G x <;> cases h2 : G (flipSet x {i}) <;> simp
  have inv : Function.Involutive (fun x : Cube ι => flipSet x {i}) := fun x => flip_flip x {i}
  have h : ∑ x : Cube ι, (if G (flipSet x {i}) = true ∧ G (flipSet (flipSet x {i}) {i}) = false
            then (1 : ℝ) else 0)
      = ∑ x : Cube ι, (if G x = true ∧ G (flipSet x {i}) = false then (1 : ℝ) else 0) :=
    Fintype.sum_bijective (fun x : Cube ι => flipSet x {i}) inv.bijective _ _ (fun _ => rfl)
  rw [Finset.sum_congr rfl fun x _ => pt x, Finset.sum_add_distrib, h]
  ring

lemma two_bdry (G : Cube ι → Bool) (i : ι) :
    2 * (bdry G i : ℝ) = 2 ^ Fintype.card ι * infl G i := by
  rw [infl, card_sens, mul_div_cancel₀ _ (by positivity)]

section core

variable (G : Cube ι → Bool) (c : Cube ι → ι → ℝ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
  (H : Cube ι → Finset ι) (M : Cube ι → Cube ι → Prop) [∀ x y, Decidable (M x y)]
  (hM : ∀ x y, M x y → G x = true ∧ G y = false ∧ IsRow G x (c x) ∧ IsRow G y (c y) ∧
    ∑ i ∈ H y, c x i < 1 ∧ ∀ i, i ∉ H y → c y i ≤ w i)

include hw hM

omit [Fintype ι] in
/-- The subcube inequality applied to the subcube through `a` with free coordinates `J`. -/
lemma core (J : Finset ι) (a : Cube ι) :
    ((univ.filter fun u : Cube ↥J => M (glue J a u) (flipSet (glue J a u) J)).card : ℝ)
      ≤ ∑ i : ↥J, w i.1 * (bdry (fun u : Cube ↥J => G (glue J a u)) i : ℝ) := by
  refine AaronsonAmbainis.Short.det_core (fun u : Cube ↥J => G (glue J a u)) (fun i => w i.1)
    (fun i => hw i.1) (univ.filter fun u : Cube ↥J => M (glue J a u) (flipSet (glue J a u) J))
    (fun u => univ.filter fun i : ↥J => i.1 ∈ H (flipSet (glue J a u) J)) ?_ ?_
  · intro u hu S hS
    rw [Finset.mem_filter] at hu
    obtain ⟨hGx, -, hrx, -, hlt, -⟩ := hM _ _ hu.2
    show G (glue J a (flipSet u S)) = true
    rw [glue_flip]
    by_contra hne
    have hne' : G (flipSet (glue J a u) (S.map (Function.Embedding.subtype _))) ≠ G (glue J a u) := by
      rw [hGx]; exact hne
    have h1 := hrx.2 _ hne'
    have h2 : ∑ j ∈ S.map (Function.Embedding.subtype _), c (glue J a u) j
        ≤ ∑ j ∈ H (flipSet (glue J a u) J), c (glue J a u) j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hrx.1 j)
      intro j hj
      rw [Finset.mem_map] at hj
      obtain ⟨k, hk, rfl⟩ := hj
      exact (Finset.mem_filter.1 (hS hk)).2
    linarith
  · intro u hu z hz hK
    rw [Finset.mem_filter] at hu
    obtain ⟨-, hGy, -, hry, -, hle⟩ := hM _ _ hu.2
    have hz' : G (glue J a z) = true := hz
    have hZ : flipSet (flipSet (glue J a u) J)
        ((diffSet (antipode u) z).map (Function.Embedding.subtype _)) = glue J a z := by
      rw [← glue_antipode, ← glue_flip, flip_diff]
    have hne : G (flipSet (flipSet (glue J a u) J)
        ((diffSet (antipode u) z).map (Function.Embedding.subtype _)))
          ≠ G (flipSet (glue J a u) J) := by
      rw [hZ, hGy, hz']; simp
    have h1 := hry.2 _ hne
    rw [Finset.sum_map] at h1
    refine h1.trans (Finset.sum_le_sum fun k hk => hle _ ?_)
    intro hkH
    have hk2 : k ∈ diffSet u z := hK (Finset.mem_filter.2 ⟨Finset.mem_univ _, hkH⟩)
    have hk' : (!(u k)) ≠ z k := (Finset.mem_filter.1 hk).2
    have hk2' : u k ≠ z k := (Finset.mem_filter.1 hk2).2
    have hb : ∀ b d : Bool, (!b) ≠ d → b ≠ d → False := by decide
    exact hb _ _ hk' hk2'

/-- For a fixed direction set `J`, count the marked pairs `(x, x ⊕ J)`. -/
lemma perJ (J : Finset ι) :
    ((univ.filter fun x : Cube ι => M x (flipSet x J)).card : ℝ)
      ≤ ∑ i ∈ J, w i * (bdry G i : ℝ) := by
  have hpos : (0 : ℝ) < 2 ^ J.card := by positivity
  have key : (2 : ℝ) ^ J.card * ((univ.filter fun x : Cube ι => M x (flipSet x J)).card : ℝ)
      ≤ 2 ^ J.card * ∑ i ∈ J, w i * (bdry G i : ℝ) := by
    calc (2 : ℝ) ^ J.card * ((univ.filter fun x : Cube ι => M x (flipSet x J)).card : ℝ)
        = ∑ a : Cube ι, ∑ u : Cube ↥J,
            (if M (glue J a u) (flipSet (glue J a u) J) then (1 : ℝ) else 0) := by
          rw [Finset.natCast_card_filter]
          exact (sum_glue J (fun x => if M x (flipSet x J) then (1 : ℝ) else 0)).symm
      _ ≤ ∑ a : Cube ι, ∑ i : ↥J, w i.1 * ∑ u : Cube ↥J,
            (if G (glue J a u) = true ∧ G (flipSet (glue J a u) {i.1}) = false
              then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h := core G c w hw H M hM J a
          rw [Finset.natCast_card_filter] at h
          refine h.trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [bdry, Finset.natCast_card_filter]
          simp only [glue_flip_single]
      _ = ∑ i : ↥J, w i.1 * (2 ^ J.card * (bdry G i.1 : ℝ)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, bdry, Finset.natCast_card_filter]
          exact congrArg (fun t => w i.1 * t) (sum_glue J
            (fun x => if G x = true ∧ G (flipSet x {i.1}) = false then (1 : ℝ) else 0))
      _ = 2 ^ J.card * ∑ i ∈ J, w i * (bdry G i : ℝ) := by
          rw [Finset.sum_coe_sort J (fun i => w i * (2 ^ J.card * (bdry G i : ℝ))),
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  exact le_of_mul_le_mul_left key hpos

lemma total :
    2 * ∑ x : Cube ι, ∑ y : Cube ι, (if M x y then (1 : ℝ) else 0)
      ≤ 2 ^ Fintype.card ι * ∑ i, w i * (bdry G i : ℝ) := by
  have e1 : ∑ x : Cube ι, ∑ y : Cube ι, (if M x y then (1 : ℝ) else 0)
      = ∑ J : Finset ι, ((univ.filter fun x : Cube ι => M x (flipSet x J)).card : ℝ) := by
    have hb : ∀ x : Cube ι, ∑ J : Finset ι, (if M x (flipSet x J) then (1 : ℝ) else 0)
        = ∑ y : Cube ι, (if M x y then (1 : ℝ) else 0) := fun x =>
      Fintype.sum_bijective (fun J : Finset ι => flipSet x J) (flip_bij x)
        (fun J : Finset ι => if M x (flipSet x J) then (1 : ℝ) else 0)
        (fun y : Cube ι => if M x y then (1 : ℝ) else 0) (fun _ => rfl)
    calc ∑ x : Cube ι, ∑ y : Cube ι, (if M x y then (1 : ℝ) else 0)
        = ∑ x : Cube ι, ∑ J : Finset ι, (if M x (flipSet x J) then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun x _ => (hb x).symm
      _ = ∑ J : Finset ι, ∑ x : Cube ι, (if M x (flipSet x J) then (1 : ℝ) else 0) :=
          Finset.sum_comm
      _ = ∑ J : Finset ι, ((univ.filter fun x : Cube ι => M x (flipSet x J)).card : ℝ) :=
          Finset.sum_congr rfl fun J _ => (Finset.natCast_card_filter _ _).symm
  have hs : ∑ J : Finset ι, ((univ.filter fun x : Cube ι => M x (flipSet x J)).card : ℝ)
      ≤ ∑ J : Finset ι, ∑ i ∈ J, w i * (bdry G i : ℝ) :=
    Finset.sum_le_sum fun J _ => perJ G c w hw H M hM J
  rw [e1, ← sum_powerset (fun i => w i * (bdry G i : ℝ))]
  exact mul_le_mul_of_nonneg_left hs (by norm_num)

end core

lemma main (G : Cube ι → Bool) (c : Cube ι → ι → ℝ) (U0 U1 : Finset (Cube ι)) (γ0 γ1 : ℝ)
    (hγ0 : 0 < γ0) (hγ1 : 0 < γ1)
    (h0 : ∀ x ∈ U0, G x = false ∧ IsRow G x (c x) ∧ ∑ j, c x j ≤ γ0)
    (h1 : ∀ x ∈ U1, G x = true ∧ IsRow G x (c x) ∧ ∑ j, c x j ≤ γ1)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : ∀ j, infl G j ≤ τ) (hU1 : U1.Nonempty) :
    ((U0.card : ℝ) / 2 ^ Fintype.card ι) * ((U1.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ γ0 * γ1 * τ := by
  have hN1 : (0 : ℝ) < U1.card := by exact_mod_cast hU1.card_pos
  obtain ⟨w, hwdef⟩ : ∃ w : ι → ℝ, ∀ i, w i = 2 * γ0 / U1.card * ∑ x ∈ U1, c x i :=
    ⟨_, fun _ => rfl⟩
  have hσ : ∀ i, 0 ≤ ∑ x ∈ U1, c x i :=
    fun i => Finset.sum_nonneg fun x hx => (h1 x hx).2.1.1 i
  have hw : ∀ i, 0 ≤ w i := fun i => by
    rw [hwdef]; exact mul_nonneg (by positivity) (hσ i)
  obtain ⟨H, hH⟩ : ∃ H : Cube ι → Finset ι, ∀ y i, i ∈ H y ↔ w i < c y i :=
    ⟨fun y => univ.filter fun i => w i < c y i, by simp⟩
  have hT := total G c w hw H (fun x y => x ∈ U1 ∧ y ∈ U0 ∧ ∑ i ∈ H y, c x i < 1) (by
    rintro x y ⟨hx, hy, hlt⟩
    exact ⟨(h1 x hx).1, (h0 y hy).1, (h1 x hx).2.1, (h0 y hy).2.1, hlt,
      fun i hi => not_lt.1 (fun h => hi ((hH y i).2 h))⟩)
  have hsumw : ∑ i, w i ≤ 2 * γ0 * γ1 := by
    have hs : ∑ i, ∑ x ∈ U1, c x i ≤ U1.card * γ1 := by
      rw [Finset.sum_comm]
      calc ∑ x ∈ U1, ∑ i, c x i ≤ ∑ _x ∈ U1, γ1 := Finset.sum_le_sum fun x hx => (h1 x hx).2.2
        _ = U1.card * γ1 := by rw [Finset.sum_const, nsmul_eq_mul]
    calc ∑ i, w i = 2 * γ0 / U1.card * ∑ i, ∑ x ∈ U1, c x i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hwdef i
      _ ≤ 2 * γ0 / U1.card * (U1.card * γ1) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * γ0 * γ1 := by field_simp
  have hup : ∑ i, w i * (bdry G i : ℝ)
      ≤ 2 ^ Fintype.card ι * τ * (γ0 * γ1) := by
    have hb : ∀ i, (bdry G i : ℝ) ≤ 2 ^ Fintype.card ι * τ / 2 := by
      intro i
      have h3 : (2 : ℝ) ^ Fintype.card ι * infl G i ≤ 2 ^ Fintype.card ι * τ :=
        mul_le_mul_of_nonneg_left (hτ i) (by positivity)
      linarith [two_bdry G i]
    calc ∑ i, w i * (bdry G i : ℝ) ≤ ∑ i, w i * (2 ^ Fintype.card ι * τ / 2) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i)
      _ = (2 ^ Fintype.card ι * τ / 2) * ∑ i, w i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ ≤ (2 ^ Fintype.card ι * τ / 2) * (2 * γ0 * γ1) :=
          mul_le_mul_of_nonneg_left hsumw (by positivity)
      _ = _ := by ring
  have hlow : (U0.card : ℝ) * U1.card / 2
      ≤ ∑ x : Cube ι, ∑ y : Cube ι,
          (if x ∈ U1 ∧ y ∈ U0 ∧ ∑ i ∈ H y, c x i < 1 then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    have hy : ∀ y ∈ U0, (U1.card : ℝ) / 2
        ≤ ∑ x : Cube ι, (if x ∈ U1 ∧ y ∈ U0 ∧ ∑ i ∈ H y, c x i < 1 then (1 : ℝ) else 0) := by
      intro y hy
      have hs0 : ∀ x ∈ U1, 0 ≤ ∑ i ∈ H y, c x i :=
        fun x hx => Finset.sum_nonneg fun i _ => (h1 x hx).2.1.1 i
      have hsum : ∑ x ∈ U1, ∑ i ∈ H y, c x i ≤ (U1.card : ℝ) / 2 := by
        rw [Finset.sum_comm]
        obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (U1.card : ℝ) / (2 * γ0) := ⟨_, rfl⟩
        have hq : 0 ≤ q := by rw [hqdef]; positivity
        have hqγ : q * γ0 = (U1.card : ℝ) / 2 := by rw [hqdef]; field_simp
        have e : ∀ i, ∑ x ∈ U1, c x i = q * w i := by
          intro i; rw [hwdef, hqdef]; field_simp
        calc ∑ i ∈ H y, ∑ x ∈ U1, c x i = ∑ i ∈ H y, q * w i :=
              Finset.sum_congr rfl fun i _ => e i
          _ ≤ ∑ i ∈ H y, q * c y i :=
              Finset.sum_le_sum fun i hi =>
                mul_le_mul_of_nonneg_left (le_of_lt ((hH y i).1 hi)) hq
          _ = q * ∑ i ∈ H y, c y i := by rw [Finset.mul_sum]
          _ ≤ q * γ0 :=
              mul_le_mul_of_nonneg_left
                (le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  fun i _ _ => (h0 y hy).2.1.1 i) (h0 y hy).2.2) hq
          _ = (U1.card : ℝ) / 2 := hqγ
      calc (U1.card : ℝ) / 2 ≤ ∑ x ∈ U1, (1 - ∑ i ∈ H y, c x i) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]; linarith
        _ ≤ ∑ x ∈ U1, (if x ∈ U1 ∧ y ∈ U0 ∧ ∑ i ∈ H y, c x i < 1 then (1 : ℝ) else 0) :=
            Finset.sum_le_sum fun x hx => by
              have := hs0 x hx
              by_cases hlt : ∑ i ∈ H y, c x i < 1
              · rw [if_pos ⟨hx, hy, hlt⟩]; linarith
              · rw [if_neg (fun h => hlt h.2.2)]; linarith
        _ ≤ ∑ x : Cube ι, (if x ∈ U1 ∧ y ∈ U0 ∧ ∑ i ∈ H y, c x i < 1 then (1 : ℝ) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun x _ _ => by split_ifs <;> norm_num)
    calc (U0.card : ℝ) * U1.card / 2 = ∑ _y ∈ U0, (U1.card : ℝ) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ y ∈ U0, ∑ x : Cube ι,
            (if x ∈ U1 ∧ y ∈ U0 ∧ ∑ i ∈ H y, c x i < 1 then (1 : ℝ) else 0) :=
          Finset.sum_le_sum hy
      _ ≤ ∑ y : Cube ι, ∑ x : Cube ι,
            (if x ∈ U1 ∧ y ∈ U0 ∧ ∑ i ∈ H y, c x i < 1 then (1 : ℝ) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun y _ _ => Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num)
  have hp : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hup' := mul_le_mul_of_nonneg_left hup hp.le
  have hfin : (U0.card : ℝ) * U1.card
      ≤ γ0 * γ1 * τ * (2 ^ Fintype.card ι * 2 ^ Fintype.card ι) := by
    calc (U0.card : ℝ) * U1.card = 2 * ((U0.card : ℝ) * U1.card / 2) := by ring
      _ ≤ 2 * ∑ x : Cube ι, ∑ y : Cube ι,
          (if x ∈ U1 ∧ y ∈ U0 ∧ ∑ i ∈ H y, c x i < 1 then (1 : ℝ) else 0) :=
          mul_le_mul_of_nonneg_left hlow (by norm_num)
      _ ≤ _ := hT
      _ ≤ _ := hup'
      _ = _ := by ring
  rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
  exact hfin

end AASolCert

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Cube ι → Bool) (c : Cube ι → ι → ℝ) (U0 U1 : Finset (Cube ι)) (γ0 γ1 : ℝ)
    (hγ0 : 0 < γ0) (hγ1 : 0 < γ1)
    (h0 : ∀ x ∈ U0, G x = false ∧ IsRow G x (c x) ∧ ∑ j, c x j ≤ γ0)
    (h1 : ∀ x ∈ U1, G x = true ∧ IsRow G x (c x) ∧ ∑ j, c x j ≤ γ1)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : ∀ j, infl G j ≤ τ) :
    ((U0.card : ℝ) / 2 ^ Fintype.card ι) * ((U1.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ γ0 * γ1 * τ := by
  rcases U1.eq_empty_or_nonempty with hU1 | hU1
  · rw [hU1, Finset.card_empty, Nat.cast_zero, zero_div, mul_zero]
    positivity
  · exact AASolCert.main G c U0 U1 γ0 γ1 hγ0 hγ1 h0 h1 τ hτ0 hτ hU1
