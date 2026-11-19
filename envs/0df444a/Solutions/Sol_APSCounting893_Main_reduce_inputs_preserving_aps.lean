-- Prove2me | solution 1 for APSCounting893.Main.reduce_inputs_preserving_aps
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:09:28.09268+00:00
-- url     : https://prove2.me/submissions/898f4522-2c3a-4d47-824b-a973fd061351

import Mathlib
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Tactic
import Theorems.Thm_APSCounting893_Main_input_reduction_nonvanishing_certificate
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial Finset Fintype
namespace APSCounting893.Main

open Classical in
lemma finite_grid_success_lower_bound {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (hp : p ≠ 0) (B : Finset R) (hB : B.Nonempty)
    (D : ℕ) (hD : p.totalDegree ≤ D) (Good : (Fin n → R) → Prop)
    (hgood : ∀ x ∈ piFinset (fun _ : Fin n => B), MvPolynomial.eval x p ≠ 0 → Good x) :
    ((piFinset (fun _ : Fin n => B)).filter Good).card / (B.card ^ n : ℝ) ≥
      1 - (D : ℝ) / B.card := by
  classical
  have hs := MvPolynomial.schwartz_zippel_totalDegree hp B
  have hsR : (((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p = 0)).card : ℝ) /
      (B.card ^ n : ℝ) ≤ (p.totalDegree : ℝ) / B.card := by
    have hh := (NNRat.cast_le (K := ℝ)).mpr hs
    simpa only [NNRat.cast_div,NNRat.cast_pow,NNRat.cast_natCast] using hh
  have hcard : (piFinset (fun _ : Fin n => B)).card = B.card ^ n := by simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := piFinset (fun _ : Fin n => B)) (p := fun x => MvPolynomial.eval x p = 0)
  have hle : ((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p ≠ 0)).card ≤
      ((piFinset (fun _ : Fin n => B)).filter Good).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hx,hne⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx,hgood x hx hne⟩
  have hden : (0 : ℝ) < B.card ^ n := by positivity
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hsplitR :
      (((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p = 0)).card : ℝ) +
      (((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p ≠ 0)).card : ℝ) =
        (B.card ^ n : ℝ) := by exact_mod_cast (hsplit.trans hcard)
  have hleR :
      (((piFinset (fun _ : Fin n => B)).filter (fun x => MvPolynomial.eval x p ≠ 0)).card : ℝ) ≤
      (((piFinset (fun _ : Fin n => B)).filter Good).card : ℝ) := by exact_mod_cast hle
  have hdeg : (p.totalDegree : ℝ) / B.card ≤ (D : ℝ) / B.card := by gcongr
  have hbound := hsR.trans hdeg
  apply (le_div_iff₀ hden).mpr
  have hh := (div_le_iff₀ hden).mp hbound
  have htmp : (1-(D : ℝ)/B.card)*(B.card^n : ℝ) =
      (B.card^n : ℝ) - ((D : ℝ)/B.card)*(B.card^n : ℝ) := by ring
  rw [htmp]
  linarith

end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial Finset Fintype
namespace APSCounting893.Main

open Classical in
lemma finite_grid_subtype_success_lower_bound {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (hp : p ≠ 0) (B : Finset R) (hB : B.Nonempty)
    (D : ℕ) (hD : p.totalDegree ≤ D) (Good : (Fin n → R) → Prop)
    (hgood : ∀ x ∈ piFinset (fun _ : Fin n => B), MvPolynomial.eval x p ≠ 0 → Good x) :
    (Set.ncard {s : Fin n → {q // q ∈ B} | Good (fun j => (s j).val)} : ℝ) /
      (Fintype.card (Fin n → {q // q ∈ B}) : ℝ) ≥ 1 - (D : ℝ) / B.card := by
  classical
  have hc : Set.ncard {s : Fin n → {q // q ∈ B} | Good (fun j => (s j).val)} =
      ((piFinset (fun _ : Fin n => B)).filter Good).card := by
    calc
      _ = Set.ncard {x : Fin n → R | x ∈ piFinset (fun _ : Fin n => B) ∧ Good x} := by
        apply Set.ncard_congr (fun s _ j => (s j).val)
        · intro s hs
          exact ⟨mem_piFinset.mpr (fun j => (s j).2),hs⟩
        · intro s t hs ht he
          funext j
          exact Subtype.ext (congrFun he j)
        · intro x hx
          let s : Fin n → {q // q ∈ B} := fun j => ⟨x j,mem_piFinset.mp hx.1 j⟩
          exact ⟨s,hx.2,rfl⟩
      _ = _ := by
        have he : {x : Fin n → R | x ∈ piFinset (fun _ : Fin n => B) ∧ Good x} =
            (((piFinset (fun _ : Fin n => B)).filter Good : Finset _) : Set _) := by ext x; simp
        rw [he,Set.ncard_coe_finset]
  have htotal : Fintype.card (Fin n → {q // q ∈ B}) = B.card ^ n := by simp
  rw [hc,htotal]
  simpa only [Nat.cast_pow] using finite_grid_success_lower_bound p hp B hB D hD Good hgood

end APSCounting893.Main
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial Finset Fintype
namespace APSCounting893.Main

open Classical in
lemma finite_grid_embedding_success_lower_bound {R K : Type} [CommRing R] [CommRing K] [IsDomain K]
    {n : ℕ} (f : R →+* K) (hf : Function.Injective f)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (B : Finset R) (hB : B.Nonempty)
    (D : ℕ) (hD : p.totalDegree ≤ D) (Good : (Fin n → R) → Prop)
    (hgood : ∀ x ∈ piFinset (fun _ : Fin n => B),
      MvPolynomial.eval (fun j => f (x j)) p ≠ 0 → Good x) :
    (Set.ncard {s : Fin n → {q // q ∈ B} | Good (fun j => (s j).val)} : ℝ) /
      (Fintype.card (Fin n → {q // q ∈ B}) : ℝ) ≥ 1 - (D : ℝ) / B.card := by
  classical
  let B' := B.image f
  let Good' : (Fin n → K) → Prop := fun y => ∃ x : Fin n → R,
    (∀ j, x j ∈ B) ∧ (fun j => f (x j)) = y ∧ Good x
  have hgood' : ∀ y ∈ piFinset (fun _ : Fin n => B'), MvPolynomial.eval y p ≠ 0 → Good' y := by
    intro y hy hpy
    have hex (j : Fin n) : ∃ x ∈ B, f x = y j := mem_image.mp (mem_piFinset.mp hy j)
    choose x hx hfx using hex
    have he : (fun j => f (x j)) = y := funext hfx
    exact ⟨x,hx,he,hgood x (mem_piFinset.mpr hx) (he ▸ hpy)⟩
  have hs := finite_grid_subtype_success_lower_bound p hp B' (hB.image f) D hD Good' hgood'
  have hcard : B'.card = B.card := Finset.card_image_of_injective _ hf
  have hncard : Set.ncard {s : Fin n → {q // q ∈ B} | Good (fun j => (s j).val)} =
      Set.ncard {s : Fin n → {q // q ∈ B'} | Good' (fun j => (s j).val)} := by
    apply Set.ncard_congr (fun s _ j => ⟨f (s j).1,mem_image_of_mem f (s j).2⟩)
    · intro s hs
      exact ⟨fun j => (s j).1,fun j => (s j).2,rfl,hs⟩
    · intro s t hs ht he
      funext j
      apply Subtype.ext
      apply hf
      exact congrArg Subtype.val (congrFun he j)
    · intro t ht
      obtain ⟨x,hx,he,hgoodx⟩ := ht
      let s : Fin n → {q // q ∈ B} := fun j => ⟨x j,hx j⟩
      refine ⟨s,hgoodx,?_⟩
      funext j
      exact Subtype.ext (congrFun he j)
  have htotal : Fintype.card (Fin n → {q // q ∈ B'}) = Fintype.card (Fin n → {q // q ∈ B}) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,hcard]
  rw [← hncard,htotal,hcard] at hs
  exact hs

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
namespace APSCounting893.Main

lemma sampled_ncard_reindex {σ τ R : Type} (e : σ ≃ τ) (B : Finset R)
    (Good : (σ → R) → Prop) :
    Set.ncard {s : σ → {q // q ∈ B} | Good (fun j => (s j).val)} =
      Set.ncard {s : τ → {q // q ∈ B} | Good (fun j => (s (e j)).val)} := by
  apply Set.ncard_congr (fun s _ j => s (e.symm j))
  · intro s hs
    simpa only [Set.mem_setOf_eq,e.symm_apply_apply] using hs
  · intro s t hs ht he
    funext j
    have hh := congrFun he (e j)
    simpa only [e.symm_apply_apply] using hh
  · intro t ht
    exact ⟨fun j => t (e j),ht,by funext j; simp⟩

open Classical in
lemma sampled_card_reindex {σ τ R : Type} [Fintype σ] [Fintype τ] (e : σ ≃ τ) (B : Finset R) :
    Fintype.card (σ → {q // q ∈ B}) = Fintype.card (τ → {q // q ∈ B}) := by
  simp only [Fintype.card_fun,Fintype.card_congr e]

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
open APSCounting893.Main
theorem solution (n m r : ℕ) (F : PolynomialMap ℂ n m)
    (hnonconstant : ∀ i, 0 < (F i).totalDegree)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (hr : 1 ≤ r) (hrm : r < m) (B : Finset ℚ) (hB : B.Nonempty) :
    reductionSuccessProbability (r := r) F B ≥
      1 - ((2 * (n - r) * inputDegree F ^ m + (r + 1) * inputDegree F ^ r : ℕ) : ℝ) /
        (B.card : ℝ) := by
  classical
  obtain ⟨p,hp,hdegree,hgood⟩ := input_reduction_nonvanishing_certificate n m r F hnonconstant hdim hr hrm
  let e := Fintype.equivFin (ReductionLabels n m r)
  let Good : (Fin (Fintype.card (ReductionLabels n m r)) → ℚ) → Prop :=
    fun x => ReductionSucceeds F (fun j => x (e j))
  have hs := finite_grid_embedding_success_lower_bound (algebraMap ℚ ℂ)
    (algebraMap ℚ ℂ).injective p hp B hB
    (2*(n-r)*inputDegree F^m+(r+1)*inputDegree F^r) hdegree Good (by
      intro x hx hpx
      apply hgood (fun j => x (e j))
      simpa [e] using hpx)
  have hc := sampled_ncard_reindex e B (ReductionSucceeds F)
  have ht := sampled_card_reindex e B
  unfold reductionSuccessProbability
  simp only [Fintype.card_eq_nat_card] at ht hs ⊢
  rw [hc,ht]
  exact hs

end Component_4

open APSCounting893.Main

