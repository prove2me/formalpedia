-- Prove2me | solution 1 for AlgebraicPCSP.BLP.remark_7_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:48:13.057113+00:00
-- url     : https://prove2.me/submissions/ea67b9cf-67bf-4a2a-8c14-d7c56c376c80

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_BLP_Qconv
import Definitions.Def_AlgebraicPCSP_BLP_LP

open PCSPBLPAff.Symmetric

open AlgebraicPCSP.BLP in
theorem solution {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) {n : ℕ} (e : Fin n ≃ A) (m : τ → ℕ)
    (eR : (R : τ) → Fin (m R) ≃ 𝔸.rel R) :
    ∃ h : LPDist A ≃ {f // f ∈ convexMinion.mem n},
      (∀ ϕ : LPDist A, (h ϕ).val = fun x : Fin n → ℚ => ∑ i, ϕ.val (e i) * x i) ∧
      ∀ (R : τ) (t : Fin (ar R) → LPDist A),
        t ∈ (LP 𝔸).rel R ↔
          (fun i => h (t i)) ∈ (AlgebraicPCSP.Theory.freeStructure convexMinion 𝔸 e m eR).rel R := by
  classical
  have le1 : ∀ ϕ : LPDist A, ∀ a, ϕ.val a ≤ 1 := by
    intro ϕ a
    calc ϕ.val a ≤ ∑ b, ϕ.val b :=
          Finset.single_le_sum (f := ϕ.val) (fun b _ => ϕ.2.1 b) (Finset.mem_univ a)
      _ = 1 := ϕ.2.2
  let toF : LPDist A → {f // f ∈ convexMinion.mem n} := fun ϕ =>
    ⟨fun x => ∑ i, ϕ.val (e i) * x i, ⟨fun i => ϕ.val (e i), fun i => ⟨ϕ.2.1 _, le1 ϕ _⟩,
      by rw [Equiv.sum_comp e ϕ.val]; exact ϕ.2.2, rfl⟩⟩
  have heval : ∀ ϕ : LPDist A, ∀ a, (toF ϕ).val (Pi.single (e.symm a) 1) = ϕ.val a := by
    intro ϕ a
    simp [toF, Pi.single_apply]
  have hinj : Function.Injective toF := by
    intro ϕ ψ hϕψ
    apply Subtype.ext
    funext a
    rw [← heval ϕ a, ← heval ψ a, hϕψ]
  have hsurj : Function.Surjective toF := by
    rintro ⟨f, α, hα01, hαs, rfl⟩
    refine ⟨⟨fun a => α (e.symm a), fun a => (hα01 _).1, ?_⟩, ?_⟩
    · rw [Equiv.sum_comp e.symm α]; exact hαs
    · apply Subtype.ext
      funext x
      simp [toF]
  let h := Equiv.ofBijective toF ⟨hinj, hsurj⟩
  refine ⟨h, fun ϕ => rfl, ?_⟩
  intro R t
  -- reindexing sums over the relation
  have hsplit : ∀ F : (Fin (ar R) → A) → ℚ, (∀ r, r ∉ 𝔸.rel R → F r = 0) →
      ∑ r, F r = ∑ j, F ((eR R j).val) := by
    intro F hF
    have h1 : ∑ r, F r = ∑ r ∈ Finset.univ.filter (fun r => r ∈ 𝔸.rel R), F r := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      split_ifs with hr
      · rfl
      · exact hF r hr
    rw [h1, Finset.sum_subtype (p := fun r => r ∈ 𝔸.rel R)
      (Finset.univ.filter (fun r => r ∈ 𝔸.rel R))
      (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) F]
    exact (Equiv.sum_comp (eR R) (fun x => F x.val)).symm
  constructor
  · rintro ⟨γ, hγ0, hγz, hγ1, hγm⟩
    have hγle : ∀ r, γ r ≤ 1 := by
      intro r
      rw [← hγ1]
      exact Finset.single_le_sum (f := γ) (fun b _ => hγ0 b) (Finset.mem_univ r)
    refine ⟨fun y => ∑ j, γ ((eR R j).val) * y j,
      ⟨fun j => γ ((eR R j).val), fun j => ⟨hγ0 _, hγle _⟩, ?_, rfl⟩, ?_⟩
    · rw [← hsplit γ hγz]; exact hγ1
    · intro i
      funext x
      change ∑ k, (t i).val (e k) * x k = ∑ j, γ ((eR R j).val) * x (e.symm ((eR R j).val i))
      rw [← hsplit (fun r => γ r * x (e.symm (r i))) (fun r hr => by simp [hγz r hr])]
      rw [← Finset.sum_fiberwise Finset.univ (fun r : Fin (ar R) → A => e.symm (r i))
        (fun r => γ r * x (e.symm (r i)))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hfil : (Finset.univ.filter (fun r : Fin (ar R) → A => e.symm (r i) = k)) =
          Finset.univ.filter (fun r : Fin (ar R) → A => r i = e k) := by
        ext r; simp [Equiv.symm_apply_eq]
      rw [hfil, ← hγm i (e k), Finset.sum_mul]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have : r i = e k := (Finset.mem_filter.mp hr).2
      rw [this, Equiv.symm_apply_apply]
  · rintro ⟨g, ⟨β, hβ01, hβs, rfl⟩, hg⟩
    let γ : (Fin (ar R) → A) → ℚ := fun r =>
      if hr : r ∈ 𝔸.rel R then β ((eR R).symm ⟨r, hr⟩) else 0
    have hγz : ∀ r, r ∉ 𝔸.rel R → γ r = 0 := fun r hr => by simp [γ, hr]
    have hγj : ∀ j, γ ((eR R j).val) = β j := by
      intro j
      simp only [γ, dif_pos (eR R j).2]
      congr 1
      rw [Equiv.symm_apply_eq]
    refine ⟨γ, fun r => ?_, hγz, ?_, ?_⟩
    · simp only [γ]; split_ifs
      · exact (hβ01 _).1
      · exact le_refl 0
    · rw [hsplit γ hγz]
      simp only [hγj]
      exact hβs
    · intro i a
      have hv : (t i).val a = ∑ j, β j * (if (eR R j).val i = a then 1 else 0) := by
        rw [← heval (t i) a]
        have := congrFun (hg i) (Pi.single (e.symm a) 1)
        change (toF (t i)).val (Pi.single (e.symm a) 1) = _ at this
        rw [this]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        congr 1
        simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
      rw [hv, Finset.sum_filter]
      rw [hsplit (fun r => if r i = a then γ r else 0) (fun r hr => by simp [hγz r hr])]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hγj]
      split_ifs <;> simp
