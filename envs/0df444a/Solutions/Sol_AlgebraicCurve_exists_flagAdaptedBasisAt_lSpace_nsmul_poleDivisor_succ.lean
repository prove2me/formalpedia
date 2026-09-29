-- Prove2me | solution 1 for AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/defa0e4c-d6f1-5413-9eef-5021eb596fe8

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ

set_option autoImplicit false
set_option maxHeartbeats 32000000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1) (M₁ : ℕ)
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hle : ∀ σ, e σ ≤ M₁) (hy : ∀ σ, y σ ∈ LSpace ((e σ) • D))
    (hspan : ∀ M ≤ M₁, (LSpace (M • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ})
    (hLI : ∀ M ≤ M₁, LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) :
    ∃ (d'' : ℕ) (y' : Fin d'' → F) (e' : Fin d'' → ℕ),
      (∀ σ, e' σ ≤ M₁ + 1) ∧
      (∀ σ, y' σ ∈ LSpace ((e' σ) • D)) ∧
      (∀ M ≤ M₁ + 1, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e' σ ≤ M ∧ z = x ^ j * y' σ}) ∧
      (∀ M ≤ M₁ + 1, LinearIndependent K
        (fun p : {p : Fin d'' × ℕ // p.2 + e' p.1 ≤ M} => x ^ p.val.2 * y' p.val.1)) := by
  classical
  have hD0 : 0 ≤ D := fun v => by simp [hD v]
  have hmono : ∀ {a b : ℕ}, a ≤ b → (LSpace (a • D) : Submodule K F) ≤ LSpace (b • D) := by
    intro a b hab; refine lSpace_mono ?_
    intro v; simpa using nsmul_le_nsmul_left (hD0 v) hab
  have hxne : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  set φ : F →ₗ[K] F := LinearMap.mulLeft K x with hφdef
  have hφinj : Function.Injective φ := fun a b h =>
    mul_left_cancel₀ hxne (by simpa [hφdef] using h)
  have hfr_map : ∀ (U : Submodule K F), FiniteDimensional K ↥U →
      Module.finrank K ↥(U.map φ) = Module.finrank K ↥U := fun U _ =>
    (Submodule.equivMapOfInjective φ hφinj U).symm.finrank_eq
  have hmem : ∀ σ j, x ^ j * y σ ∈ LSpace ((j + e σ) • D) := by
    intro σ j; induction j with
    | zero => simpa using hy σ
    | succ j ih2 =>
      have h := (mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD (j+e σ)).1 _ ih2
      have heq : (j + 1 + e σ) • D = (j + e σ + 1) • D := by ring_nf
      rw [heq, pow_succ', mul_assoc]; exact h
  haveI hFin : ∀ N, Fintype {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} := fun N =>
    Fintype.ofInjective
      (fun p => (p.val.1, (⟨p.val.2,
        Nat.lt_succ_of_le (le_trans (Nat.le_add_right _ _) p.2)⟩ : Fin (N + 1))))
      (by rintro ⟨⟨a,j⟩,_⟩ ⟨⟨b,l⟩,_⟩ h;
          simp only [Prod.mk.injEq, Fin.mk.injEq] at h;
          exact Subtype.ext (Prod.ext h.1 h.2))
  have hspanEq : ∀ N ≤ M₁, (Submodule.span K
      (Set.range (fun p : {p : Fin d' × ℕ // p.2+e p.1 ≤ N} => x^p.val.2 * y p.val.1))
      : Submodule K F) = LSpace (N • D) := by
    intro N hN; apply le_antisymm
    · rw [Submodule.span_le]; rintro z ⟨⟨⟨σ,j⟩,hje⟩,rfl⟩; exact hmono hje (hmem σ j)
    · refine (hspan N hN).trans (Submodule.span_mono ?_)
      rintro z ⟨σ,j,hje,rfl⟩; exact ⟨⟨(σ,j),hje⟩,rfl⟩
  have hcount : ∀ N ≤ M₁, Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N}
      = Module.finrank K ↥(LSpace (N • D) : Submodule K F) := by
    intro N hN; haveI := hFD N
    set g : {p : Fin d' × ℕ // p.2+e p.1 ≤ N} → ↥(LSpace (N•D) : Submodule K F) :=
      fun p => ⟨x^p.val.2 * y p.val.1, hmono p.2 (hmem p.val.1 p.val.2)⟩
    have hLIg : LinearIndependent K g := by
      have h : LinearIndependent K ((LSpace (N•D)).subtype ∘ g) := hLI N hN
      exact h.of_comp _
    have hspT : ⊤ ≤ Submodule.span K (Set.range g) := by
      rw [top_le_iff]
      apply Submodule.map_injective_of_injective (Submodule.injective_subtype _)
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
      exact hspanEq N hN
    exact (Module.finrank_eq_card_basis (Module.Basis.mk hLIg hspT)).symm
  have hcard : ∀ N, Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} = ∑ σ, (N + 1 - e σ) := by
    intro N
    have eqv : {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} ≃ (σ : Fin d') × Fin (N + 1 - e σ) := {
      toFun := fun p => ⟨p.val.1, ⟨p.val.2, by
        have h := p.2; change p.val.2 < N + 1 - e p.val.1; omega⟩⟩
      invFun := fun q => ⟨(q.1, (q.2 : ℕ)), by
        change (q.2 : ℕ) + e q.1 ≤ N; have h := q.2.isLt; omega⟩
      left_inv := fun p => rfl, right_inv := fun q => rfl }
    simp [Fintype.card_congr eqv, Fintype.card_sigma]
  have hstep : ∀ N, (∀ σ, e σ ≤ N) →
      Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N + 1}
        = Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} + d' := by
    intro N hN; rw [hcard (N+1), hcard N]
    have heq : ∀ σ : Fin d', N + 1 + 1 - e σ = (N + 1 - e σ) + 1 :=
      fun σ => by have := hN σ; omega
    simp only [heq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  have hcountM := hcount M₁ le_rfl
  have hcountM1 := hstep M₁ hle
  set L := (LSpace (M₁ • D) : Submodule K F) with hLdef
  set V := (LSpace ((M₁ + 1) • D) : Submodule K F) with hVdef
  haveI : FiniteDimensional K ↥L := hFD M₁
  haveI : FiniteDimensional K ↥V := hFD (M₁ + 1)
  haveI : FiniteDimensional K ↥(L.map φ) :=
    (Submodule.equivMapOfInjective φ hφinj L).finiteDimensional
  set W : Submodule K F := L ⊔ L.map φ with hWdef
  haveI : FiniteDimensional K ↥W := Submodule.finiteDimensional_sup L (L.map φ)
  obtain ⟨hsh1, _⟩ := mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD M₁
  have hW_le_V : W ≤ V := sup_le (hmono (Nat.le_succ M₁))
    (Submodule.map_le_iff_le_comap.2 fun g hg => hsh1 g hg)
  have hinf_dim : Module.finrank K ↥(L ⊓ L.map φ) + d' = Module.finrank K ↥L := by
    rcases Nat.eq_zero_or_pos M₁ with hM0 | hM1
    · subst hM0
      have hLfr : Module.finrank K ↥L = 1 := by
        have h : ell ((0:ℕ) • D) = 1 := by rw [zero_smul]; exact hell0
        exact h
      have hd1 : d' = 1 := by
        have hc0 : Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ 0} = d' := by
          rw [hcard 0]
          have heq : ∀ σ : Fin d', 0 + 1 - e σ = 1 := fun σ => by have := hle σ; omega
          simp [heq]
        omega
      have hlt : L ⊓ L.map φ < L := by
        refine lt_of_le_of_ne inf_le_left fun heq => ?_
        have hLle : L ≤ L.map φ := (le_of_eq heq.symm).trans inf_le_right
        have hne : L ≠ ⊥ := fun h => by rw [h] at hLfr; simp at hLfr
        obtain ⟨v, hvL, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
        have hLeq : L = Submodule.span K {v} :=
          (Submodule.eq_of_le_of_finrank_le
            (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvL))
            (by rw [finrank_span_singleton hvne, hLfr])).symm
        obtain ⟨h, hhL, hφh⟩ := hLle hvL
        rw [hLeq] at hhL
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hhL
        have hax : algebraMap K F a * x = 1 := by
          have heq1 : algebraMap K F a * x * v = v := by
            have := hφh; simp only [hφdef, LinearMap.mulLeft_apply, Algebra.smul_def] at this
            linear_combination this
          have : (algebraMap K F a * x - 1) * v = 0 := by linear_combination heq1
          rcases mul_eq_zero.mp this with h1 | h1
          · exact sub_eq_zero.mp h1
          · exact absurd h1 hvne
        have ha0 : a ≠ 0 := fun h => by simp [h] at hax
        refine hx ⟨Polynomial.C a * Polynomial.X - 1, ?_, ?_⟩
        · intro h; apply ha0
          have := congrArg (·.coeff 1) h; simpa [Polynomial.coeff_one] using this
        · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one]
          rw [hax, sub_self]
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    · have hm1 : M₁ - 1 + 1 = M₁ := by omega
      obtain ⟨hsh1p, hsh2p⟩ :=
        mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD (M₁ - 1)
      rw [hm1] at hsh1p hsh2p
      have hinf : L ⊓ L.map φ = (LSpace ((M₁-1)•D)).map φ := by
        apply le_antisymm
        · rintro z ⟨hzL, g, hgL, rfl⟩; exact ⟨g, hsh2p g hgL hzL, rfl⟩
        · rintro z ⟨g, hgP, rfl⟩
          exact ⟨hsh1p g hgP, g, hmono (Nat.sub_le _ _) hgP, rfl⟩
      haveI := hFD (M₁-1)
      rw [hinf, hfr_map _ (hFD (M₁-1))]
      rw [← hcount (M₁-1) (by omega), ← hcountM, hcard M₁, hcard (M₁-1)]
      have heq : ∀ σ : Fin d', M₁+1-e σ = (M₁-1+1-e σ)+1 := fun σ => by have := hle σ; omega
      simp only [heq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
  have hWfr : Module.finrank K ↥W
      = Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ M₁ + 1} := by
    have hsi := Submodule.finrank_sup_add_finrank_inf_eq L (L.map φ)
    rw [hfr_map L (hFD M₁), ← hWdef] at hsi
    omega
  have hspanOldW : (Submodule.span K
      (Set.range (fun p : {p : Fin d' × ℕ // p.2+e p.1 ≤ M₁+1} => x^p.val.2 * y p.val.1))
      : Submodule K F) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro z ⟨⟨⟨σ,j⟩,hje⟩,rfl⟩
      rcases Nat.eq_zero_or_pos j with hj0 | hj1
      · subst hj0; simp only [pow_zero, one_mul]
        exact Submodule.mem_sup_left (hmono (hle σ) (hy σ))
      · have hje' : j + e σ ≤ M₁ + 1 := hje
        refine Submodule.mem_sup_right ⟨x^(j-1) * y σ,
          hmono (show j-1+e σ ≤ M₁ by omega) (hmem σ (j-1)), ?_⟩
        simp only [hφdef, LinearMap.mulLeft_apply, ← mul_assoc, ← pow_succ']
        congr 2; omega
    · refine sup_le ?_ ?_
      · refine (hspan M₁ le_rfl).trans (Submodule.span_mono ?_)
        rintro z ⟨σ,j,hje,rfl⟩; exact ⟨⟨(σ,j), Nat.le_succ_of_le hje⟩, rfl⟩
      · rw [Submodule.map_le_iff_le_comap]
        refine (hspan M₁ le_rfl).trans (Submodule.span_le.mpr ?_)
        rintro z ⟨σ,j,hje,rfl⟩
        exact Submodule.mem_comap.mpr (Submodule.subset_span ⟨⟨(σ,j+1),
          by show j+1+e σ ≤ M₁+1; omega⟩, by simp [hφdef, ← mul_assoc, ← pow_succ']⟩)
  have hLIold : LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2+e p.1 ≤ M₁+1} => x^p.val.2 * y p.val.1) := by
    set gW : {p : Fin d' × ℕ // p.2+e p.1 ≤ M₁+1} → ↥W :=
      fun p => ⟨x^p.val.2 * y p.val.1, hspanOldW ▸ Submodule.subset_span ⟨p, rfl⟩⟩
    have hspT : ⊤ ≤ Submodule.span K (Set.range gW) := by
      rw [top_le_iff]
      apply Submodule.map_injective_of_injective (Submodule.injective_subtype W)
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
      exact hspanOldW
    have hLIgW : LinearIndependent K gW := by
      have h := (basisOfTopLeSpanOfCardEqFinrank gW hspT hWfr.symm).linearIndependent
      rwa [coe_basisOfTopLeSpanOfCardEqFinrank] at h
    exact hLIgW.map' W.subtype (Submodule.ker_subtype W)

  set W' : Submodule K ↥V := Submodule.comap V.subtype W with hW'def
  haveI : FiniteDimensional K ↥W' := inferInstance
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W'
  haveI : FiniteDimensional K ↥C := inferInstance
  haveI : Module.Free K ↥C := Module.Free.of_divisionRing K ↥C
  set k := Module.finrank K ↥C with hkdef
  let zC : Module.Basis (Fin k) K ↥C := Module.finBasis K ↥C
  let z : Fin k → F := fun i => (C.subtype (zC i) : F)
  have hzV : ∀ i, z i ∈ V := fun i => (C.subtype (zC i)).2
  have hW'fr : Module.finrank K ↥W' = Module.finrank K ↥W := by
    have heq : W'.map V.subtype = W := by
      rw [hW'def, Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hW_le_V]
    rw [← heq]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective V.subtype
      (Submodule.injective_subtype V) W')
  have hVfr : Module.finrank K ↥V = Module.finrank K ↥W + k := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W' C
    rw [hC.sup_eq_top, hC.inf_eq_bot, finrank_bot, finrank_top, add_zero, hW'fr] at this
    omega

  let y' : Fin (d' + k) → F := Fin.append y z
  let e' : Fin (d' + k) → ℕ := Fin.append e (fun _ => M₁ + 1)

  have hnewSetOld : ∀ M ≤ M₁, {w | ∃ σ j, j + e' σ ≤ M ∧ w = x ^ j * y' σ}
      = {w | ∃ σ j, j + e σ ≤ M ∧ w = x ^ j * y σ} := by
    intro M hM; ext w; constructor
    · rintro ⟨σ, j, hje, rfl⟩
      induction σ using Fin.addCases with
      | left i => exact ⟨i, j, by simpa only [e', Fin.append_left] using hje,
          by simp only [y', Fin.append_left]⟩
      | right i => exfalso; simp only [e', Fin.append_right] at hje; omega
    · rintro ⟨σ, j, hje, rfl⟩
      exact ⟨Fin.castAdd k σ, j, by simpa only [e', Fin.append_left] using hje,
        by simp only [y', Fin.append_left]⟩

  have hnewSpanV : V ≤ Submodule.span K {w | ∃ σ j, j + e' σ ≤ M₁+1 ∧ w = x^j*y' σ} := by
    intro v hv
    have hv2 : (⟨v, hv⟩ : ↥V) ∈ W' ⊔ C := hC.sup_eq_top ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at hv2; obtain ⟨w, hwW, c, hcC, hwc⟩ := hv2
    have hvw : v = (w : F) + (c : F) := by
      have := congrArg Subtype.val hwc; simpa using this.symm
    rw [hvw]; refine Submodule.add_mem _ ?_ ?_
    · have hw1 : (w : F) ∈ W := hwW
      rw [← hspanOldW] at hw1
      refine Submodule.span_le.mpr ?_ hw1
      rintro u ⟨⟨⟨σ,j⟩,hje⟩,rfl⟩
      exact Submodule.subset_span ⟨Fin.castAdd k σ, j,
        by simpa only [e', Fin.append_left] using hje, by simp only [y', Fin.append_left]⟩
    · have hcspan : (c : ↥V) ∈ Submodule.span K (Set.range (C.subtype ∘ ⇑zC)) := by
        rw [Set.range_comp, ← Submodule.map_span, zC.span_eq, Submodule.map_top,
          Submodule.range_subtype]; exact hcC
      have := Submodule.apply_mem_span_image_of_mem_span V.subtype hcspan
      rw [← Set.range_comp] at this
      refine Submodule.span_le.mpr ?_ this
      rintro u ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Fin.natAdd d' i, 0,
        by simp only [e', Fin.append_right]; omega,
        by simp only [y', Fin.append_right, z, Function.comp_apply, pow_zero, one_mul]; rfl⟩

  have hnewMemV : ∀ p : {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M₁+1}, x^p.val.2*y' p.val.1 ∈ V := by
    rintro ⟨⟨σ,j⟩,hp⟩; dsimp only
    induction σ using Fin.addCases with
    | left i => simp only [y', Fin.append_left]
                refine hmono ?_ (hmem i j); simpa only [e', Fin.append_left] using hp
    | right i =>
      simp only [y', e', Fin.append_right] at hp ⊢
      have hj : j = 0 := by omega
      subst hj; simpa using hzV i

  haveI hFinNew : ∀ M, Fintype {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M} := fun M =>
    Fintype.ofInjective
      (fun p => (p.val.1, (⟨p.val.2,
        Nat.lt_succ_of_le (le_trans (Nat.le_add_right _ _) p.2)⟩ : Fin (M+1))))
      (by rintro ⟨⟨a,j⟩,_⟩ ⟨⟨b,l⟩,_⟩ h;
          simp only [Prod.mk.injEq, Fin.mk.injEq] at h;
          exact Subtype.ext (Prod.ext h.1 h.2))
  have hnewcard : ∀ M, Fintype.card {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M} = ∑ σ, (M+1-e' σ) := by
    intro M
    have eqv : {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M} ≃ (σ : Fin (d'+k)) × Fin (M+1 - e' σ) := {
      toFun := fun p => ⟨p.val.1, ⟨p.val.2, by
        have h := p.2; change p.val.2 < M+1-e' p.val.1; omega⟩⟩
      invFun := fun q => ⟨(q.1,(q.2:ℕ)), by
        change (q.2:ℕ)+e' q.1≤M; have h:=q.2.isLt; omega⟩
      left_inv := fun p => rfl, right_inv := fun q => rfl }
    simp [Fintype.card_congr eqv, Fintype.card_sigma]
  have hnewCardV : Fintype.card {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M₁+1} = Module.finrank K ↥V := by
    rw [hnewcard (M₁+1), Fin.sum_univ_add]
    simp only [e', Fin.append_left, Fin.append_right]
    rw [← hcard (M₁+1), hWfr.symm, hVfr]
    congr 1
    simp only [show M₁+1+1-(M₁+1)=1 from by omega, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]

  refine ⟨d' + k, y', e', ?_, ?_, ?_, ?_⟩
  · intro σ; induction σ using Fin.addCases with
    | left i => simp only [e', Fin.append_left]; exact (hle i).trans (Nat.le_succ _)
    | right i => simp only [e', Fin.append_right]; exact le_refl _
  · intro σ; induction σ using Fin.addCases with
    | left i => simp only [y', e', Fin.append_left]; exact hy i
    | right i => simp only [y', e', Fin.append_right]; exact hzV i
  · intro M hM
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hM) with hMlt | rfl
    · rw [hnewSetOld M (Nat.lt_succ_iff.mp hMlt)]; exact hspan M (Nat.lt_succ_iff.mp hMlt)
    · exact hnewSpanV
  · intro M hM
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hM) with hMlt | rfl
    · have hMle := Nat.lt_succ_iff.mp hMlt

      have hlt : ∀ p : {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M}, (p.val.1:ℕ) < d' := by
        intro p; by_contra h; push_neg at h
        have hσlt := p.val.1.isLt
        have heq : p.val.1 = Fin.natAdd d' ⟨(p.val.1:ℕ) - d', by omega⟩ :=
          Fin.ext (by show (p.val.1:ℕ) = d' + ((p.val.1:ℕ) - d'); omega)
        have hp := p.2; rw [heq] at hp; simp only [e', Fin.append_right] at hp; omega
      let ι : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} ≃ {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M} := {
        toFun := fun q => ⟨(Fin.castAdd k q.val.1, q.val.2), by
          simp only [e', Fin.append_left]; exact q.2⟩
        invFun := fun p => ⟨(⟨p.val.1, hlt p⟩, p.val.2), by
          have h := p.2
          have heq : p.val.1 = Fin.castAdd k ⟨(p.val.1:ℕ), hlt p⟩ := Fin.ext (by simp)
          rw [heq] at h; simpa only [e', Fin.append_left] using h⟩
        left_inv := fun q => by
          apply Subtype.ext; apply Prod.ext
          · simp [Fin.ext_iff]
          · rfl
        right_inv := fun p => by
          apply Subtype.ext; apply Prod.ext
          · simp [Fin.ext_iff]
          · rfl }
      have heqf : (fun p : {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M} => x^p.val.2*y' p.val.1)
          = (fun q : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x^q.val.2*y q.val.1) ∘ ι.symm := by
        ext p; simp only [Function.comp_apply, ι, Equiv.coe_fn_symm_mk]
        congr 1
        have heq : p.val.1 = Fin.castAdd k ⟨(p.val.1:ℕ), hlt p⟩ := Fin.ext (by simp)
        conv_lhs => rw [heq]; simp only [y', Fin.append_left]
      rw [heqf]; exact (hLI M hMle).comp ι.symm ι.symm.injective
    ·
      set gV : {p : Fin (d'+k) × ℕ // p.2 + e' p.1 ≤ M₁+1} → ↥V := fun p => ⟨x^p.val.2*y' p.val.1, hnewMemV p⟩
      have hspT : ⊤ ≤ Submodule.span K (Set.range gV) := by
        rw [top_le_iff]
        apply Submodule.map_injective_of_injective (Submodule.injective_subtype V)
        rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
        have hreq : Set.range (V.subtype ∘ gV)
            = {w | ∃ σ j, j + e' σ ≤ M₁+1 ∧ w = x^j*y' σ} := by
          ext w; constructor
          · rintro ⟨⟨⟨σ,j⟩,hje⟩, rfl⟩; exact ⟨σ, j, hje, rfl⟩
          · rintro ⟨σ,j,hje,rfl⟩; exact ⟨⟨(σ,j),hje⟩, rfl⟩
        rw [hreq]
        exact le_antisymm
          (Submodule.span_le.mpr fun u ⟨σ,j,hje,hu⟩ => hu ▸ hnewMemV ⟨(σ,j),hje⟩) hnewSpanV
      have hLIgV : LinearIndependent K gV := by
        have h := (basisOfTopLeSpanOfCardEqFinrank gV hspT hnewCardV).linearIndependent
        rwa [coe_basisOfTopLeSpanOfCardEqFinrank] at h
      exact hLIgV.map' V.subtype (Submodule.ker_subtype V)

end S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ
end P2MW
export P2MW.S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ (solution)
