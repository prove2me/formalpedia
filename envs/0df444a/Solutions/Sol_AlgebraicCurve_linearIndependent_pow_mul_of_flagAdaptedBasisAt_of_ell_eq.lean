-- Prove2me | solution 1 for AlgebraicCurve.linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2f32079a-aeb9-512f-8b61-fe87170a50b5

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq

set_option autoImplicit false
set_option maxHeartbeats 12000000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (M₀ d g₀ : ℕ)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀)
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hle : ∀ σ, e σ ≤ M₀ + 1) (hy : ∀ σ, y σ ∈ LSpace ((e σ) • D))
    (hspan : ∀ M : ℕ, (LSpace (M • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ})
    (hLIat : ∀ M ≤ M₀ + 1, LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) :
    LinearIndependent K (fun p : Fin d' × ℕ => x ^ p.2 * y p.1) := by
  classical
  have hD0 : 0 ≤ D := fun v => by simp [hD v]
  have hmono : ∀ {a b : ℕ}, a ≤ b → (LSpace (a • D) : Submodule K F) ≤ LSpace (b • D) := by
    intro a b hab; refine lSpace_mono ?_
    intro v; simpa using nsmul_le_nsmul_left (hD0 v) hab
  have hmem : ∀ σ j, x ^ j * y σ ∈ LSpace ((j + e σ) • D) := by
    intro σ j
    induction j with
    | zero => simpa using hy σ
    | succ j ih =>
      have h := (mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD (j + e σ)).1 _ ih
      have heq : (j + 1 + e σ) • D = (j + e σ + 1) • D := by ring_nf
      rw [heq, pow_succ', mul_assoc]; exact h

  have hrange : ∀ N, {z | ∃ σ j, j + e σ ≤ N ∧ z = x ^ j * y σ}
      = Set.range (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} => x ^ p.val.2 * y p.val.1) := by
    intro N; ext z; constructor
    · rintro ⟨σ, j, hje, rfl⟩; exact ⟨⟨(σ, j), hje⟩, rfl⟩
    · rintro ⟨⟨⟨σ, j⟩, hje⟩, rfl⟩; exact ⟨σ, j, hje, rfl⟩
  have hspanEq : ∀ N, (Submodule.span K
        (Set.range (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} => x ^ p.val.2 * y p.val.1))
      : Submodule K F) = LSpace (N • D) := by
    intro N; apply le_antisymm
    · rw [Submodule.span_le]; rintro z ⟨⟨⟨σ, j⟩, hje⟩, rfl⟩; exact hmono hje (hmem σ j)
    · rw [← hrange N]; exact hspan N

  haveI hFin : ∀ N, Fintype {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} := fun N =>
    Fintype.ofInjective
      (fun p => (p.val.1, (⟨p.val.2, Nat.lt_succ_of_le (le_trans (Nat.le_add_right _ _) p.2)⟩
        : Fin (N + 1))))
      (by
        rintro ⟨⟨aσ, aj⟩, ha⟩ ⟨⟨bσ, bj⟩, hb⟩ h
        simp only [Prod.mk.injEq, Fin.mk.injEq] at h
        exact Subtype.ext (Prod.ext h.1 h.2))

  have hcard : ∀ N, Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} = ∑ σ, (N + 1 - e σ) := by
    intro N
    have eqv : {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} ≃ (σ : Fin d') × Fin (N + 1 - e σ) := {
      toFun := fun p => ⟨p.val.1, ⟨p.val.2, by
        have h := p.2; change p.val.2 < N + 1 - e p.val.1; omega⟩⟩
      invFun := fun q => ⟨(q.1, (q.2 : ℕ)), by
        change (q.2 : ℕ) + e q.1 ≤ N; have h := q.2.isLt; omega⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
    simp [Fintype.card_congr eqv, Fintype.card_sigma]

  have hceq_at : ∀ N ≤ M₀ + 1,
      Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N}
        = Module.finrank K ↥(LSpace (N • D) : Submodule K F) := by
    intro N hN; haveI := hFD N
    set g : {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} → ↥(LSpace (N • D) : Submodule K F) :=
      fun p => ⟨x ^ p.val.2 * y p.val.1, hmono p.2 (hmem p.val.1 p.val.2)⟩ with hgdef
    have hLIg : LinearIndependent K g := by
      have h : LinearIndependent K ((LSpace (N • D)).subtype ∘ g) := hLIat N hN
      exact h.of_comp _
    have hspanTop : ⊤ ≤ Submodule.span K (Set.range g) := by
      rw [top_le_iff]
      apply Submodule.map_injective_of_injective (Submodule.injective_subtype _)
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
      exact hspanEq N
    exact (Module.finrank_eq_card_basis (Module.Basis.mk hLIg hspanTop)).symm
  have hc0 := hceq_at M₀ (by omega)
  have hc1 := hceq_at (M₀ + 1) le_rfl
  have hfrZ : ∀ N, M₀ ≤ N →
      (Module.finrank K ↥(LSpace (N • D) : Submodule K F) : ℤ) = N * d + 1 - g₀ := by
    intro N hN; have := hell N hN; exact_mod_cast this
  have hstep : ∀ N, (∀ σ, e σ ≤ N + 1) →
      Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N + 1}
        = Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} + d' := by
    intro N hN; rw [hcard (N + 1), hcard N]
    have heq : ∀ σ : Fin d', N + 1 + 1 - e σ = (N + 1 - e σ) + 1 :=
      fun σ => by have := hN σ; omega
    simp only [heq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  have hfrD : ∀ N, M₀ ≤ N →
      (Module.finrank K ↥(LSpace ((N + 1) • D) : Submodule K F) : ℤ)
        = Module.finrank K ↥(LSpace (N • D) : Submodule K F) + d := by
    intro N hN; rw [hfrZ N hN, hfrZ (N + 1) (by omega)]; push_cast; ring
  have hd'd : (d' : ℤ) = d := by
    have hs := hstep M₀ hle
    have h0Z : (Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ M₀} : ℤ)
             = Module.finrank K ↥(LSpace (M₀ • D) : Submodule K F) := by exact_mod_cast hc0
    have h1Z : (Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ M₀ + 1} : ℤ)
             = Module.finrank K ↥(LSpace ((M₀ + 1) • D) : Submodule K F) := by exact_mod_cast hc1
    have hsZ : (Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ M₀ + 1} : ℤ)
             = Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ M₀} + d' := by exact_mod_cast hs
    linarith [hfrD M₀ le_rfl]
  have hceq_ge : ∀ N, M₀ ≤ N →
      Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N}
        = Module.finrank K ↥(LSpace (N • D) : Submodule K F) := by
    intro N hN
    induction N with
    | zero => exact hceq_at 0 (by omega)
    | succ N ih =>
      rcases le_or_gt (N + 1) (M₀ + 1) with h | h
      · exact hceq_at (N + 1) h
      · have hNge : M₀ ≤ N := by omega
        have hstepN := hstep N fun σ => (hle σ).trans (by omega)
        have ihN := ih hNge
        have goal : (Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N + 1} : ℤ)
             = Module.finrank K ↥(LSpace ((N + 1) • D) : Submodule K F) := by
          have stZ : (Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N + 1} : ℤ)
                   = Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} + d' := by
            exact_mod_cast hstepN
          have ihZ : (Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} : ℤ)
                   = Module.finrank K ↥(LSpace (N • D) : Submodule K F) := by
            exact_mod_cast ihN
          linarith [hd'd, hfrD N hNge]
        exact_mod_cast goal

  have hLI_ge : ∀ N, M₀ + 1 ≤ N → LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} => x ^ p.val.2 * y p.val.1) := by
    intro N hN; haveI := hFD N
    set V := (LSpace (N • D) : Submodule K F) with hVdef
    set g : {p : Fin d' × ℕ // p.2 + e p.1 ≤ N} → ↥V :=
      fun p => ⟨x ^ p.val.2 * y p.val.1, hmono p.2 (hmem p.val.1 p.val.2)⟩ with hgdef
    have hspanTop : ⊤ ≤ Submodule.span K (Set.range g) := by
      rw [top_le_iff]
      apply Submodule.map_injective_of_injective (Submodule.injective_subtype V)
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
      have hcomp : V.subtype ∘ g = fun p => x ^ p.val.2 * y p.val.1 := rfl
      rw [hcomp]; exact hspanEq N
    have hceq := hceq_ge N (by omega)
    have hLIg : LinearIndependent K g := by
      have h := (basisOfTopLeSpanOfCardEqFinrank g hspanTop hceq).linearIndependent
      rwa [coe_basisOfTopLeSpanOfCardEqFinrank] at h
    exact hLIg.map' V.subtype (Submodule.ker_subtype V)

  rw [linearIndependent_iff']
  intro s c hc p hp
  set N := M₀ + 1 + s.sup (fun q => q.2 + e q.1) with hNdef
  have hN1 : M₀ + 1 ≤ N := Nat.le_add_right _ _
  have hN2 : ∀ q ∈ s, q.2 + e q.1 ≤ N := fun q hq =>
    le_trans (Finset.le_sup (f := fun q => q.2 + e q.1) hq) (Nat.le_add_left _ _)
  have hLI := hLI_ge N hN1
  have hlinj : Function.Injective
      (fun q : {q // q ∈ s} => (⟨q.val, hN2 q.val q.2⟩ : {p : Fin d' × ℕ // p.2 + e p.1 ≤ N})) := by
    intro a b h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h
  have key := (linearIndependent_iff'.mp hLI)
    (s.attach.map ⟨_, hlinj⟩) (fun q => c q.val)
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk] at key
  have hc' : ∑ q ∈ s.attach,
      c q.val • (x ^ (q : Fin d' × ℕ).2 * y (q : Fin d' × ℕ).1) = 0 := by
    rw [Finset.sum_attach s (fun q => c q • (x ^ q.2 * y q.1))]; exact hc
  exact key hc' ⟨p, hN2 p hp⟩ (Finset.mem_map.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩)

end S_AlgebraicCurve_linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
end P2MW
export P2MW.S_AlgebraicCurve_linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq (solution)
