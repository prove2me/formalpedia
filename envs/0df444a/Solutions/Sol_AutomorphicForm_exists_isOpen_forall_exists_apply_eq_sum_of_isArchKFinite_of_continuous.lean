-- Prove2me | solution 1 for AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/37ed5913-80f0-5824-a397-8d86adc62d9c

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open Topology

noncomputable section

namespace EvalMatrix

variable {𝕜 : Type*} [Field 𝕜] {X : Type*}

private def evalMatrix {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => v j (x i)

omit [Field 𝕜] in
private theorem evalMatrix_apply {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X) (i j : Fin n) :
    evalMatrix v x i j = v j (x i) := rfl

private theorem exists_det_evalMatrix_ne_zero :
    ∀ {n : ℕ} (v : Fin n → X → 𝕜), LinearIndependent 𝕜 v →
      ∃ x : Fin n → X, (evalMatrix v x).det ≠ 0
  | 0, _, _ => ⟨Fin.elim0, by rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  | n + 1, v, hv => by
    obtain ⟨x', hx'⟩ :=
      exists_det_evalMatrix_ne_zero (fun j => v j.succ) (hv.comp Fin.succ (Fin.succ_injective n))

    let e : Fin (n + 1) → 𝕜 := fun j =>
      (-1) ^ (j : ℕ) * (Matrix.of fun (i : Fin n) (j' : Fin n) => v (j.succAbove j') (x' i)).det
    have hminor : ∀ (y : X) (j : Fin (n + 1)),
        (evalMatrix v (Fin.cons y x')).submatrix Fin.succ j.succAbove
          = Matrix.of fun (i : Fin n) (j' : Fin n) => v (j.succAbove j') (x' i) := by
      intro y j
      ext i j'
      simp [evalMatrix, Matrix.submatrix, Fin.cons_succ]
    have hexp : ∀ y : X, (evalMatrix v (Fin.cons y x')).det = ∑ j, e j * v j y := by
      intro y
      rw [Matrix.det_succ_row_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hminor y j]
      simp only [e, evalMatrix_apply, Fin.cons_zero]
      ring
    have he0 : e 0 ≠ 0 := by
      have h0 : (Matrix.of fun (i : Fin n) (j' : Fin n) => v ((0 : Fin (n + 1)).succAbove j') (x' i))
          = evalMatrix (fun j => v j.succ) x' := by
        ext i j'
        simp [evalMatrix]
      simp only [e, Fin.val_zero, pow_zero, one_mul, h0]
      exact hx'
    by_cases hy : ∃ y : X, (evalMatrix v (Fin.cons y x')).det ≠ 0
    · obtain ⟨y, hy⟩ := hy
      exact ⟨Fin.cons y x', hy⟩
    · exfalso
      have hzero : ∀ y : X, (evalMatrix v (Fin.cons y x')).det = 0 :=
        fun y => by_contra fun h => hy ⟨y, h⟩
      have hsum : ∑ j, e j • v j = 0 := by
        funext y
        have := hexp y
        rw [hzero y] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact this.symm
      exact he0 (Fintype.linearIndependent_iff.mp hv e hsum 0)

private theorem linearIndependent_of_det_evalMatrix_ne_zero {n : ℕ} (v : Fin n → X → 𝕜)
    (x : Fin n → X) (h : (evalMatrix v x).det ≠ 0) : LinearIndependent 𝕜 v := by
  have hrows : LinearIndependent 𝕜 (fun j => (evalMatrix v x).transpose j) :=
    Matrix.linearIndependent_rows_of_det_ne_zero (by rwa [Matrix.det_transpose])
  let f : (X → 𝕜) →ₗ[𝕜] (Fin n → 𝕜) := LinearMap.pi fun i => LinearMap.proj (x i)
  have hcomp : (⇑f ∘ v) = fun j => (evalMatrix v x).transpose j := by
    funext j i
    rfl
  exact LinearIndependent.of_comp f (by rw [hcomp]; exact hrows)

private theorem linearIndependent_iff_exists_det_evalMatrix_ne_zero {n : ℕ} (v : Fin n → X → 𝕜) :
    LinearIndependent 𝕜 v ↔ ∃ x : Fin n → X, (evalMatrix v x).det ≠ 0 :=
  ⟨exists_det_evalMatrix_ne_zero v, fun ⟨x, hx⟩ => linearIndependent_of_det_evalMatrix_ne_zero v x hx⟩

private theorem eq_sum_inv_evalMatrix_mulVec_smul {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X)
    (hx : (evalMatrix v x).det ≠ 0) (g : X → 𝕜) (hg : g ∈ Submodule.span 𝕜 (Set.range v)) :
    g = ∑ j, ((evalMatrix v x)⁻¹.mulVec (fun i => g (x i))) j • v j := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := 𝕜)).mp hg
  have hvals : (fun i => (∑ j, c j • v j) (x i)) = (evalMatrix v x).mulVec c := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      evalMatrix_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hinv : (evalMatrix v x)⁻¹.mulVec ((evalMatrix v x).mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]
  rw [hvals, hinv]

end EvalMatrix

namespace UniformRank

open scoped Pointwise

variable {G : Type*} [Monoid G]

private def TranslatesFinite (Q : Set G) (f : G → ℂ) : Prop :=
  ∃ t : Finset (G → ℂ), ∀ k ∈ Q, (fun g => f (g * k)) ∈ Submodule.span ℂ (t : Set (G → ℂ))

private def rt (x : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun φ := fun g => φ (g * x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rt_apply (x : G) (φ : G → ℂ) (g : G) : rt x φ g = φ (g * x) := rfl

private theorem rt_translate (a b : G) (f : G → ℂ) :
    rt a (fun g => f (g * b)) = fun g => f (g * (a * b)) := by
  funext g
  show f (g * a * b) = f (g * (a * b))
  rw [mul_assoc]

private theorem exists_finset_subset_forall_mem_span (Q : Set G) (f : G → ℂ)
    (h : TranslatesFinite Q f) :
    ∃ B : Finset G, (↑B : Set G) ⊆ Q ∧
      ∀ k ∈ Q, (fun g => f (g * k)) ∈
        Submodule.span ℂ ((fun b : G => fun g => f (g * b)) '' (↑B : Set G)) := by
  classical
  obtain ⟨t, ht⟩ := h

  set X : Set (G → ℂ) := (fun b : G => fun g => f (g * b)) '' Q with hX
  have hle : Submodule.span ℂ X ≤ Submodule.span ℂ (t : Set (G → ℂ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact ht k hk
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (t : Set (G → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ t.finite_toSet
  haveI hW : FiniteDimensional ℂ (Submodule.span ℂ X) := Submodule.finiteDimensional_of_le hle
  have hfg : (Submodule.span ℂ X).FG := (Submodule.fg_iff_finiteDimensional _).mpr hW
  obtain ⟨s, hs⟩ := hfg

  have hmem : ∀ v ∈ s, ∃ T : Finset (G → ℂ), (↑T : Set (G → ℂ)) ⊆ X ∧
      v ∈ Submodule.span ℂ (T : Set (G → ℂ)) := by
    intro v hv
    have hvX : v ∈ Submodule.span ℂ X := by
      rw [← hs]
      exact Submodule.subset_span hv
    exact Submodule.mem_span_finite_of_mem_span hvX
  choose T hTX hvT using hmem
  set U : Finset (G → ℂ) := s.attach.biUnion (fun v => T v.1 v.2) with hU
  have hUX : (↑U : Set (G → ℂ)) ⊆ X := by
    intro y hy
    rw [Finset.mem_coe, hU, Finset.mem_biUnion] at hy
    obtain ⟨v, -, hyv⟩ := hy
    exact hTX v.1 v.2 (Finset.mem_coe.mpr hyv)
  have hWU : Submodule.span ℂ X ≤ Submodule.span ℂ (U : Set (G → ℂ)) := by
    rw [← hs, Submodule.span_le]
    intro v hv
    have hv' : v ∈ s := hv
    refine Submodule.span_mono ?_ (hvT v hv')
    intro y hy
    rw [Finset.mem_coe, hU, Finset.mem_biUnion]
    exact ⟨⟨v, hv'⟩, Finset.mem_attach _ _, Finset.mem_coe.mp hy⟩

  have hUX' : (↑U : Set (G → ℂ)) ⊆ (fun b : G => fun g => f (g * b)) '' Q := hUX
  obtain ⟨B, hBQ, hBU⟩ := Finset.subset_set_image_iff.mp hUX'
  refine ⟨B, hBQ, fun k hk => ?_⟩
  have hkX : (fun g => f (g * k)) ∈ Submodule.span ℂ X := Submodule.subset_span ⟨k, hk, rfl⟩
  have h1 := hWU hkX
  rwa [← hBU, Finset.coe_image] at h1

private theorem translatesFinite_mul (Q₁ Q₂ : Set G) (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (f : G → ℂ) (h₁ : TranslatesFinite Q₁ f) (h₂ : TranslatesFinite Q₂ f) :
    TranslatesFinite (Q₁ * Q₂) f :=
 by
  classical
  obtain ⟨A, hAQ, hA⟩ := exists_finset_subset_forall_mem_span Q₁ f h₁
  obtain ⟨B, hBQ, hB⟩ := exists_finset_subset_forall_mem_span Q₂ f h₂

  refine ⟨(A ×ˢ B).image fun p : G × G => fun g => f (g * (p.1 * p.2)), ?_⟩
  intro k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hk
  set t : Finset (G → ℂ) := (A ×ˢ B).image fun p : G × G => fun g => f (g * (p.1 * p.2)) with ht
  have hgen : ∀ a' ∈ A, ∀ b' ∈ B,
      (fun g => f (g * (a' * b'))) ∈ Submodule.span ℂ (t : Set (G → ℂ)) := by
    intro a' ha' b' hb'
    apply Submodule.subset_span
    rw [ht, Finset.coe_image]
    exact ⟨(a', b'), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨ha', hb'⟩), rfl⟩

  have hstep : ∀ b' ∈ B, rt a (fun g => f (g * b')) ∈ Submodule.span ℂ (t : Set (G → ℂ)) := by
    intro b' hb'
    have e : rt a (fun g => f (g * b')) = rt b' (fun g => f (g * a)) := by
      rw [rt_translate, rt_translate, hcomm a ha b' (hBQ hb')]
    rw [e]

    have hRa := hA a ha
    have h2 : rt b' (fun g => f (g * a)) ∈
        Submodule.span ℂ ((rt b') '' ((fun a' : G => fun g => f (g * a')) '' (↑A : Set G))) := by
      rw [Submodule.span_image]
      exact Submodule.mem_map_of_mem hRa
    refine Submodule.span_le.mpr ?_ h2
    rintro _ ⟨_, ⟨a', ha', rfl⟩, rfl⟩
    rw [rt_translate, ← hcomm a' (hAQ ha') b' (hBQ hb')]
    exact hgen a' ha' b' hb'

  rw [← rt_translate a b f]
  have h3 : rt a (fun g => f (g * b)) ∈
      Submodule.span ℂ ((rt a) '' ((fun b' : G => fun g => f (g * b')) '' (↑B : Set G))) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map_of_mem (hB b hb)
  refine Submodule.span_le.mpr ?_ h3
  rintro _ ⟨_, ⟨b', hb', rfl⟩, rfl⟩
  exact hstep b' hb'

private theorem exists_isOpen_subset_forall_det_ne_zero_and_mem_span (Q : Set G) (u : ℂ → G → ℂ)
    (hfin : ∀ s, TranslatesFinite Q (u s)) (hc : ∀ g, Continuous fun s => u s g)
    (U₀ : Set ℂ) (hU₀ : IsOpen U₀) (hne : U₀.Nonempty) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ U₀ ∧
      ∃ (r : ℕ) (κ : Fin r → G) (x : Fin r → G), (∀ j, κ j ∈ Q) ∧
        (∀ s ∈ U, (Matrix.of fun i j => u s (x i * κ j)).det ≠ 0) ∧
        ∀ s ∈ U, ∀ k ∈ Q,
          (fun g => u s (g * k)) ∈ Submodule.span ℂ (Set.range fun j => fun g => u s (g * κ j)) :=
 by
  classical

  have hcontdet : ∀ {n : ℕ} (κ : Fin n → G) (x : Fin n → G),
      Continuous fun s : ℂ => (Matrix.of fun i j => u s (x i * κ j)).det := by
    intro n κ x
    have hprod : ∀ σ : Equiv.Perm (Fin n), Continuous fun s : ℂ => ∏ i, u s (x (σ i) * κ i) :=
      fun σ => continuous_finsetProd _ fun i _ => hc (x (σ i) * κ i)
    simp only [Matrix.det_apply, Matrix.of_apply]
    exact continuous_finsetSum _ fun σ _ => (hprod σ).const_smul _

  have hbound : ∀ s, ∃ n : ℕ, ∀ κ : Fin (n + 1) → G, (∀ j, κ j ∈ Q) → ∀ x : Fin (n + 1) → G,
      (Matrix.of fun i j => u s (x i * κ j)).det = 0 := by
    intro s
    obtain ⟨t, ht⟩ := hfin s
    refine ⟨t.card, fun κ hκ x => ?_⟩
    by_contra hdet
    have hind : LinearIndependent ℂ (fun j => fun g => u s (g * κ j)) :=
      EvalMatrix.linearIndependent_of_det_evalMatrix_ne_zero _ x hdet
    have hmem : ∀ j, (fun g => u s (g * κ j)) ∈ Submodule.span ℂ (t : Set (G → ℂ)) :=
      fun j => ht (κ j) (hκ j)
    have hind' : LinearIndependent ℂ
        (fun j => (⟨_, hmem j⟩ : Submodule.span ℂ (t : Set (G → ℂ)))) :=
      LinearIndependent.of_comp (Submodule.span ℂ (t : Set (G → ℂ))).subtype hind
    have h1 := hind'.fintype_card_le_finrank
    have h2 : Module.finrank ℂ (Submodule.span ℂ (t : Set (G → ℂ))) ≤ t.card :=
      finrank_span_finset_le_card (R := ℂ) t
    rw [Fintype.card_fin] at h1
    omega

  haveI : BaireSpace U₀ := hU₀.baireSpace
  haveI : Nonempty U₀ := hne.to_subtype
  let F : ℕ → Set U₀ := fun m =>
    ⋂ (κ : Fin (m + 1) → G) (_ : ∀ j, κ j ∈ Q) (x : Fin (m + 1) → G),
      {s : U₀ | (Matrix.of fun i j => u s.1 (x i * κ j)).det = 0}
  have hF : ∀ m, IsClosed (F m) := fun m =>
    isClosed_iInter fun κ => isClosed_iInter fun _ => isClosed_iInter fun x =>
      isClosed_eq ((hcontdet κ x).comp continuous_subtype_val) continuous_const
  have hcover : ⋃ m, F m = Set.univ := by
    refine Set.eq_univ_of_forall fun s => ?_
    obtain ⟨n, hn⟩ := hbound s.1
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iInter.mpr fun κ => Set.mem_iInter.mpr fun hκ =>
      Set.mem_iInter.mpr fun x => hn κ hκ x⟩
  obtain ⟨m, s₀, hs₀⟩ := nonempty_interior_of_iUnion_of_closed hF hcover
  have hU₁open : IsOpen (Subtype.val '' interior (F m)) :=
    hU₀.isOpenMap_subtype_val _ isOpen_interior
  have hU₁sub : Subtype.val '' interior (F m) ⊆ U₀ := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hU₁rank : ∀ s ∈ Subtype.val '' interior (F m), ∀ κ : Fin (m + 1) → G, (∀ j, κ j ∈ Q) →
      ∀ x : Fin (m + 1) → G, (Matrix.of fun i j => u s (x i * κ j)).det = 0 := by
    rintro _ ⟨s, hs, rfl⟩ κ hκ x
    have hsF : s ∈ F m := interior_subset hs
    exact Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hsF κ) hκ) x

  let A : ℕ → Prop := fun n => ∃ s ∈ Subtype.val '' interior (F m), ∃ κ : Fin n → G,
    (∀ j, κ j ∈ Q) ∧ ∃ x : Fin n → G, (Matrix.of fun i j => u s (x i * κ j)).det ≠ 0
  have hA0 : A 0 :=
    ⟨s₀.1, ⟨s₀, hs₀, rfl⟩, Fin.elim0, fun j => Fin.elim0 j, Fin.elim0, by
      rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  obtain ⟨r, hAr, hnot⟩ : ∃ r, A r ∧ ¬ A (r + 1) := by
    refine ⟨Nat.findGreatest A m, Nat.findGreatest_spec (P := A) (Nat.zero_le m) hA0, ?_⟩
    by_cases h : Nat.findGreatest A m + 1 ≤ m
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) h
    · have hrm : Nat.findGreatest A m = m := by
        have := Nat.findGreatest_le (P := A) m
        omega
      rw [hrm]
      rintro ⟨s, hs, κ, hκ, x, hdet⟩
      exact hdet (hU₁rank s hs κ hκ x)
  obtain ⟨s₁, hs₁, κ, hκ, x, hdet₁⟩ := hAr

  refine ⟨Subtype.val '' interior (F m) ∩ {s | (Matrix.of fun i j => u s (x i * κ j)).det ≠ 0},
    hU₁open.inter (isOpen_ne_fun (hcontdet κ x) continuous_const), ⟨s₁, hs₁, hdet₁⟩,
    fun s hs => hU₁sub hs.1, r, κ, x, hκ, fun s hs => hs.2, ?_⟩
  intro s hs k hk
  by_contra hnotmem
  apply hnot
  have hind : LinearIndependent ℂ (fun j => fun g => u s (g * κ j)) :=
    EvalMatrix.linearIndependent_of_det_evalMatrix_ne_zero _ x hs.2
  have hind' : LinearIndependent ℂ
      (Fin.cons (fun g => u s (g * k)) (fun j => fun g => u s (g * κ j)) : Fin (r + 1) → G → ℂ) :=
    linearIndependent_finCons.mpr ⟨hind, hnotmem⟩
  have hfam : (fun j => fun g => u s (g * (Fin.cons k κ : Fin (r + 1) → G) j))
      = (Fin.cons (fun g => u s (g * k)) (fun j => fun g => u s (g * κ j)) : Fin (r + 1) → G → ℂ) := by
    funext j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  obtain ⟨x', hx'⟩ := EvalMatrix.exists_det_evalMatrix_ne_zero
    (fun j => fun g => u s (g * (Fin.cons k κ : Fin (r + 1) → G) j)) (by rw [hfam]; exact hind')
  exact ⟨s, hs.1, Fin.cons k κ, fun j => by refine Fin.cases ?_ (fun j' => ?_) j <;> simp [hk, hκ],
    x', hx'⟩

end UniformRank

namespace CoefficientSpan

variable {Q : Type*} [Monoid Q]

private def coeffSpan {r : ℕ} (ρ : Q → Matrix (Fin r) (Fin r) ℂ) : Submodule ℂ (Q → ℂ) :=
  Submodule.span ℂ (Set.range fun p : Fin r × Fin r => fun q => ρ q p.1 p.2)

omit [Monoid Q] in

private theorem finiteDimensional_coeffSpan {r : ℕ} (ρ : Q → Matrix (Fin r) (Fin r) ℂ) :
    FiniteDimensional ℂ (coeffSpan ρ) :=
  Module.Finite.span_of_finite ℂ (Set.finite_range _)

private theorem span_le_coeffSpan_of_translate {r : ℕ} (b : Fin r → Q → ℂ)
    (ρ : Q → Matrix (Fin r) (Fin r) ℂ)
    (hlaw : ∀ (q x : Q) (j : Fin r), b j (x * q) = ∑ i, ρ q i j * b i x) :
    Submodule.span ℂ (Set.range b) ≤ coeffSpan ρ := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hb : b j = ∑ i, b i 1 • (fun q => ρ q i j) := by
    funext q
    have h := hlaw q 1 j
    rw [one_mul] at h
    rw [h, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hb]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

omit [Monoid Q] in

private theorem coeffSpan_le_of_intertwiner {r : ℕ} (ρ ρ₀ : Q → Matrix (Fin r) (Fin r) ℂ)
    (T : Matrix (Fin r) (Fin r) ℂ) (hT : IsUnit T) (hconj : ∀ q, T * ρ q = ρ₀ q * T) :
    coeffSpan ρ ≤ coeffSpan ρ₀ := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  have hρ : ∀ q, ρ q = T⁻¹ * (ρ₀ q * T) := fun q => by
    rw [← hconj q, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul T hdet, Matrix.one_mul]
  unfold coeffSpan
  rw [Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  have hcoeff : (fun q => ρ q i j)
      = ∑ a, ∑ c, (T⁻¹ i a * T c j) • (fun q => ρ₀ q a c) := by
    funext q
    simp only [hρ q, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  show (fun q => ρ q i j)
      ∈ Submodule.span ℂ (Set.range fun p : Fin r × Fin r => fun q => ρ₀ q p.1 p.2)
  rw [hcoeff]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, c), rfl⟩)

private theorem span_le_coeffSpan_of_intertwiner {r : ℕ} (b : Fin r → Q → ℂ)
    (ρ ρ₀ : Q → Matrix (Fin r) (Fin r) ℂ)
    (hlaw : ∀ (q x : Q) (j : Fin r), b j (x * q) = ∑ i, ρ q i j * b i x)
    (T : Matrix (Fin r) (Fin r) ℂ) (hT : IsUnit T) (hconj : ∀ q, T * ρ q = ρ₀ q * T) :
    Submodule.span ℂ (Set.range b) ≤ coeffSpan ρ₀ :=
  (span_le_coeffSpan_of_translate b ρ hlaw).trans (coeffSpan_le_of_intertwiner ρ ρ₀ T hT hconj)

#print axioms finiteDimensional_coeffSpan
#print axioms span_le_coeffSpan_of_intertwiner

end CoefficientSpan

namespace SliceSpan

variable {G : Type*} [Mul G] {Q : Type*}

private theorem finiteDimensional_pi_const {ι : Type*} [Finite ι] {X : Type*} [AddCommGroup X]
    [Module ℂ X] (W₀ : Submodule ℂ X) [FiniteDimensional ℂ W₀] :
    FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : ι => W₀) :=
  Module.Finite.iff_fg.mpr (Submodule.fg_pi fun _ => Module.Finite.iff_fg.mp inferInstance)

private def slices (ι : Q → G) (reps : Finset G) (f : G → ℂ) : reps → Q → ℂ :=
  fun c q => f (ι q * c)

private theorem exists_forall_mem_exists_forall_eq_sum (ι : Q → G) (reps : Finset G) (H : Set G)
    (K : Set G) (hcover : ∀ k ∈ K, ∃ q : Q, ∃ c ∈ reps, ∃ h ∈ H, k = ι q * c * h)
    (u : ℂ → G → ℂ) (U : Set ℂ) (hinv : ∀ s ∈ U, ∀ g : G, ∀ h ∈ H, u s (g * h) = u s g)
    (V : Submodule ℂ (reps → Q → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ s ∈ U, slices ι reps (u s) ∈ V) :
    ∃ (n : ℕ) (σ : Fin n → ℂ), (∀ i, σ i ∈ U) ∧
      ∀ s ∈ U, ∃ a : Fin n → ℂ, ∀ k ∈ K, u s k = ∑ i, a i * u (σ i) k := by
  classical
  let f : U → (reps → Q → ℂ) := fun s => slices ι reps (u s.1)
  have hle : Submodule.span ℂ (Set.range f) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact hV s.1 s.2
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
    Submodule.finiteDimensional_of_le hle
  obtain ⟨t, htf, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := ℂ) (Set.range f)).mp
    ((Module.Finite.iff_fg (R := ℂ)).mp inferInstance)
  choose par hpar using htf
  let pick : t → U := fun w => par w.2
  have hpick : ∀ w : t, slices ι reps (u (pick w).1) = w.1 := fun w => hpar w.2
  let e := t.equivFin
  refine ⟨t.card, fun i => (pick (e.symm i)).1, fun i => (pick (e.symm i)).2, fun s hs => ?_⟩
  have hsub : Submodule.span ℂ (t : Set (reps → Q → ℂ))
      ≤ Submodule.span ℂ (Set.range fun i => slices ι reps (u (pick (e.symm i)).1)) := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨i, hi⟩ : ∃ i, e.symm i = ⟨v, hv⟩ := ⟨e ⟨v, hv⟩, e.symm_apply_apply _⟩
    refine Submodule.subset_span ⟨i, ?_⟩
    show slices ι reps (u (pick (e.symm i)).1) = v
    rw [hi]
    exact hpick ⟨v, hv⟩
  have h1 : slices ι reps (u s) ∈ Submodule.span ℂ (Set.range f) :=
    Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
  rw [hspan] at h1
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hsub h1)
  refine ⟨a, fun k hk => ?_⟩
  obtain ⟨q, c, hc, h, hh, rfl⟩ := hcover k hk
  rw [hinv s hs _ h hh]
  simp only [fun i => hinv _ (pick (e.symm i)).2 (ι q * c) h hh]
  have hcq := congrFun (congrFun ha ⟨c, hc⟩) q
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, slices] at hcq
  exact hcq.symm

#print axioms finiteDimensional_pi_const
#print axioms exists_forall_mem_exists_forall_eq_sum

end SliceSpan

namespace SliceCoefficients

variable {G : Type*} [Monoid G] {Q : Type*} [Monoid Q]

private theorem slices_mem_pi_coeffSpan {r : ℕ} (ι : Q →* G) (reps : Finset G)
    (hcomm : ∀ (q : Q), ∀ c ∈ reps, ι q * c = c * ι q)
    (u : ℂ → G → ℂ) (κ : Fin r → Q) (ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ)
    (ρ₀ : Q → Matrix (Fin r) (Fin r) ℂ) (U W : Set ℂ) (hWU : W ⊆ U)
    (hspan : ∀ s ∈ U, ∀ q : Q, (fun g => u s (g * ι q)) ∈
      Submodule.span ℂ (Set.range fun j => fun g => u s (g * ι (κ j))))
    (hlaw : ∀ s ∈ U, ∀ (q : Q) (g : G) (j : Fin r),
      u s (g * ι q * ι (κ j)) = ∑ i, ρ s q i j * u s (g * ι (κ i)))
    (hT : ∀ s ∈ W, ∃ T : Matrix (Fin r) (Fin r) ℂ, IsUnit T ∧ ∀ q : Q, T * ρ s q = ρ₀ q * T) :
    ∀ s ∈ W, SliceSpan.slices (⇑ι) reps (u s) ∈
      Submodule.pi Set.univ (fun _ : reps => CoefficientSpan.coeffSpan ρ₀) := by
  intro s hs
  obtain ⟨T, hTu, hconj⟩ := hT s hs
  rw [Submodule.mem_pi]
  intro c _
  show (fun x : Q => u s (ι x * (c : G))) ∈ CoefficientSpan.coeffSpan ρ₀
  refine CoefficientSpan.span_le_coeffSpan_of_intertwiner
    (fun j x => u s (ι x * (c : G) * ι (κ j))) (ρ s) ρ₀ ?_ T hTu hconj ?_
  · intro q x j
    show u s (ι (x * q) * (c : G) * ι (κ j)) = ∑ i, ρ s q i j * u s (ι x * (c : G) * ι (κ i))
    rw [map_mul, mul_assoc (ι x) (ι q) (c : G), hcomm q c c.2, ← mul_assoc]
    exact hlaw s (hWU hs) q (ι x * (c : G)) j
  · obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hspan s (hWU hs) 1)
    have hfun : (fun x : Q => u s (ι x * (c : G)))
        = ∑ j, d j • (fun x : Q => u s (ι x * (c : G) * ι (κ j))) := by
      funext x
      have h := congrFun hd (ι x * (c : G))
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_one, mul_one] at h ⊢
      exact h.symm
    rw [hfun]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end SliceCoefficients

namespace ArchimedeanIsometryGroup

private theorem norm_entry_le_one {K : Type*} [NormedField K] {k : GL (Fin 2) K} (hk : IsRowIsometry k)
    (i j : Fin 2) : ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1 := by
  obtain ⟨-, hrow⟩ := hk
  have h0 := hrow 1 0
  have h1 := hrow 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, norm_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at h0 h1
  have n00 := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) K) 0 0)
  have n01 := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) K) 0 1)
  have n10 := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) K) 1 0)
  have n11 := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) K) 1 1)
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> nlinarith

private theorem isClosed_setOf_isRowIsometry {K : Type*} [NormedField K] :
    IsClosed {k : GL (Fin 2) K | IsRowIsometry k} := by
  have hc : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have hset : {k : GL (Fin 2) K | IsRowIsometry k}
      = {k : GL (Fin 2) K | ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1}
        ∩ ⋂ (x : K) (y : K), {k : GL (Fin 2) K |
            ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
              + ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
              = ‖x‖ ^ 2 + ‖y‖ ^ 2} := by
    ext k
    simp only [IsRowIsometry, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine (isClosed_eq Units.continuous_val.matrix_det.norm continuous_const).inter ?_
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
  exact (((continuous_const.mul (hc 0 0)).add (continuous_const.mul (hc 1 0))).norm.pow 2).add
    (((continuous_const.mul (hc 0 1)).add (continuous_const.mul (hc 1 1))).norm.pow 2)

private theorem isClosed_range_embedProduct {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    [T2Space M] : IsClosed (Set.range (Units.embedProduct M)) := by
  have hr : Set.range (Units.embedProduct M)
      = {p : M × Mᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨u, hu⟩
      simp only [Units.embedProduct_apply, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      simp
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, b.unop, h1, h2⟩, by simp [Units.embedProduct_apply]⟩
  rw [hr]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

variable (F : Type) [Field F]

private noncomputable def Kinf : Subgroup (GL (Fin 2) (InfiniteAdeleRing F)) :=
  ⨅ w : InfinitePlace F, (rowIsometrySubgroup w.Completion).comap (archComponent F w)

variable {F}

private theorem mem_Kinf_iff (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    k ∈ Kinf F ↔ ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w k) := by
  simp only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap, mem_rowIsometrySubgroup_iff]

variable (F)

private theorem isClosed_Kinf : IsClosed (Kinf F : Set (GL (Fin 2) (InfiniteAdeleRing F))) := by
  have hset : (Kinf F : Set (GL (Fin 2) (InfiniteAdeleRing F)))
      = ⋂ w : InfinitePlace F, archComponent F w ⁻¹' {k | IsRowIsometry k} := by
    ext k
    simp only [SetLike.mem_coe, mem_Kinf_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  exact isClosed_iInter fun w => isClosed_setOf_isRowIsometry.preimage (continuous_archComponent F w)

private def box : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  {m | ∀ (i j : Fin 2) (w : InfinitePlace F), ‖m i j w‖ ≤ 1}

private theorem properSpace_completion_w (w : InfinitePlace F) : ProperSpace w.Completion :=
  NumberField.AdelicBox.properSpace_completion F w

private theorem isCompact_box : IsCompact (box F) := by
  haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion := properSpace_completion_w F
  have hset : box F = Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 =>
      Set.pi Set.univ (fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1))) := by
    ext m
    constructor
    · intro h i _ j _ w _
      exact mem_closedBall_zero_iff.2 (h i j w)
    · intro h i j w
      exact mem_closedBall_zero_iff.1 (h i (Set.mem_univ i) j (Set.mem_univ j) w (Set.mem_univ w))
  rw [hset]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _

private theorem coe_mem_box {k : GL (Fin 2) (InfiniteAdeleRing F)} (hk : k ∈ Kinf F) :
    (k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ box F :=
  fun i j w => norm_entry_le_one ((mem_Kinf_iff k).1 hk w) i j

private theorem isCompact_Kinf : IsCompact (Kinf F : Set (GL (Fin 2) (InfiniteAdeleRing F))) := by
  rw [Units.isInducing_embedProduct.isCompact_iff]
  refine ((isCompact_box F).prod ((isCompact_box F).image MulOpposite.continuous_op)).of_isClosed_subset ?_ ?_
  · exact (Topology.IsClosedEmbedding.mk Units.isEmbedding_embedProduct isClosed_range_embedProduct).isClosedMap _
      (isClosed_Kinf F)
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨coe_mem_box F hk, ⟨((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)),
      coe_mem_box F ((Kinf F).inv_mem hk), rfl⟩⟩

private scoped instance instCompactSpaceKinf : CompactSpace (Kinf F) :=
  isCompact_iff_compactSpace.mp (isCompact_Kinf F)

private noncomputable scoped instance instMeasurableSpaceKinf : MeasurableSpace (Kinf F) := borel _

private scoped instance instBorelSpaceKinf : BorelSpace (Kinf F) := ⟨rfl⟩

private noncomputable def haarProb : Measure (Kinf F) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Kinf F))

private scoped instance instIsProbabilityMeasureHaarProb : IsProbabilityMeasure (haarProb F) :=
  ⟨by
    have h := Measure.haarMeasure_self (G := Kinf F) (K₀ := ⊤)
    simpa [haarProb] using h⟩

private scoped instance instIsMulLeftInvariantHaarProb : (haarProb F).IsMulLeftInvariant := by
  unfold haarProb
  infer_instance

end ArchimedeanIsometryGroup
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

namespace ArchimedeanIsometryGroup

variable (F : Type) [Field F] [NumberField F]

private noncomputable def incl : Kinf F →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (Kinf F).subtype

private theorem translatesFinite_archRowIsometrySubgroup (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsArchKFiniteAt F w φ) :
    UniformRank.TranslatesFinite (archRowIsometrySubgroup F w : Set (AdelicGL2 (𝓞 F) F)) φ := by
  obtain ⟨s, hs⟩ := hφ
  exact Exists.intro s fun k hk => hs k hk

private theorem eq_of_forall_archComponent_eq {k k' : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w k = archComponent F w k') : k = k' := by
  have _ := ‹NumberField F›
  refine Units.ext ((archMatrixPiEquiv F).injective (funext fun w => Matrix.ext fun i j => ?_))
  exact congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

private theorem adelicArchGLInclAt_mul_comm {v w : InfinitePlace F} (hvw : v ≠ w) (a : GL (Fin 2) v.Completion)
    (b : GL (Fin 2) w.Completion) :
    adelicArchGLInclAt F v a * adelicArchGLInclAt F w b = adelicArchGLInclAt F w b * adelicArchGLInclAt F v a := by
  have hcomm : archGLIncl F v a * archGLIncl F w b = archGLIncl F w b * archGLIncl F v a := by
    refine eq_of_forall_archComponent_eq F fun u => ?_
    rw [map_mul, map_mul]
    by_cases huv : u = v
    · subst huv
      rw [archComponent_archGLIncl_self, archComponent_archGLIncl_of_ne F hvw, mul_one, one_mul]
    · rw [archComponent_archGLIncl_of_ne F huv]
      by_cases huw : u = w
      · subst huw
        rw [archComponent_archGLIncl_self, one_mul, mul_one]
      · rw [archComponent_archGLIncl_of_ne F huw]
  show adelicArchGLIncl F (archGLIncl F v a) * adelicArchGLIncl F (archGLIncl F w b) =
    adelicArchGLIncl F (archGLIncl F w b) * adelicArchGLIncl F (archGLIncl F v a)
  rw [← map_mul, ← map_mul, hcomm]

private theorem exists_mem_Kinf_eq_archGLIncl_mul (w : InfinitePlace F) {k : GL (Fin 2) (InfiniteAdeleRing F)}
    (hk : k ∈ Kinf F) :
    ∃ k' ∈ Kinf F, archComponent F w k' = 1 ∧ (∀ v : InfinitePlace F, v ≠ w → archComponent F v k' = archComponent F v k) ∧
      k = archGLIncl F w (archComponent F w k) * k' := by
  have _ := ‹NumberField F›
  have hrow : ∀ u : InfinitePlace F, archComponent F u k ∈ rowIsometrySubgroup u.Completion := by
    simpa only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap] using hk
  refine ⟨(archGLIncl F w (archComponent F w k))⁻¹ * k, ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩
  · simp only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro u
    rw [map_mul, map_inv]
    by_cases huw : u = w
    · subst huw
      rw [archComponent_archGLIncl_self, inv_mul_cancel]
      exact one_mem _
    · rw [archComponent_archGLIncl_of_ne F huw, inv_one, one_mul]
      exact hrow u
  · rw [map_mul, map_inv, archComponent_archGLIncl_self, inv_mul_cancel]
  · intro v hvw
    rw [map_mul, map_inv, archComponent_archGLIncl_of_ne F hvw, inv_one, one_mul]

private theorem translatesFinite_range_incl (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchKFinite F φ) :
    UniformRank.TranslatesFinite (Set.range (incl F)) φ := by
  classical
  have hmono : ∀ {Q Q' : Set (AdelicGL2 (𝓞 F) F)}, Q' ⊆ Q →
      UniformRank.TranslatesFinite Q φ → UniformRank.TranslatesFinite Q' φ :=
    fun hQ h => Exists.imp (fun _t ht k hk => ht k (hQ hk)) h
  let P : Finset (InfinitePlace F) → Set (AdelicGL2 (𝓞 F) F) := fun S =>
    {g | ∃ k ∈ Kinf F, (∀ v : InfinitePlace F, v ∉ S → archComponent F v k = 1) ∧ g = adelicArchGLIncl F k}
  have hP : ∀ S : Finset (InfinitePlace F), UniformRank.TranslatesFinite (P S) φ := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · refine hmono (Q := {1}) ?_ (Exists.intro {φ} fun k hk => ?_)
      · rintro g ⟨k, -, hk1, rfl⟩
        have hk : k = 1 := eq_of_forall_archComponent_eq F fun v => by rw [hk1 v (by simp), map_one]
        rw [hk, map_one]
        exact Set.mem_singleton 1
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        simp only [mul_one]
        exact Submodule.subset_span (by simp)
    · intro w S hw ih
      refine hmono ?_
        (UniformRank.translatesFinite_mul _ _ ?_ φ (translatesFinite_archRowIsometrySubgroup F w φ (hφ w)) ih)
      · rintro g ⟨k, hk, hk1, rfl⟩
        obtain ⟨k', hk'mem, hk'w, hk'v, hkeq⟩ := exists_mem_Kinf_eq_archGLIncl_mul F w hk
        have hrow : archComponent F w k ∈ rowIsometrySubgroup w.Completion := by
          have hk2 := hk
          simp only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap] at hk2
          exact hk2 w
        have h₁ : adelicArchGLIncl F (archGLIncl F w (archComponent F w k)) ∈
            (archRowIsometrySubgroup F w : Set (AdelicGL2 (𝓞 F) F)) :=
          Subgroup.mem_map_of_mem (adelicArchGLInclAt F w) hrow
        have h₂ : adelicArchGLIncl F k' ∈ P S := by
          show ∃ k₀ ∈ Kinf F, (∀ v : InfinitePlace F, v ∉ S → archComponent F v k₀ = 1) ∧
            adelicArchGLIncl F k' = adelicArchGLIncl F k₀
          refine ⟨k', hk'mem, fun v hv => ?_, rfl⟩
          by_cases hvw : v = w
          · subst hvw
            exact hk'w
          · rw [hk'v v hvw]
            exact hk1 v fun h => hv (Finset.mem_of_mem_insert_of_ne h hvw)
        rw [hkeq, map_mul]
        exact Set.mul_mem_mul h₁ h₂
      · intro a ha g hg
        obtain ⟨k', -, hk'1, rfl⟩ := hg
        simp only [archRowIsometrySubgroup, SetLike.mem_coe, Subgroup.mem_map] at ha
        obtain ⟨a₀, -, rfl⟩ := ha
        have hcomm : archGLIncl F w a₀ * k' = k' * archGLIncl F w a₀ := by
          refine eq_of_forall_archComponent_eq F fun u => ?_
          rw [map_mul, map_mul]
          by_cases huw : u = w
          · subst huw
            rw [archComponent_archGLIncl_self, hk'1 u hw, mul_one, one_mul]
          · rw [archComponent_archGLIncl_of_ne F huw, one_mul, mul_one]
        show adelicArchGLIncl F (archGLIncl F w a₀) * adelicArchGLIncl F k' =
          adelicArchGLIncl F k' * adelicArchGLIncl F (archGLIncl F w a₀)
        rw [← map_mul, ← map_mul, hcomm]
  have hrange : Set.range (incl F) ⊆ P Finset.univ := by
    rintro g ⟨⟨k, hk⟩, rfl⟩
    show ∃ k₀ ∈ Kinf F, (∀ v : InfinitePlace F, v ∉ Finset.univ → archComponent F v k₀ = 1) ∧
      incl F ⟨k, hk⟩ = adelicArchGLIncl F k₀
    exact ⟨k, hk, fun v hv => (hv (Finset.mem_univ v)).elim, rfl⟩
  exact hmono hrange (hP Finset.univ)

private theorem continuous_incl : Continuous (incl F) :=
  Units.continuous_iff.mpr
    ⟨continuous_matrix fun i j => by
        show Continuous fun q : Kinf F =>
          ((⟨((q : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j⟩ : AdeleRing (𝓞 F) F))
        exact ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j).prodMk continuous_const,
      continuous_matrix fun i j => by
        show Continuous fun q : Kinf F =>
          ((⟨(((q : GL (Fin 2) (InfiniteAdeleRing F))⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) :
              Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j⟩ : AdeleRing (𝓞 F) F))
        exact ((Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem i j).prodMk continuous_const⟩

private theorem incl_mul_comm_of_glArch_eq_one (q : Kinf F) (c : AdelicGL2 (𝓞 F) F)
    (hc : glArch (𝓞 F) F c = 1) : incl F q * c = c * incl F q := by
  have hA : glArch (𝓞 F) F (incl F q * c) = glArch (𝓞 F) F (c * incl F q) := by
    rw [map_mul, map_mul, hc, mul_one, one_mul]
  have hF : glFin (𝓞 F) F (incl F q * c) = glFin (𝓞 F) F (c * incl F q) := by
    have h1 : glFin (𝓞 F) F (incl F q) = 1 := glFin_adelicArchGLIncl F _
    rw [map_mul, map_mul, h1, mul_one, one_mul]
  have hA' : (glArch (𝓞 F) F (incl F q * c) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) =
      glArch (𝓞 F) F (c * incl F q) := by
    rw [hA]
  have hF' : (glFin (𝓞 F) F (incl F q * c) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) =
      glFin (𝓞 F) F (c * incl F q) := by
    rw [hF]
  ext i j
  exact Prod.ext (congrFun (congrFun hA' i) j) (congrFun (congrFun hF' i) j)

private theorem exists_exists_mem_exists_mem_eq_incl_mul_mul (T : Finset (AdelicGL2 (𝓞 F) F))
    (H : Set (AdelicGL2 (𝓞 F) F))
    (hT : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      ∃ g ∈ T, ∃ h ∈ H, k = g * h)
    (k : AdelicGL2 (𝓞 F) F) (hk₁ : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F)
    (hk₂ : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) :
    ∃ q : Kinf F, ∃ c ∈ T, ∃ h ∈ H, k = incl F q * c * h := by
  have hq : glArch (𝓞 F) F k ∈ Kinf F := by
    simp only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap, mem_rowIsometrySubgroup_iff]
    exact hk₂
  have h1 : glArch (𝓞 F) F ((adelicArchGLIncl F (glArch (𝓞 F) F k))⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]
  have h2 : glFin (𝓞 F) F ((adelicArchGLIncl F (glArch (𝓞 F) F k))⁻¹ * k) ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
    exact hk₁
  obtain ⟨c, hc, h, hh, hk'⟩ := hT _ h1 h2
  refine ⟨⟨glArch (𝓞 F) F k, hq⟩, c, hc, h, hh, ?_⟩
  show k = adelicArchGLIncl F (glArch (𝓞 F) F k) * c * h
  rw [mul_assoc, ← hk', mul_inv_cancel_left]

end ArchimedeanIsometryGroup
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

namespace AveragedIntertwiner

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]

section Body

variable {r : ℕ} {U : Set ℂ} {ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ}

omit [Group Q] [IsTopologicalGroup Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
private theorem continuous_of_mem
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s : ℂ} (hs : s ∈ U) :
    Continuous (ρ s) := by
  have h : ContinuousOn ((fun p : ℂ × Q => ρ p.1 p.2) ∘ fun q : Q => (s, q)) Set.univ :=
    hρ_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun q _ => ⟨hs, Set.mem_univ q⟩)
  exact continuousOn_univ.mp h

private noncomputable def kern (ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ) (s₀ s : ℂ) (q : Q) :
    Matrix (Fin r) (Fin r) ℂ :=
  ρ s₀ q * ρ s q⁻¹

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
private theorem continuous_kern
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ s : ℂ}
    (hs₀ : s₀ ∈ U) (hs : s ∈ U) : Continuous (kern ρ s₀ s) := by
  unfold kern
  exact (continuous_of_mem hρ_cont hs₀).matrix_mul ((continuous_of_mem hρ_cont hs).comp continuous_inv)

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
private theorem continuousOn_kern
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (i j : Fin r) : ContinuousOn (fun p : ℂ × Q => kern ρ s₀ p.1 p.2 i j) (U ×ˢ Set.univ) := by
  have h1 : ContinuousOn (fun p : ℂ × Q => ρ s₀ p.2) (U ×ˢ Set.univ) :=
    ((continuous_of_mem hρ_cont hs₀).comp continuous_snd).continuousOn
  have h2 : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2⁻¹) (U ×ˢ Set.univ) :=
    hρ_cont.comp (continuous_fst.prodMk continuous_snd.inv).continuousOn
      (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  rw [continuousOn_iff_continuous_restrict] at h1 h2 ⊢
  exact (h1.matrix_mul h2).matrix_elem i j

variable (μ : Measure Q) [IsProbabilityMeasure μ]

private theorem integrable_kern
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ s : ℂ}
    (hs₀ : s₀ ∈ U) (hs : s ∈ U) (i j : Fin r) : Integrable (fun q => kern ρ s₀ s q i j) μ := by
  rw [← integrableOn_univ]
  exact ((continuous_kern hρ_cont hs₀ hs).matrix_elem i j).continuousOn.integrableOn_compact'
    isCompact_univ MeasurableSet.univ

private noncomputable def avg (ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ) (s₀ s : ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ∫ q, kern ρ s₀ s q i j ∂μ

omit [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [BorelSpace Q] in
private theorem avg_self (hρ_one : ∀ s ∈ U, ρ s 1 = 1)
    (hρ_mul : ∀ s ∈ U, ∀ q q' : Q, ρ s (q * q') = ρ s q * ρ s q') {s₀ : ℂ} (hs₀ : s₀ ∈ U) :
    avg μ ρ s₀ s₀ = 1 := by
  have h : ∀ q : Q, kern ρ s₀ s₀ q = 1 := fun q => by
    rw [kern, ← hρ_mul s₀ hs₀, mul_inv_cancel, hρ_one s₀ hs₀]
  ext i j
  simp only [avg, Matrix.of_apply, h, integral_const, probReal_univ, one_smul]

private theorem avg_mul [μ.IsMulLeftInvariant]
    (hρ_mul : ∀ s ∈ U, ∀ q q' : Q, ρ s (q * q') = ρ s q * ρ s q')
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ s : ℂ}
    (hs₀ : s₀ ∈ U) (hs : s ∈ U) (q' : Q) : avg μ ρ s₀ s * ρ s q' = ρ s₀ q' * avg μ ρ s₀ s := by
  ext i j
  have hL : (avg μ ρ s₀ s * ρ s q') i j = ∫ q, (kern ρ s₀ s q * ρ s q') i j ∂μ := by
    simp only [Matrix.mul_apply, avg, Matrix.of_apply]
    rw [integral_finsetSum _ (fun k _ => (integrable_kern μ hρ_cont hs₀ hs i k).mul_const (ρ s q' k j))]
    simp only [integral_mul_const]
  have hR : (ρ s₀ q' * avg μ ρ s₀ s) i j = ∫ q, (ρ s₀ q' * kern ρ s₀ s q) i j ∂μ := by
    simp only [Matrix.mul_apply, avg, Matrix.of_apply]
    rw [integral_finsetSum _ (fun k _ => (integrable_kern μ hρ_cont hs₀ hs k j).const_mul (ρ s₀ q' i k))]
    simp only [integral_const_mul]
  have h1 : ∀ q : Q, kern ρ s₀ s q * ρ s q' = ρ s₀ q * ρ s (q⁻¹ * q') := fun q => by
    rw [kern, mul_assoc, hρ_mul s hs]
  have h2 : ∀ q : Q, ρ s₀ q' * kern ρ s₀ s q = ρ s₀ (q' * q) * ρ s q⁻¹ := fun q => by
    rw [kern, ← mul_assoc, hρ_mul s₀ hs₀]
  rw [hL, hR]
  simp only [h1, h2]
  calc ∫ q, (ρ s₀ q * ρ s (q⁻¹ * q')) i j ∂μ
      = ∫ q, (ρ s₀ (q' * q) * ρ s ((q' * q)⁻¹ * q')) i j ∂μ :=
        (integral_mul_left_eq_self (μ := μ) (fun q => (ρ s₀ q * ρ s (q⁻¹ * q')) i j) q').symm
    _ = ∫ q, (ρ s₀ (q' * q) * ρ s q⁻¹) i j ∂μ := by
        congr 1
        funext q
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

private theorem continuousAt_avg (hU : IsOpen U)
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ U) : ContinuousAt (fun s => avg μ ρ s₀ s) s₀ := by
  obtain ⟨N, hN_nhds, hNU, hN_cpt⟩ := local_compact_nhds (hU.mem_nhds hs₀)
  refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
  simp only [avg, Matrix.of_apply]
  have hK := continuousOn_kern hρ_cont hs₀ i j
  obtain ⟨C, hC⟩ :=
    (hN_cpt.prod isCompact_univ).exists_bound_of_continuousOn
      (hK.mono (Set.prod_mono hNU Set.Subset.rfl))
  refine continuousAt_of_dominated (F := fun s q => kern ρ s₀ s q i j) (bound := fun _ => C)
    ?_ ?_ (integrable_const C) ?_
  · filter_upwards [hU.mem_nhds hs₀] with s hs
    exact ((continuous_kern hρ_cont hs₀ hs).matrix_elem i j).aestronglyMeasurable
  · filter_upwards [hN_nhds] with s hs
    exact ae_of_all μ fun q => hC (s, q) ⟨hs, Set.mem_univ q⟩
  · refine ae_of_all μ fun q => ?_
    have hat : ContinuousAt (fun p : ℂ × Q => kern ρ s₀ p.1 p.2 i j) (s₀, q) :=
      hK.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hs₀, Set.mem_univ q⟩)
    have hf : ContinuousAt (fun s : ℂ => (s, q)) s₀ := (continuous_id.prodMk continuous_const).continuousAt
    exact ContinuousAt.comp (g := fun p : ℂ × Q => kern ρ s₀ p.1 p.2 i j) (f := fun s : ℂ => (s, q))
      (x := s₀) hat hf

end Body
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

private theorem exists_isOpen_forall_exists_isUnit_mul_eq_mul
    (μ : Measure Q) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (r : ℕ) (U : Set ℂ) (hU : IsOpen U) (ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ)
    (hρ_one : ∀ s ∈ U, ρ s 1 = 1)
    (hρ_mul : ∀ s ∈ U, ∀ q q' : Q, ρ s (q * q') = ρ s q * ρ s q')
    (hρ_cont : ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ)) :
    ∀ s₀ ∈ U, ∃ U' : Set ℂ, IsOpen U' ∧ s₀ ∈ U' ∧ U' ⊆ U ∧
      ∀ s ∈ U', ∃ T : Matrix (Fin r) (Fin r) ℂ, IsUnit T ∧ ∀ q : Q, T * ρ s q = ρ s₀ q * T := by
  intro s₀ hs₀
  have hdet : ContinuousAt (fun s => (avg μ ρ s₀ s).det) s₀ :=
    (continuous_id.matrix_det).continuousAt.comp (continuousAt_avg μ hU hρ_cont hs₀)
  have h1 : (avg μ ρ s₀ s₀).det ≠ 0 := by
    rw [avg_self μ hρ_one hρ_mul hs₀, Matrix.det_one]
    exact one_ne_zero
  have hUev : ∀ᶠ s in nhds s₀, s ∈ U := Filter.eventually_mem_set.2 (hU.mem_nhds hs₀)
  have hev : {s : ℂ | s ∈ U ∧ (avg μ ρ s₀ s).det ≠ 0} ∈ nhds s₀ := hUev.and (hdet.eventually_ne h1)
  obtain ⟨V, hV, hV_open, hs₀V⟩ := mem_nhds_iff.mp hev
  refine ⟨V, hV_open, hs₀V, fun s hs => ?_, fun s hs => ?_⟩
  · have hs' : s ∈ U ∧ (avg μ ρ s₀ s).det ≠ 0 := hV hs
    exact hs'.1
  · have hs' : s ∈ U ∧ (avg μ ρ s₀ s).det ≠ 0 := hV hs
    refine ⟨avg μ ρ s₀ s, ?_, fun q => avg_mul μ hρ_mul hρ_cont hs₀ hs'.1 q⟩
    exact (Matrix.isUnit_iff_isUnit_det (avg μ ρ s₀ s)).2 (isUnit_iff_ne_zero.2 hs'.2)

end AveragedIntertwiner
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

namespace TranslationCoordinates

section Algebra

variable {G : Type*} [Monoid G] {Q : Type*} [Monoid Q] {r : ℕ}

private noncomputable def Mm (ι : Q →* G) (u : ℂ → G → ℂ) (κ : Fin r → Q) (x : Fin r → G) (s : ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => u s (x i * ι (κ j))

private noncomputable def Nm (ι : Q →* G) (u : ℂ → G → ℂ) (κ : Fin r → Q) (x : Fin r → G) (s : ℂ)
    (q : Q) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k j => u s (x k * ι q * ι (κ j))

variable (ι : Q →* G) (u : ℂ → G → ℂ) (κ : Fin r → Q) (x : Fin r → G) {s : ℂ}

private theorem Nm_one (s : ℂ) : Nm ι u κ x s 1 = Mm ι u κ x s := by
  ext k j
  simp only [Nm, Mm, Matrix.of_apply, map_one, mul_one]

private theorem eval_sum (e : Fin r → ℂ) :
    (fun k => ∑ i, e i * u s (x k * ι (κ i))) = (Mm ι u κ x s).mulVec e := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Mm, Matrix.of_apply, mul_comm]

private theorem inv_mulVec_mulVec (hdet : (Mm ι u κ x s).det ≠ 0) (e : Fin r → ℂ) :
    (Mm ι u κ x s)⁻¹.mulVec ((Mm ι u κ x s).mulVec e) = e := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

private theorem coeff_unique (hdet : (Mm ι u κ x s).det ≠ 0) {c d : Fin r → ℂ}
    (h : ∀ g : G, ∑ i, c i * u s (g * ι (κ i)) = ∑ i, d i * u s (g * ι (κ i))) : c = d := by
  have hM : (Mm ι u κ x s).mulVec c = (Mm ι u κ x s).mulVec d := by
    rw [← eval_sum ι u κ x, ← eval_sum ι u κ x]
    funext k
    exact h (x k)
  calc c = (Mm ι u κ x s)⁻¹.mulVec ((Mm ι u κ x s).mulVec c) := (inv_mulVec_mulVec ι u κ x hdet c).symm
    _ = (Mm ι u κ x s)⁻¹.mulVec ((Mm ι u κ x s).mulVec d) := by rw [hM]
    _ = d := inv_mulVec_mulVec ι u κ x hdet d

private theorem law (hdet : (Mm ι u κ x s).det ≠ 0)
    (hspan : ∀ q : Q, (fun g => u s (g * ι q)) ∈
      Submodule.span ℂ (Set.range fun j => fun g => u s (g * ι (κ j))))
    (q : Q) (g : G) (j : Fin r) :
    u s (g * ι q * ι (κ j)) = ∑ i, ((Mm ι u κ x s)⁻¹ * Nm ι u κ x s q) i j * u s (g * ι (κ i)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hspan (q * κ j))
  have hc' : ∀ g' : G, u s (g' * ι q * ι (κ j)) = ∑ i, c i * u s (g' * ι (κ i)) := by
    intro g'
    have h := congrFun hc g'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul, ← mul_assoc] at h
    exact h.symm
  have hcol : c = fun i => ((Mm ι u κ x s)⁻¹ * Nm ι u κ x s q) i j := by
    have h1 : (Mm ι u κ x s).mulVec c = fun k => u s (x k * ι q * ι (κ j)) := by
      rw [← eval_sum ι u κ x]
      funext k
      exact (hc' (x k)).symm
    rw [← inv_mulVec_mulVec ι u κ x hdet c, h1]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Nm, Matrix.of_apply]
  rw [hc' g, hcol]

private theorem mul_of_laws (hdet : (Mm ι u κ x s).det ≠ 0) (q q' : Q)
    {A B C : Matrix (Fin r) (Fin r) ℂ}
    (hA : ∀ (g : G) (j : Fin r), u s (g * ι q * ι (κ j)) = ∑ i, A i j * u s (g * ι (κ i)))
    (hB : ∀ (g : G) (j : Fin r), u s (g * ι q' * ι (κ j)) = ∑ i, B i j * u s (g * ι (κ i)))
    (hC : ∀ (g : G) (j : Fin r), u s (g * ι (q * q') * ι (κ j)) = ∑ i, C i j * u s (g * ι (κ i))) :
    C = A * B := by
  ext i j
  have hcol : (fun i => C i j) = fun i => (A * B) i j := by
    refine coeff_unique ι u κ x hdet fun g => ?_
    show ∑ i, C i j * u s (g * ι (κ i)) = ∑ i, (A * B) i j * u s (g * ι (κ i))
    rw [← hC g j, map_mul, ← mul_assoc, hB (g * ι q) j]
    simp only [hA g, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  exact congrFun hcol i

end Algebra
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

section Continuity

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
variable {Q : Type*} [Monoid Q] [TopologicalSpace Q] {r : ℕ}
variable (ι : Q →* G) (u : ℂ → G → ℂ) (κ : Fin r → Q) (x : Fin r → G)

omit [ContinuousMul G] [TopologicalSpace Q] in
private theorem continuous_Mm (hu : Continuous fun p : ℂ × G => u p.1 p.2) :
    Continuous fun s : ℂ => Mm ι u κ x s := by
  refine continuous_matrix fun i j => ?_
  simp only [Mm, Matrix.of_apply]
  exact hu.comp (continuous_id.prodMk continuous_const)

private theorem continuous_Nm (hι : Continuous ι) (hu : Continuous fun p : ℂ × G => u p.1 p.2) :
    Continuous fun p : ℂ × Q => Nm ι u κ x p.1 p.2 := by
  refine continuous_matrix fun k j => ?_
  simp only [Nm, Matrix.of_apply]
  have h : Continuous fun p : ℂ × Q => x k * ι p.2 * ι (κ j) :=
    (continuous_const.mul (hι.comp continuous_snd)).mul continuous_const
  exact hu.comp (continuous_fst.prodMk h)

end Continuity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
variable {Q : Type*} [Monoid Q] [TopologicalSpace Q]

private theorem exists_forall_one_and_mul_and_continuousOn_and_eq_sum
    (ι : Q →* G) (hι : Continuous ι) (u : ℂ → G → ℂ) (hu : Continuous fun p : ℂ × G => u p.1 p.2)
    (U : Set ℂ) (r : ℕ) (κ : Fin r → Q) (x : Fin r → G)
    (hdet : ∀ s ∈ U, (Matrix.of fun i j => u s (x i * ι (κ j))).det ≠ 0)
    (hspan : ∀ s ∈ U, ∀ q : Q, (fun g => u s (g * ι q)) ∈
      Submodule.span ℂ (Set.range fun j => fun g => u s (g * ι (κ j)))) :
    ∃ ρ : ℂ → Q → Matrix (Fin r) (Fin r) ℂ,
      (∀ s ∈ U, ρ s 1 = 1) ∧
      (∀ s ∈ U, ∀ q q' : Q, ρ s (q * q') = ρ s q * ρ s q') ∧
      ContinuousOn (fun p : ℂ × Q => ρ p.1 p.2) (U ×ˢ Set.univ) ∧
      ∀ s ∈ U, ∀ (q : Q) (g : G) (j : Fin r),
        u s (g * ι q * ι (κ j)) = ∑ i, ρ s q i j * u s (g * ι (κ i)) := by
  have hdetM : ∀ s ∈ U, (Mm ι u κ x s).det ≠ 0 := hdet
  refine ⟨fun s q => (Mm ι u κ x s)⁻¹ * Nm ι u κ x s q, ?_, ?_, ?_, ?_⟩
  · intro s hs
    show (Mm ι u κ x s)⁻¹ * Nm ι u κ x s 1 = 1
    rw [Nm_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdetM s hs))]
  · intro s hs q q'
    show (Mm ι u κ x s)⁻¹ * Nm ι u κ x s (q * q') =
      (Mm ι u κ x s)⁻¹ * Nm ι u κ x s q * ((Mm ι u κ x s)⁻¹ * Nm ι u κ x s q')
    exact mul_of_laws ι u κ x (hdetM s hs) q q' (law ι u κ x (hdetM s hs) (hspan s hs) q)
      (law ι u κ x (hdetM s hs) (hspan s hs) q') (law ι u κ x (hdetM s hs) (hspan s hs) (q * q'))
  · show ContinuousOn (fun p : ℂ × Q => (Mm ι u κ x p.1)⁻¹ * Nm ι u κ x p.1 p.2) (U ×ˢ Set.univ)
    have hN := continuous_Nm ι u κ x hι hu
    have hM := continuous_Mm ι u κ x hu
    have hinv : ContinuousOn (fun s : ℂ => (Mm ι u κ x s)⁻¹) U := by
      intro s hs
      apply ContinuousAt.continuousWithinAt
      have hR : ContinuousAt (Ring.inverse : ℂ → ℂ) (Mm ι u κ x s).det := by
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ (hdetM s hs)
      exact ContinuousAt.comp (f := fun s => Mm ι u κ x s) (x := s) (continuousAt_matrix_inv _ hR)
        hM.continuousAt
    have h1 : ContinuousOn (fun p : ℂ × Q => (Mm ι u κ x p.1)⁻¹) (U ×ˢ Set.univ) :=
      hinv.comp continuous_fst.continuousOn fun p hp => hp.1
    exact h1.mul hN.continuousOn
  · intro s hs q g j
    exact law ι u κ x (hdetM s hs) (hspan s hs) q g j

end TranslationCoordinates
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

namespace LevelInvariance

variable {G : Type*} [Mul G]

private def RightInvariantOn (S : Set G) (f : G → ℂ) : Prop :=
  ∀ g : G, ∀ k ∈ S, f (g * k) = f g

private theorem exists_isOpen_subset_exists_forall_rightInvariantOn (S : ℕ → Set G) (u : ℂ → G → ℂ)
    (hc : ∀ g, Continuous fun s => u s g) (hfix : ∀ s, ∃ n, RightInvariantOn (S n) (u s))
    (U₀ : Set ℂ) (hU₀ : IsOpen U₀) (hne : U₀.Nonempty) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ U₀ ∧ ∃ n, ∀ s ∈ U, RightInvariantOn (S n) (u s) := by
  classical

  set C : ℕ → Set ℂ := fun n => ⋂ g, ⋂ k ∈ S n, {s : ℂ | u s (g * k) = u s g} with hC
  have hmemC : ∀ n s, s ∈ C n ↔ RightInvariantOn (S n) (u s) := by
    intro n s
    simp only [hC, Set.mem_iInter, Set.mem_setOf_eq, RightInvariantOn]
  have hCclosed : ∀ n, IsClosed (C n) := by
    intro n
    refine isClosed_iInter fun g => isClosed_iInter fun k => isClosed_iInter fun _ => ?_
    exact isClosed_eq (hc (g * k)) (hc g)

  have hFclosed : ∀ n, IsClosed (C n ∪ U₀ᶜ) := fun n => (hCclosed n).union hU₀.isClosed_compl
  have hcover : ⋃ n, (C n ∪ U₀ᶜ) = Set.univ := by
    refine Set.eq_univ_iff_forall.2 fun s => Set.mem_iUnion.2 ?_
    by_cases hs : s ∈ U₀
    · obtain ⟨n, hn⟩ := hfix s
      exact ⟨n, Or.inl ((hmemC n s).2 hn)⟩
    · exact ⟨0, Or.inr hs⟩

  obtain ⟨x, hx, hxU₀⟩ :=
    (dense_iUnion_interior_of_closed hFclosed hcover).exists_mem_open hU₀ hne
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  refine ⟨U₀ ∩ interior (C n ∪ U₀ᶜ), hU₀.inter isOpen_interior, ⟨x, hxU₀, hxn⟩,
    Set.inter_subset_left, n, ?_⟩
  intro s hs
  rcases interior_subset hs.2 with hsC | hsU₀
  · exact (hmemC n s).1 hsC
  · exact absurd hs.1 hsU₀

variable (F : Type) [Field F] [NumberField F]

private def congrSet (n : ℕ) : Set (AdelicGL2 (𝓞 F) F) :=
  {u | glArch (𝓞 F) F u = 1 ∧ ∀ i j : Fin 2,
    (glFin (𝓞 F) F u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
      idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) ∧
    (((glFin (𝓞 F) F u)⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
      idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)})}

private theorem idealBound_span_singleton {r : 𝓞 F} (hr : r ≠ 0) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) (Ideal.span {r}) v = v.intValuation r := by
  rw [idealBound_of_ne_bot (by rwa [Ne, Ideal.span_singleton_eq_bot]) v, v.intValuation_if_neg hr]

private theorem idealBall_span_mul_subset {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) :
    idealBall (𝓞 F) F (Ideal.span {a * b}) ⊆ idealBall (𝓞 F) F (Ideal.span {a}) := by
  intro x hx v
  have h := hx v
  rw [idealBound_span_singleton F (mul_ne_zero ha hb)] at h
  rw [idealBound_span_singleton F ha]
  refine h.trans ?_
  rw [map_mul]
  exact mul_le_of_le_one_right' (v.intValuation_le_one b)

private theorem eq_zero_of_forall_mem_idealBall (x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (hx : ∀ m : ℕ, m ≠ 0 → x ∈ idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)})) : x = 0 := by
  refine IsDedekindDomain.FiniteAdeleRing.ext F fun v => ?_
  rw [coe_zero_apply]
  by_contra h0
  have hv0 : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
  set e : ℤ := WithZero.log (Valued.v (x v)) with he_def
  have he : Valued.v (x v) = WithZero.exp e := (WithZero.exp_log hv0).symm
  set M : ℕ := Ideal.absNorm v.asIdeal ^ (e.natAbs + 1) with hM_def
  have hM0 : M ≠ 0 :=
    pow_ne_zero _ (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hmem : ((M : ℕ) : 𝓞 F) ∈ v.asIdeal ^ (e.natAbs + 1) := by
    rw [hM_def, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) _
  have h1 : Valued.v (x v) ≤ v.intValuation ((M : ℕ) : 𝓞 F) := by
    rw [← idealBound_span_singleton F (Nat.cast_ne_zero.mpr hM0) v]
    exact hx M hM0 v
  have h2 : v.intValuation ((M : ℕ) : 𝓞 F) ≤ WithZero.exp (-((e.natAbs + 1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ _).mpr hmem
  have h3 := (he ▸ h1).trans h2
  rw [WithZero.exp_le_exp] at h3
  omega

private theorem exists_idealBall_subset {O : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)} (hO : IsOpen O)
    (h0 : (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ O) :
    ∃ m : ℕ, m ≠ 0 ∧ idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)}) ⊆ O := by
  have hS := isCompact_integralFiniteAdeles (𝓞 F) F
  let t : ℕ → Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := fun k =>
    idealBall (𝓞 F) F (Ideal.span {((k + 1 : ℕ) : 𝓞 F)}) ∩ Oᶜ
  have htc : ∀ k, IsClosed (t k) := fun k =>
    (isClosed_idealBall (𝓞 F) F _).inter hO.isClosed_compl
  have hst : integralFiniteAdeles (𝓞 F) F ∩ ⋂ k, t k = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxI := Set.mem_iInter.mp hx.2
    have hx0 : x = 0 := by
      refine eq_zero_of_forall_mem_idealBall F x fun m hm => ?_
      have h := (hxI (m - 1)).1
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] at h
    exact (hxI 0).2 (hx0 ▸ h0)
  obtain ⟨u, hu⟩ := hS.elim_finite_subfamily_closed t htc hst
  refine ⟨∏ k ∈ u, (k + 1), Finset.prod_ne_zero_iff.mpr fun k _ => Nat.succ_ne_zero k,
    fun x hx => ?_⟩
  by_contra hxO
  have hxall : x ∈ integralFiniteAdeles (𝓞 F) F ∩ ⋂ k ∈ u, t k := by
    refine ⟨idealBall_subset_integralFiniteAdeles _ hx, Set.mem_iInter₂.mpr fun k hk => ⟨?_, hxO⟩⟩
    have hsplit : (∏ i ∈ u, (i + 1) : ℕ) = (k + 1) * ∏ i ∈ u.erase k, (i + 1) :=
      (Finset.mul_prod_erase u (fun i => i + 1) hk).symm
    rw [hsplit, Nat.cast_mul] at hx
    exact idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
      (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.succ_ne_zero i)) hx
  rw [hu] at hxall
  exact hxall

private noncomputable def liftFin (X : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, X i j)

private theorem one_apply_eq (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) := by
  rw [Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem coe_eq_liftFin {u : AdelicGL2 (𝓞 F) F} (hu : glArch (𝓞 F) F u = 1) :
    (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      liftFin F (glFin (𝓞 F) F u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := by
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · show ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
    rw [← glArch_apply, hu, Units.val_one]
  · rfl

private theorem exists_forall_liftFin_mem {W : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))}
    (hW : IsOpen W) (h1 : (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ∈ W) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ X : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      (∀ i j, X i j - (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
        idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)})) → liftFin F X ∈ W := by
  obtain ⟨r, hr, hrW⟩ := isOpen_pi_iff'.mp hW _ h1
  have hc : ∀ i, ∃ c : Fin 2 → Set (AdeleRing (𝓞 F) F),
      (∀ j, IsOpen (c j) ∧ (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j ∈ c j) ∧
        Set.univ.pi c ⊆ r i := fun i => isOpen_pi_iff'.mp (hr i).1 _ (hr i).2
  choose c hc hcr using hc
  have hAB : ∀ i j, ∃ A : Set (InfiniteAdeleRing F), ∃ B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      IsOpen A ∧ IsOpen B ∧ (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j ∈ A ∧
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈ B ∧ A ×ˢ B ⊆ c i j := by
    intro i j
    have h := (hc i j).2
    rw [one_apply_eq] at h
    exact isOpen_prod_iff.mp (hc i j).1 _ _ h
  choose A B hA hB hA1 hB1 hABc using hAB
  let T : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    ⋂ i, ⋂ j, (fun y => (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j + y) ⁻¹' B i j
  have hT : IsOpen T :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hB i j).preimage (continuous_const.add continuous_id)
  have hT0 : (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ T := by
    refine Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun j => ?_
    show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j + 0 ∈ B i j
    rw [add_zero]
    exact hB1 i j
  obtain ⟨m, hm, hmT⟩ := exists_idealBall_subset F hT hT0
  refine ⟨m, hm, fun X hX => hrW (Set.mem_univ_pi.mpr fun i => hcr i (Set.mem_univ_pi.mpr fun j => ?_))⟩
  refine hABc i j (Set.mk_mem_prod (hA1 i j) ?_)
  have h := Set.mem_iInter.mp (Set.mem_iInter.mp (hmT (hX i j)) i) j
  have h' : (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j +
      (X i j - (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) ∈ B i j := h
  rwa [add_sub_cancel] at h'

private theorem exists_congrSet_subset {V : Set (AdelicGL2 (𝓞 F) F)} (hV : IsOpen V)
    (h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ V) : ∃ n : ℕ, congrSet F n ⊆ V := by
  obtain ⟨O, hO, hOV⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hV
  have h1O : Units.embedProduct _ (1 : AdelicGL2 (𝓞 F) F) ∈ O := by
    rw [← Set.mem_preimage, hOV]
    exact h1
  rw [map_one, Prod.one_eq_mk] at h1O
  obtain ⟨O₁, O₂, hO₁, hO₂, h1O₁, h1O₂, hprod⟩ := isOpen_prod_iff.mp hO _ _ h1O
  obtain ⟨m₁, hm₁, hW₁⟩ := exists_forall_liftFin_mem F hO₁ h1O₁
  obtain ⟨m₂, hm₂, hW₂⟩ := exists_forall_liftFin_mem F (hO₂.preimage MulOpposite.continuous_op)
    (by rw [Set.mem_preimage, MulOpposite.op_one]; exact h1O₂)
  refine ⟨m₁ * m₂ - 1, fun u hu => ?_⟩
  have hn : m₁ * m₂ - 1 + 1 = m₁ * m₂ :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hm₁ hm₂))
  obtain ⟨harch, hent⟩ := hu
  simp only [hn, Nat.cast_mul] at hent
  have harch' : glArch (𝓞 F) F u⁻¹ = 1 := by rw [map_inv, harch, inv_one]
  have hval : (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ∈ O₁ := by
    rw [coe_eq_liftFin F harch]
    exact hW₁ _ fun i j => idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr hm₁)
      (Nat.cast_ne_zero.mpr hm₂) (hent i j).1
  have hinv : MulOpposite.op ((u⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2)
      (AdeleRing (𝓞 F) F)) ∈ O₂ := by
    have h := hW₂ _ fun i j => idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr hm₂)
      (Nat.cast_ne_zero.mpr hm₁) (mul_comm (m₁ : 𝓞 F) (m₂ : 𝓞 F) ▸ (hent i j).2)
    rw [Set.mem_preimage, ← map_inv, ← coe_eq_liftFin F harch'] at h
    exact h
  rw [← hOV, Set.mem_preimage, Units.embedProduct_apply]
  exact hprod (Set.mk_mem_prod hval hinv)

private theorem exists_rightInvariantOn_congrSet_of_isKfSmooth (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsKfSmooth F f) : ∃ n : ℕ, RightInvariantOn (congrSet F n) f := by
  have hopen : IsOpen ((MulAction.stabilizer (↥(finiteAdelicGL2Subgroup F))
      (FLT.SmoothVectors.RightTranslationFn.mk f :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (↥(finiteAdelicGL2Subgroup F))) : Set (↥(finiteAdelicGL2Subgroup F))) := hf
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hopen
  have h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ V := by
    have h : (1 : ↥(finiteAdelicGL2Subgroup F)) ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]; exact Subgroup.one_mem _
    exact h
  obtain ⟨n, hn⟩ := exists_congrSet_subset F hV h1
  refine ⟨n, fun g k hk => ?_⟩
  have hkK : k ∈ finiteAdelicGL2Subgroup F := (mem_finiteAdelicGL2Subgroup_iff F k).mpr hk.1
  have hst : (⟨k, hkK⟩ : ↥(finiteAdelicGL2Subgroup F)) ∈
      ((MulAction.stabilizer (↥(finiteAdelicGL2Subgroup F))
        (FLT.SmoothVectors.RightTranslationFn.mk f :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
          Subgroup (↥(finiteAdelicGL2Subgroup F))) : Set (↥(finiteAdelicGL2Subgroup F))) := by
    rw [← hVeq]; exact hn hk
  have heq := MulAction.mem_stabilizer_iff.mp (SetLike.mem_coe.mp hst)
  exact congrArg (fun φ => FLT.SmoothVectors.RightTranslationFn.toFun φ g) heq

private noncomputable def finIncl (x : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) : AdelicGL2 (𝓞 F) F where
  val := Matrix.of fun i j =>
    ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
      (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j)
  inv := Matrix.of fun i j =>
    ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
      ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j)
  val_inv := by
    apply (adelicMatrixProdEquiv F).injective
    rw [map_mul, map_one]
    have h1 : adelicMatrixProdEquiv F (Matrix.of fun i j =>
        ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j))
        = (1, (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      Prod.ext (by ext i j; rfl) (by ext i j; rfl)
    have h2 : adelicMatrixProdEquiv F (Matrix.of fun i j =>
        ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j))
        = (1, ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      Prod.ext (by ext i j; rfl) (by ext i j; rfl)
    rw [h1, h2]
    exact Prod.ext (one_mul _) (Units.mul_inv x)
  inv_val := by
    apply (adelicMatrixProdEquiv F).injective
    rw [map_mul, map_one]
    have h1 : adelicMatrixProdEquiv F (Matrix.of fun i j =>
        ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j))
        = (1, (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      Prod.ext (by ext i j; rfl) (by ext i j; rfl)
    have h2 : adelicMatrixProdEquiv F (Matrix.of fun i j =>
        ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j))
        = (1, ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      Prod.ext (by ext i j; rfl) (by ext i j; rfl)
    rw [h1, h2]
    exact Prod.ext (one_mul _) (Units.inv_mul x)

private theorem continuous_finIncl : Continuous (finIncl F) :=
  Units.continuous_iff.mpr
    ⟨continuous_matrix fun i j => continuous_const.prodMk (Units.continuous_val.matrix_elem i j),
      continuous_matrix fun i j => continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)⟩

private theorem glArch_finIncl (x : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (finIncl F x) = 1 := by
  ext i j
  rfl

private theorem glFin_finIncl (x : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (finIncl F x) = x := by
  ext i j
  rfl

private theorem eq_finIncl_glFin (k : AdelicGL2 (𝓞 F) F) (hk : glArch (𝓞 F) F k = 1) :
    k = finIncl F (glFin (𝓞 F) F k) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ rfl)
  exact congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
    (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) hk

private def entryBall (n : ℕ) : Set (AdelicGL2 (𝓞 F) F) :=
  ⋂ i : Fin 2, ⋂ j : Fin 2,
    ((fun u : AdelicGL2 (𝓞 F) F =>
        (glFin (𝓞 F) F u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) ⁻¹'
        idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)})) ∩
    ((fun u : AdelicGL2 (𝓞 F) F =>
        (((glFin (𝓞 F) F u)⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) ⁻¹'
        idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}))

private theorem isOpen_entryBall (n : ℕ) : IsOpen (entryBall F n) := by
  have hN : (Ideal.span {((n + 1 : ℕ) : 𝓞 F)} : Ideal (𝓞 F)) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact (isOpen_idealBall (𝓞 F) F hN).preimage
      (((Units.continuous_val.comp (continuous_glFin (𝓞 F) F)).matrix_elem i j).sub continuous_const)
  · exact (isOpen_idealBall (𝓞 F) F hN).preimage
      (((Units.continuous_coe_inv.comp (continuous_glFin (𝓞 F) F)).matrix_elem i j).sub continuous_const)

private theorem one_mem_entryBall (n : ℕ) : (1 : AdelicGL2 (𝓞 F) F) ∈ entryBall F n := by
  refine Set.mem_iInter₂.mpr fun i j => ⟨?_, ?_⟩
  · rw [Set.mem_preimage, map_one, Units.val_one, sub_self]
    exact zero_mem_idealBall _
  · rw [Set.mem_preimage, map_one, inv_one, Units.val_one, sub_self]
    exact zero_mem_idealBall _

private theorem mem_congrSet_of_mem_entryBall {n : ℕ} {u : AdelicGL2 (𝓞 F) F}
    (harch : glArch (𝓞 F) F u = 1) (hu : u ∈ entryBall F n) : u ∈ congrSet F n :=
  ⟨harch, fun i j => Set.mem_iInter₂.mp hu i j⟩

private theorem exists_finset_eq_mul_mem_closure_congrSet (n : ℕ) :
    ∃ T : Finset (AdelicGL2 (𝓞 F) F),
      (∀ g ∈ T, glArch (𝓞 F) F g = 1 ∧ glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        ∃ g ∈ T, ∃ h ∈ Subgroup.closure (congrSet F n), k = g * h := by

  have hC : IsCompact (finIncl F '' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))) :=
    (isCompact_finiteLevelZero (𝓞 F) F ⊤).image (continuous_finIncl F)

  have hU : ∀ g ∈ finIncl F '' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))),
      (fun k : AdelicGL2 (𝓞 F) F => g⁻¹ * k) ⁻¹' entryBall F n ∈ nhds g := by
    intro g _
    refine IsOpen.mem_nhds ((isOpen_entryBall F n).preimage (continuous_const.mul continuous_id)) ?_
    show g⁻¹ * g ∈ entryBall F n
    rw [inv_mul_cancel]
    exact one_mem_entryBall F n
  obtain ⟨T, hTC, hsub⟩ := hC.elim_nhds_subcover (fun g => (fun k : AdelicGL2 (𝓞 F) F => g⁻¹ * k) ⁻¹' entryBall F n) hU
  have hT : ∀ g ∈ T, glArch (𝓞 F) F g = 1 ∧ glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hTC g hg
    exact ⟨glArch_finIncl F x, by rw [glFin_finIncl]; exact hx⟩
  refine ⟨T, hT, fun k harch hint => ?_⟩
  have hkC : k ∈ finIncl F '' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
    ⟨glFin (𝓞 F) F k, hint, (eq_finIncl_glFin F k harch).symm⟩
  obtain ⟨g, hgT, hkg⟩ := Set.mem_iUnion₂.mp (hsub hkC)
  refine ⟨g, hgT, g⁻¹ * k, Subgroup.subset_closure (mem_congrSet_of_mem_entryBall F ?_ hkg),
    (mul_inv_cancel_left g k).symm⟩
  rw [map_mul, map_inv, (hT g hgT).1, harch, inv_one, one_mul]

private theorem forall_mem_closure_congrSet_apply_mul_eq (n : ℕ) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : RightInvariantOn (congrSet F n) f) :
    ∀ g : AdelicGL2 (𝓞 F) F, ∀ h ∈ Subgroup.closure (congrSet F n), f (g * h) = f g := by
  intro g h hh
  induction hh using Subgroup.closure_induction generalizing g with
  | mem x hx => exact hf g x hx
  | one => rw [mul_one]
  | mul x y _ _ ihx ihy => rw [← mul_assoc, ihy, ihx]
  | inv x _ ihx =>
    have h := ihx (g * x⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

end LevelInvariance
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

open ArchimedeanIsometryGroup in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : ∀ s, IsArchKFinite F (φ s))
    (_hφf : ∀ s, IsKfSmooth F (φ s))
    (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧
      ∃ (n : ℕ) (σ : Fin n → ℂ), ∀ s ∈ U, ∃ c : Fin n → ℂ, ∀ k : AdelicGL2 (𝓞 F) F,
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s k = ∑ i, c i * φ (σ i) k := by
  classical

  obtain ⟨U₁, hU₁, hne₁, -, n, hinv₁⟩ :=
    LevelInvariance.exists_isOpen_subset_exists_forall_rightInvariantOn (LevelInvariance.congrSet F) φ
      (fun g => _hφjc.comp (continuous_id.prodMk continuous_const))
      (fun s => LevelInvariance.exists_rightInvariantOn_congrSet_of_isKfSmooth F (φ s) (_hφf s))
      Set.univ isOpen_univ Set.univ_nonempty

  obtain ⟨T, hT₁, hT₂⟩ := LevelInvariance.exists_finset_eq_mul_mem_closure_congrSet F n

  obtain ⟨U₂, hU₂, hne₂, hU₂₁, r, κ₀, x, hκ₀, hdet₀, hspan₀⟩ :=
    UniformRank.exists_isOpen_subset_forall_det_ne_zero_and_mem_span (Set.range (incl F)) φ
      (fun s => translatesFinite_range_incl F (φ s) (_hφK s))
      (fun g => _hφjc.comp (continuous_id.prodMk continuous_const)) U₁ hU₁ hne₁

  have hκ₀' : ∀ j, ∃ q : Kinf F, incl F q = κ₀ j := fun j => Set.mem_range.1 (hκ₀ j)
  choose κ hκ using hκ₀'
  have hdet : ∀ s ∈ U₂, (Matrix.of fun i j => φ s (x i * incl F (κ j))).det ≠ 0 := by
    intro s hs
    simpa only [hκ] using hdet₀ s hs
  have hspan : ∀ s ∈ U₂, ∀ q : Kinf F, (fun g => φ s (g * incl F q)) ∈
      Submodule.span ℂ (Set.range fun j => fun g => φ s (g * incl F (κ j))) := by
    intro s hs q
    simpa only [hκ] using hspan₀ s hs (incl F q) ⟨q, rfl⟩

  obtain ⟨ρ, hρ₁, hρ₂, hρ₃, hlaw⟩ :=
    TranslationCoordinates.exists_forall_one_and_mul_and_continuousOn_and_eq_sum (incl F) (continuous_incl F) φ
      _hφjc U₂ r κ x hdet hspan

  obtain ⟨s₀, hs₀⟩ := hne₂
  obtain ⟨U₃, hU₃, hs₀₃, hU₃₂, hT⟩ :=
    AveragedIntertwiner.exists_isOpen_forall_exists_isUnit_mul_eq_mul (haarProb F) r U₂ hU₂ ρ hρ₁ hρ₂ hρ₃ s₀ hs₀

  have hcomm : ∀ (q : Kinf F), ∀ c ∈ T, incl F q * c = c * incl F q :=
    fun q c hc => incl_mul_comm_of_glArch_eq_one F q c (hT₁ c hc).1
  have hV := SliceCoefficients.slices_mem_pi_coeffSpan (incl F) T hcomm φ κ ρ (ρ s₀) U₂ U₃ hU₃₂ hspan hlaw hT

  have hinv : ∀ s ∈ U₃, ∀ (g : AdelicGL2 (𝓞 F) F),
      ∀ h ∈ ((Subgroup.closure (LevelInvariance.congrSet F n) : Subgroup (AdelicGL2 (𝓞 F) F)) :
        Set (AdelicGL2 (𝓞 F) F)), φ s (g * h) = φ s g :=
    fun s hs g h hh =>
      LevelInvariance.forall_mem_closure_congrSet_apply_mul_eq F n (φ s) (hinv₁ s (hU₂₁ (hU₃₂ hs))) g h hh
  have hcover : ∀ k ∈ {k : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))},
      ∃ q : Kinf F, ∃ c ∈ T, ∃ h ∈ ((Subgroup.closure (LevelInvariance.congrSet F n) :
        Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)), k = incl F q * c * h :=
    fun k hk => exists_exists_mem_exists_mem_eq_incl_mul_mul F T _ hT₂ k hk.1 hk.2
  haveI : FiniteDimensional ℂ (CoefficientSpan.coeffSpan (ρ s₀)) := CoefficientSpan.finiteDimensional_coeffSpan (ρ s₀)
  haveI : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : T => CoefficientSpan.coeffSpan (ρ s₀)) :=
    SliceSpan.finiteDimensional_pi_const _
  obtain ⟨m, σ, -, hσ⟩ :=
    SliceSpan.exists_forall_mem_exists_forall_eq_sum (⇑(incl F)) T _ _ hcover φ U₃ hinv
      (Submodule.pi Set.univ fun _ : T => CoefficientSpan.coeffSpan (ρ s₀)) hV
  exact ⟨U₃, hU₃, ⟨s₀, hs₀₃⟩, m, σ, fun s hs => (hσ s hs).imp fun a ha k hk₁ hk₂ => ha k ⟨hk₁, hk₂⟩⟩

#print axioms solution

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.ArchimedeanIsometryGroup"

end S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous (solution)
