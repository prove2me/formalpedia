-- Prove2me | solution 1 for AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fb846da7-5cea-536b-8561-4beee2ce075a

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite
import Theorems.Thm_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open FLT.SmoothVectors Topology

noncomputable section

namespace KCLProof

variable (F : Type) [Field F] [NumberField F]

theorem ext_glArch_glFin {g g' : AdelicGL2 (𝓞 F) F}
    (h1 : glArch (𝓞 F) F g = glArch (𝓞 F) F g') (h2 : glFin (𝓞 F) F g = glFin (𝓞 F) F g') : g = g' := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h1
  · exact congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h2

theorem ext_archComponent {a b : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ u : InfinitePlace F, archComponent F u a = archComponent F u b) : a = b := by
  refine Units.ext (Matrix.ext fun i j => funext fun u => ?_)
  exact congrArg (fun m : GL (Fin 2) u.Completion => (m : Matrix (Fin 2) (Fin 2) u.Completion) i j) (h u)

theorem commute_of_glArch_glFin {x y : AdelicGL2 (𝓞 F) F}
    (ha : Commute (glArch (𝓞 F) F x) (glArch (𝓞 F) F y))
    (hf : Commute (glFin (𝓞 F) F x) (glFin (𝓞 F) F y)) : Commute x y := by
  show x * y = y * x
  apply ext_glArch_glFin F
  · rw [map_mul, map_mul]; exact ha
  · rw [map_mul, map_mul]; exact hf

abbrev Kw (w : InfinitePlace F) : Subgroup (AdelicGL2 (𝓞 F) F) := archRowIsometrySubgroup F w

abbrev Kf : Subgroup (AdelicGL2 (𝓞 F) F) := maximalCompactAway F ∅

theorem glFin_adelicArchGLInclAt (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w k) = 1 :=
  glFin_adelicArchGLIncl F _

theorem glArch_adelicArchGLInclAt (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    glArch (𝓞 F) F (adelicArchGLInclAt F w k) = archGLIncl F w k :=
  glArch_adelicArchGLIncl F _

theorem archComponent_glArch_adelicArchGLInclAt_self (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w k)) = k := by
  rw [glArch_adelicArchGLInclAt, archComponent_archGLIncl_self]

theorem archComponent_glArch_adelicArchGLInclAt_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (k : GL (Fin 2) w.Completion) :
    archComponent F v (glArch (𝓞 F) F (adelicArchGLInclAt F w k)) = 1 := by
  rw [glArch_adelicArchGLInclAt, archComponent_archGLIncl_of_ne _ hvw]

theorem mem_Kw_iff {w : InfinitePlace F} {x : AdelicGL2 (𝓞 F) F} :
    x ∈ Kw F w ↔ ∃ k : GL (Fin 2) w.Completion, IsRowIsometry k ∧ adelicArchGLInclAt F w k = x := by
  simp only [Kw, archRowIsometrySubgroup, Subgroup.mem_map, mem_rowIsometrySubgroup_iff]

theorem mem_Kf_iff {x : AdelicGL2 (𝓞 F) F} :
    x ∈ Kf F ↔ (glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F ∧
      ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F x))) ∧ glArch (𝓞 F) F x = 1 := by
  rw [Kf, mem_maximalCompactAway_iff, mem_adelicMaximalCompact_iff]
  simp

theorem commute_Kw_Kw {v w : InfinitePlace F} (hvw : v ≠ w) {x y : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ Kw F v) (hy : y ∈ Kw F w) : Commute x y := by
  obtain ⟨kx, _, rfl⟩ := (mem_Kw_iff F).1 hx
  obtain ⟨ky, _, rfl⟩ := (mem_Kw_iff F).1 hy
  apply commute_of_glArch_glFin F
  · show glArch (𝓞 F) F _ * glArch (𝓞 F) F _ = glArch (𝓞 F) F _ * glArch (𝓞 F) F _
    apply ext_archComponent F
    intro u
    rw [map_mul, map_mul]
    by_cases huv : u = v
    · subst huv
      rw [archComponent_glArch_adelicArchGLInclAt_of_ne F hvw, mul_one, one_mul]
    · rw [archComponent_glArch_adelicArchGLInclAt_of_ne F huv, one_mul, mul_one]
  · show glFin (𝓞 F) F _ * glFin (𝓞 F) F _ = glFin (𝓞 F) F _ * glFin (𝓞 F) F _
    rw [glFin_adelicArchGLInclAt, glFin_adelicArchGLInclAt]

theorem commute_Kw_Kf {w : InfinitePlace F} {x y : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ Kw F w) (hy : y ∈ Kf F) : Commute x y := by
  obtain ⟨kx, _, rfl⟩ := (mem_Kw_iff F).1 hx
  have hy' := ((mem_Kf_iff F).1 hy).2
  apply commute_of_glArch_glFin F
  · show glArch (𝓞 F) F _ * glArch (𝓞 F) F _ = glArch (𝓞 F) F _ * glArch (𝓞 F) F _
    rw [hy', mul_one, one_mul]
  · show glFin (𝓞 F) F _ * glFin (𝓞 F) F _ = glFin (𝓞 F) F _ * glFin (𝓞 F) F _
    rw [glFin_adelicArchGLInclAt, mul_one, one_mul]

theorem list_prod_ofFn_eq_single {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (f : Fin n → M) (i₀ : Fin n), (∀ i, i ≠ i₀ → f i = 1) → (List.ofFn f).prod = f i₀ := by
  intro n
  induction n with
  | zero => intro f i₀; exact i₀.elim0
  | succ n ih =>
    intro f i₀ h
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i₀ with h0 | ⟨j₀, hj₀⟩
    · subst h0
      have hrest : (List.ofFn fun i : Fin n => f i.succ).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero i)
      rw [hrest, mul_one]
    · subst hj₀
      rw [h 0 (Fin.succ_ne_zero j₀).symm, one_mul]
      exact ih (fun i => f i.succ) j₀ (fun i hi => h _ (fun he => hi (Fin.succ_injective _ he)))

theorem list_prod_ofFn_eq_one {M : Type*} [Monoid M] {n : ℕ} (f : Fin n → M) (h : ∀ i, f i = 1) :
    (List.ofFn f).prod = 1 := by
  apply List.prod_eq_one
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact h i

end KCLProof

namespace KCLProof

variable (F : Type) [Field F] [NumberField F]

def IsK (k : AdelicGL2 (𝓞 F) F) : Prop :=
  glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
    ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))

def archPiece (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  adelicArchGLInclAt F w (archComponent F w (glArch (𝓞 F) F k))

def finPiece (k : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F (glArch (𝓞 F) F k))⁻¹ * k

theorem archPiece_mem {k : AdelicGL2 (𝓞 F) F} (hk : IsK F k) (w : InfinitePlace F) :
    archPiece F w k ∈ Kw F w :=
  (mem_Kw_iff F).2 ⟨_, hk.2 w, rfl⟩

theorem glArch_finPiece (k : AdelicGL2 (𝓞 F) F) : glArch (𝓞 F) F (finPiece F k) = 1 := by
  rw [finPiece, map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

theorem glFin_finPiece (k : AdelicGL2 (𝓞 F) F) : glFin (𝓞 F) F (finPiece F k) = glFin (𝓞 F) F k := by
  rw [finPiece, map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]

theorem finPiece_mem {k : AdelicGL2 (𝓞 F) F} (hk : IsK F k) : finPiece F k ∈ Kf F := by
  rw [mem_Kf_iff]
  refine ⟨⟨?_, fun w => ?_⟩, glArch_finPiece F k⟩
  · rw [glFin_finPiece]; exact hk.1
  · rw [glArch_finPiece, map_one]; exact isRowIsometry_one

theorem finPiece_mem_finiteAdelicGL2Subgroup (k : AdelicGL2 (𝓞 F) F) :
    finPiece F k ∈ finiteAdelicGL2Subgroup F :=
  (mem_finiteAdelicGL2Subgroup_iff F _).2 (glArch_finPiece F k)

def idx : Fin (Fintype.card (Option (InfinitePlace F))) ≃ Option (InfinitePlace F) :=
  (Fintype.equivFin (Option (InfinitePlace F))).symm

def Ksub (i : Fin (Fintype.card (Option (InfinitePlace F)))) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  match idx F i with
  | none => Kf F
  | some w => Kw F w

def piece (k : AdelicGL2 (𝓞 F) F) (i : Fin (Fintype.card (Option (InfinitePlace F)))) : AdelicGL2 (𝓞 F) F :=
  match idx F i with
  | none => finPiece F k
  | some w => archPiece F w k

theorem piece_mem {k : AdelicGL2 (𝓞 F) F} (hk : IsK F k) (i : Fin (Fintype.card (Option (InfinitePlace F)))) :
    piece F k i ∈ Ksub F i := by
  unfold piece Ksub
  cases h : idx F i with
  | none => exact finPiece_mem F hk
  | some w => exact archPiece_mem F hk w

theorem Ksub_comm (i j : Fin (Fintype.card (Option (InfinitePlace F)))) (hij : i ≠ j)
    (x : AdelicGL2 (𝓞 F) F) (hx : x ∈ Ksub F i) (y : AdelicGL2 (𝓞 F) F) (hy : y ∈ Ksub F j) : Commute x y := by
  have hne : idx F i ≠ idx F j := fun h => hij ((idx F).injective h)
  unfold Ksub at hx hy
  cases hi : idx F i with
  | none =>
    cases hj : idx F j with
    | none => exact absurd (hi.trans hj.symm) hne
    | some w =>
      rw [hi] at hx; rw [hj] at hy
      exact (commute_Kw_Kf F hy hx).symm
  | some v =>
    cases hj : idx F j with
    | none =>
      rw [hi] at hx; rw [hj] at hy
      exact commute_Kw_Kf F hx hy
    | some w =>
      rw [hi] at hx; rw [hj] at hy
      have hvw : v ≠ w := fun h => hne (by rw [hi, hj, h])
      exact commute_Kw_Kw F hvw hx hy

theorem eq_listProd_piece {k : AdelicGL2 (𝓞 F) F} (hk : IsK F k) :
    k = (List.ofFn (piece F k)).prod := by
  apply ext_glArch_glFin F
  · rw [map_list_prod, List.map_ofFn]
    apply ext_archComponent F
    intro u
    rw [map_list_prod, List.map_ofFn]

    rw [list_prod_ofFn_eq_single _ ((idx F).symm (some u))]
    · show archComponent F u (glArch (𝓞 F) F k) = archComponent F u (glArch (𝓞 F) F (piece F k ((idx F).symm (some u))))
      unfold piece
      rw [Equiv.apply_symm_apply]
      simp only [archPiece]
      rw [archComponent_glArch_adelicArchGLInclAt_self]
    · intro i hi
      show archComponent F u (glArch (𝓞 F) F (piece F k i)) = 1
      unfold piece
      cases h : idx F i with
      | none => simp only [glArch_finPiece, map_one]
      | some w =>
        simp only [archPiece]
        have huw : u ≠ w := by
          intro huw; subst huw; exact hi ((idx F).eq_symm_apply.mpr h)
        rw [archComponent_glArch_adelicArchGLInclAt_of_ne F huw]
  · rw [map_list_prod, List.map_ofFn]
    rw [list_prod_ofFn_eq_single _ ((idx F).symm none)]
    · show glFin (𝓞 F) F k = glFin (𝓞 F) F (piece F k ((idx F).symm none))
      unfold piece
      rw [Equiv.apply_symm_apply]
      simp only [glFin_finPiece]
    · intro i hi
      show glFin (𝓞 F) F (piece F k i) = 1
      unfold piece
      cases h : idx F i with
      | none => exact absurd ((idx F).eq_symm_apply.mpr h) hi
      | some w => simp only [archPiece, glFin_adelicArchGLInclAt]

theorem isK_of_mem_Ksub {i : Fin (Fintype.card (Option (InfinitePlace F)))} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ Ksub F i) : IsK F x := by
  unfold Ksub at hx
  cases h : idx F i with
  | none => rw [h] at hx; exact ((mem_Kf_iff F).1 hx).1
  | some w =>
    rw [h] at hx
    obtain ⟨kx, hkx, rfl⟩ := (mem_Kw_iff F).1 hx
    refine ⟨?_, fun u => ?_⟩
    · rw [glFin_adelicArchGLInclAt]; exact (finiteIntegralGL2 (𝓞 F) F).one_mem
    · by_cases huw : u = w
      · subst huw; rw [archComponent_glArch_adelicArchGLInclAt_self]; exact hkx
      · rw [archComponent_glArch_adelicArchGLInclAt_of_ne F huw]; exact isRowIsometry_one

theorem isK_mul {k k' : AdelicGL2 (𝓞 F) F} (hk : IsK F k) (hk' : IsK F k') : IsK F (k * k') := by
  refine ⟨?_, fun w => ?_⟩
  · rw [map_mul]; exact (finiteIntegralGL2 (𝓞 F) F).mul_mem hk.1 hk'.1
  · rw [map_mul, map_mul]; exact (hk.2 w).mul (hk'.2 w)

theorem isK_inv {k : AdelicGL2 (𝓞 F) F} (hk : IsK F k) : IsK F k⁻¹ := by
  refine ⟨?_, fun w => ?_⟩
  · rw [map_inv]; exact (finiteIntegralGL2 (𝓞 F) F).inv_mem hk.1
  · rw [map_inv, map_inv]; exact (hk.2 w).inv

theorem isK_of_mem_iSup {x : AdelicGL2 (𝓞 F) F} (hx : x ∈ ⨆ j, Ksub F j) : IsK F x := by
  refine Subgroup.iSup_induction (Ksub F) (C := fun x => IsK F x) hx (fun i x hx => isK_of_mem_Ksub F hx) ?_ ?_
  · refine ⟨?_, fun w => ?_⟩
    · rw [map_one]; exact (finiteIntegralGL2 (𝓞 F) F).one_mem
    · rw [map_one, map_one]; exact isRowIsometry_one
  · intro x y hx hy; exact isK_mul F hx hy

end KCLProof

namespace KCLProof

variable (F : Type) [Field F] [NumberField F]

def Rt (k : AdelicGL2 (𝓞 F) F) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun f := fun x => f (x * k)
  map_add' f g := rfl
  map_smul' c f := rfl

@[scoped simp] theorem Rt_apply (k : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    Rt F k f x = f (x * k) := rfl

theorem conj_mem_Kw {w : InfinitePlace F} {k₀ x : AdelicGL2 (𝓞 F) F} (hk₀ : IsK F k₀) (hx : x ∈ Kw F w) :
    k₀⁻¹ * x * k₀ ∈ Kw F w := by
  obtain ⟨κ, hκ, rfl⟩ := (mem_Kw_iff F).1 hx
  set κ₀ : GL (Fin 2) w.Completion := archComponent F w (glArch (𝓞 F) F k₀)
  refine (mem_Kw_iff F).2 ⟨κ₀⁻¹ * κ * κ₀, (((hk₀.2 w).inv).mul hκ).mul (hk₀.2 w), ?_⟩
  apply ext_glArch_glFin F
  · apply ext_archComponent F
    intro u
    simp only [map_mul, map_inv]
    by_cases huw : u = w
    · subst huw
      simp only [archComponent_glArch_adelicArchGLInclAt_self, κ₀]
    · simp only [archComponent_glArch_adelicArchGLInclAt_of_ne F huw, mul_one, inv_mul_cancel, inv_one]
  · simp only [map_mul, map_inv, glFin_adelicArchGLInclAt, mul_one, inv_mul_cancel, inv_one]

theorem isArchKFiniteAt_translate {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchKFiniteAt F w φ) {k₀ : AdelicGL2 (𝓞 F) F} (hk₀ : IsK F k₀) :
    IsArchKFiniteAt F w (fun x => φ (x * k₀)) := by
  classical
  obtain ⟨s, hs⟩ := hφ
  refine ⟨s.image (Rt F k₀), ?_⟩
  intro k hk
  have hk' : k₀⁻¹ * k * k₀ ∈ Kw F w := conj_mem_Kw F hk₀ hk
  have hmem := hs _ hk'

  have heq : (fun x => (fun y => φ (y * k₀)) (x * k)) = Rt F k₀ (fun y => φ (y * (k₀⁻¹ * k * k₀))) := by
    funext x
    simp only [Rt_apply]
    congr 1
    group
  rw [heq, Finset.coe_image]
  exact Submodule.apply_mem_span_image_of_mem_span (Rt F k₀) hmem

theorem isArchKFinite_translate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchKFinite F φ)
    {k₀ : AdelicGL2 (𝓞 F) F} (hk₀ : IsK F k₀) : IsArchKFinite F (fun x => φ (x * k₀)) :=
  fun w => isArchKFiniteAt_translate F (hφ w) hk₀

theorem isArchKFiniteAt_add {w : InfinitePlace F} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchKFiniteAt F w φ) (hψ : IsArchKFiniteAt F w ψ) : IsArchKFiniteAt F w (φ + ψ) := by
  classical
  obtain ⟨s, hs⟩ := hφ
  obtain ⟨t, ht⟩ := hψ
  refine ⟨s ∪ t, fun k hk => ?_⟩
  have : (fun x => (φ + ψ) (x * k)) = (fun x => φ (x * k)) + fun x => ψ (x * k) := rfl
  rw [this, Finset.coe_union]
  exact Submodule.add_mem _ (Submodule.span_mono Set.subset_union_left (hs k hk))
    (Submodule.span_mono Set.subset_union_right (ht k hk))

theorem isArchKFiniteAt_smul {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchKFiniteAt F w φ) (c : ℂ) : IsArchKFiniteAt F w (c • φ) := by
  obtain ⟨s, hs⟩ := hφ
  refine ⟨s, fun k hk => ?_⟩
  have : (fun x => (c • φ) (x * k)) = c • fun x => φ (x * k) := rfl
  rw [this]
  exact Submodule.smul_mem _ c (hs k hk)

theorem isArchKFinite_zero' : IsArchKFinite F (0 : AdelicGL2 (𝓞 F) F → ℂ) := isArchKFinite_zero F

theorem isKfSmooth_translate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ)
    {k₀ : AdelicGL2 (𝓞 F) F} (_hk₀ : IsK F k₀) : IsKfSmooth F (fun x => φ (x * k₀)) := by

  set kinf : AdelicGL2 (𝓞 F) F := adelicArchGLIncl F (glArch (𝓞 F) F k₀) with hkinf
  have hsplit : k₀ = kinf * finPiece F k₀ := by simp only [finPiece, hkinf, mul_inv_cancel_left]
  have hkf : finPiece F k₀ ∈ finiteAdelicGL2Subgroup F := finPiece_mem_finiteAdelicGL2Subgroup F k₀

  have h1 : IsKfSmooth F (fun x => φ (x * finPiece F k₀)) := by
    have := IsSmoothVector.smul (G := ↥(finiteAdelicGL2Subgroup F)) hφ ⟨finPiece F k₀, hkf⟩
    exact this

  rw [isKfSmooth_iff] at h1 ⊢
  refine Subgroup.isOpen_mono ?_ h1
  intro h hh
  rw [MulAction.mem_stabilizer_iff] at hh ⊢
  have hcomm : (h : AdelicGL2 (𝓞 F) F) * kinf = kinf * h := by
    apply ext_glArch_glFin F
    · rw [map_mul, map_mul, (mem_finiteAdelicGL2Subgroup_iff F _).1 h.2, one_mul, mul_one]
    · rw [map_mul, map_mul, hkinf, glFin_adelicArchGLIncl, one_mul, mul_one]
  apply RightTranslationFn.ext
  intro x
  have hhx := congrArg (fun f => RightTranslationFn.toFun f (x * kinf)) hh
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul] at hhx ⊢
  change φ (x * kinf * ↑h * finPiece F k₀) = φ (x * kinf * finPiece F k₀) at hhx
  change φ (x * ↑h * k₀) = φ (x * k₀)
  rw [hsplit, ← mul_assoc, ← mul_assoc, mul_assoc x, hcomm, ← mul_assoc]
  exact hhx

end KCLProof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth.KCLProof"

namespace KCLProof

variable (F : Type) [Field F] [NumberField F]

theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) :=
  IsSmoothVector.add hφ hψ

theorem isKfSmooth_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (c : ℂ) :
    IsKfSmooth F (c • φ) := by
  rw [isKfSmooth_iff] at hφ ⊢
  refine Subgroup.isOpen_mono ?_ hφ
  intro h hh
  rw [MulAction.mem_stabilizer_iff] at hh ⊢
  apply RightTranslationFn.ext
  intro x
  have hhx := congrArg (fun f => RightTranslationFn.toFun f x) hh
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul] at hhx ⊢
  change φ (x * ↑h) = φ x at hhx
  change c • φ (x * ↑h) = c • φ x
  rw [hhx]

def Tset (φ : AdelicGL2 (𝓞 F) F → ℂ) : Set (AdelicGL2 (𝓞 F) F → ℂ) :=
  {ψ | ∃ k, IsK F k ∧ ψ = fun x => φ (x * k)}

theorem translate_mem_Tset (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : IsK F k) :
    (fun x => φ (x * k)) ∈ Tset F φ := ⟨k, hk, rfl⟩

theorem isArchKFinite_and_isKfSmooth_of_mem_span {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Tset F φ)) : IsArchKFinite F f ∧ IsKfSmooth F f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨isArchKFinite_translate F hφK hk, isKfSmooth_translate F hφf hk⟩
  | zero => exact ⟨isArchKFinite_zero F, isKfSmooth_zero F⟩
  | add x y _ _ hx hy => exact ⟨fun w => isArchKFiniteAt_add F (hx.1 w) (hy.1 w), isKfSmooth_add F hx.2 hy.2⟩
  | smul c x _ hx => exact ⟨fun w => isArchKFiniteAt_smul F (hx.1 w) c, isKfSmooth_smul F hx.2 c⟩

theorem continuous_of_mem_span {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ Submodule.span ℂ (Tset F φ)) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, _, rfl⟩ := hx
    exact hφc.comp (continuous_mul_const k)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.const_smul c

theorem rightTranslatesSpanFinite_Kf {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφf : IsKfSmooth F φ) :
    ∃ s : Finset (AdelicGL2 (𝓞 F) F → ℂ), ∀ k ∈ Kf F,
      (fun x => φ (x * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL2 (𝓞 F) F → ℂ)) := by
  classical

  set C : Set ↥(finiteAdelicGL2Subgroup F) := Subtype.val ⁻¹' (Kf F : Set (AdelicGL2 (𝓞 F) F)) with hC
  have hCc : IsCompact C := by
    have hemb : Topology.IsClosedEmbedding (Subtype.val : ↥(finiteAdelicGL2Subgroup F) → AdelicGL2 (𝓞 F) F) :=
      (isClosed_finiteAdelicGL2Subgroup F).isClosedEmbedding_subtypeVal
    exact hemb.isCompact_preimage (isCompact_maximalCompactAway F ∅)
  have hfin := AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact hφf hCc
  refine ⟨(hfin.toFinset.image RightTranslationFn.toFun), ?_⟩
  intro k hk
  have hkfa : k ∈ finiteAdelicGL2Subgroup F := (mem_finiteAdelicGL2Subgroup_iff F _).2 ((mem_Kf_iff F).1 hk).2
  apply Submodule.subset_span
  rw [Finset.coe_image, Set.mem_image]
  refine ⟨(⟨k, hkfa⟩ : ↥(finiteAdelicGL2Subgroup F)) • (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ), ?_, rfl⟩
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  exact ⟨⟨k, hkfa⟩, hk, rfl⟩

end KCLProof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth.KCLProof"

namespace KCLProof

variable (F : Type) [Field F] [NumberField F]

theorem main (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ) (hφc : Continuous φ) :
    ∃ (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 F) F → ℂ) (a : Fin m → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ j, (∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → AdelicGL2 (𝓞 F) F),
          (∀ i, glFin (𝓞 F) F (k i) ∈ finiteIntegralGL2 (𝓞 F) F ∧
            ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (k i)))) ∧
          e j = fun x => ∑ i, c i * φ (x * k i)) ∧
        IsArchKFinite F (e j) ∧ IsKfSmooth F (e j)) ∧
      (∀ j, ContinuousOn (a j) {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        ∀ x : AdelicGL2 (𝓞 F) F, φ (x * k) = ∑ j, a j k * e j x := by
  classical

  have hf : ∀ i, ∃ s : Finset (AdelicGL2 (𝓞 F) F → ℂ), ∀ k ∈ Ksub F i,
      (fun x => φ (x * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL2 (𝓞 F) F → ℂ)) := by
    intro i
    unfold Ksub
    cases idx F i with
    | none => exact rightTranslatesSpanFinite_Kf F hφf
    | some w => exact hφK w
  obtain ⟨N, aa, bb, _haa, _haa', hbb, hsum⟩ :=
    AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite (Ksub F) (Ksub_comm F) φ hf

  set W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range bb) with hW
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range bb)
  have hWT : W ≤ Submodule.span ℂ (Tset F φ) := by
    rw [hW]
    apply Submodule.span_le.mpr
    rintro _ ⟨mm, rfl⟩
    refine Submodule.span_mono ?_ (hbb mm)
    rintro ψ ⟨h, hh, rfl⟩
    exact ⟨h, isK_of_mem_iSup F hh, rfl⟩

  have htr : ∀ k, IsK F k → (fun x => φ (x * k)) ∈ W := by
    intro k hk
    have heq : (fun x => φ (x * k)) = ∑ mm, (∏ i, aa mm i (piece F k i)) • bb mm := by
      funext x
      have hx : φ (x * k) = φ (x * (List.ofFn (piece F k)).prod) := by rw [← eq_listProd_piece F hk]
      rw [hx, hsum x (piece F k) (piece_mem F hk)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact Submodule.sum_mem _ (fun mm _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨mm, rfl⟩))

  let bW := Module.finBasis ℂ W
  refine ⟨Module.finrank ℂ W, fun j => ((bW j : W) : AdelicGL2 (𝓞 F) F → ℂ),
    fun j k => if hk : IsK F k then bW.repr ⟨_, htr k hk⟩ j else 0, ?_, ?_, ?_⟩
  · intro j
    have hmemT : ((bW j : W) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Submodule.span ℂ (Tset F φ) := hWT (bW j).2
    refine ⟨?_, (isArchKFinite_and_isKfSmooth_of_mem_span F hφK hφf hmemT).1,
      (isArchKFinite_and_isKfSmooth_of_mem_span F hφK hφf hmemT).2⟩
    obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hmemT
    refine ⟨n, c, fun i => Classical.choose (g i).2, fun i => (Classical.choose_spec (g i).2).1, ?_⟩
    funext x
    show ((bW j : W) : AdelicGL2 (𝓞 F) F → ℂ) x = ∑ i, c i * φ (x * Classical.choose (g i).2)
    rw [← hg]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    exact congrFun (Classical.choose_spec (g i).2).2 x
  · intro j
    rw [continuousOn_iff_continuous_restrict]
    have hcontW : Continuous (fun k : {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))} =>
        (⟨fun x => φ (x * k), htr k k.2⟩ : W)) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro x
      exact hφc.comp (continuous_const.mul continuous_subtype_val)
    have hcoord : Continuous (bW.coord j) := LinearMap.continuous_of_finiteDimensional _
    convert hcoord.comp hcontW using 1 <;> try with_reducible_and_instances rfl
    funext k
    simp only [Set.restrict_apply, Function.comp_apply]
    rw [dif_pos (show IsK F (k : AdelicGL2 (𝓞 F) F) from k.2)]
    rfl
  · intro k hk1 hk2 x
    have hk : IsK F k := ⟨hk1, hk2⟩
    have hrepr := bW.sum_repr (⟨_, htr k hk⟩ : W)
    have h1 := congrArg (fun v : W => (v : AdelicGL2 (𝓞 F) F → ℂ) x) hrepr
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    show φ (x * k) = ∑ j, (if hk : IsK F k then (bW.repr ⟨_, htr k hk⟩) j else 0) * ((bW j : W) : AdelicGL2 (𝓞 F) F → ℂ) x
    simp only [dif_pos hk]
    exact h1.symm

end KCLProof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth.KCLProof"

theorem solution
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : IsArchKFinite F φ) (_hφf : IsKfSmooth F φ) (_hφc : Continuous φ) :
    ∃ (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 F) F → ℂ) (a : Fin m → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ j, (∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → AdelicGL2 (𝓞 F) F),
          (∀ i, glFin (𝓞 F) F (k i) ∈ finiteIntegralGL2 (𝓞 F) F ∧
            ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (k i)))) ∧
          e j = fun x => ∑ i, c i * φ (x * k i)) ∧
        IsArchKFinite F (e j) ∧ IsKfSmooth F (e j)) ∧
      (∀ j, ContinuousOn (a j) {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        ∀ x : AdelicGL2 (𝓞 F) F, φ (x * k) = ∑ j, a j k * e j x :=
  KCLProof.main F φ _hφK _hφf _hφc

end
end S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth (solution)
