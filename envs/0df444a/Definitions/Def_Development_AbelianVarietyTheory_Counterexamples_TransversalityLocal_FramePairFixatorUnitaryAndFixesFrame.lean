-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
-- name    : Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:14.340702+00:00
-- url     : https://prove2.me/theorems/0741f37e-ca34-50f0-90d2-472cf75e4874
-- title:
--   Frame Pair Fixator Unitary And Fixes Frame
-- statement:
--   Definitions and structural lemmas for Frame Pair Fixator Unitary And Fixes Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
namespace GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
section General
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
theorem X_zero (f : Fin 1 → V) : H.X (r := 0) f = ⊥ := by
  change Submodule.span E (Set.range fun a : Fin 0 => f a.castSucc) = ⊥
  rw [Set.range_eq_empty, Submodule.span_empty]
theorem mem_perp_zero (f : Fin 1 → V) (v : V) : v ∈ H.perp (H.X (r := 0) f) := by
  show ∀ x ∈ H.X (r := 0) f, H.h v x = 0
  intro x hx
  rw [X_zero, Submodule.mem_bot] at hx
  subst hx
  rw [H.h_herm, H.h_zero_left, map_zero]
theorem mkW_inj (f : Fin 1 → V) : Function.Injective (H.mkW (r := 0) f) := by
  intro a b hab
  simp only [HermSp.mkW, Submodule.mkQ_apply] at hab
  have hXb : ∀ v : V, v ∈ H.X (r := 0) f → v = 0 := fun v hv => by
    rw [X_zero] at hv
    exact (Submodule.mem_bot E).mp hv
  have hmem := (Submodule.Quotient.eq _).mp hab
  have h0 : ((a - b : H.perp (H.X (r := 0) f)) : V) = 0 := hXb _ (Submodule.mem_comap.mp hmem)
  exact sub_eq_zero.mp (Subtype.ext h0)
end General
section Model
variable (M) (m : ℕ)
def stdH : HermSp M (Fin (m + 2) → E) where
  h x y := ∑ i, x i * M.L.cj (y i)
  h_add_left x x' y := by simp [add_mul, Finset.sum_add_distrib]
  h_smul_left a x y := by simp [Finset.mul_sum, mul_assoc]
  h_herm x y := by simp [map_sum, M.L.cj_cj, mul_comm]
  nondeg x hx := by
    funext i
    simpa [Pi.single_apply, apply_ite M.L.cj] using hx (Pi.single i 1)
  free := inferInstance
  fin := inferInstance
theorem stdH_single (x : Fin (m + 2) → E) (i) : (stdH M m).h x (Pi.single i 1) = x i := by
  change ∑ j, x j * M.L.cj ((Pi.single i (1 : E) : Fin (m + 2) → E) j) = x i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h
def vec (c : F) : Fin (m + 2) → E := Pi.single 0 1 + Pi.single 1 (algebraMap F E c)
theorem vec_zero (c : F) : vec (E := E) m c 0 = 1 := by
  have h : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
  simp [vec, Pi.single_apply, h]
theorem vec_one (c : F) : vec (E := E) m c 1 = algebraMap F E c := by
  have h : (1 : Fin (m + 2)) ≠ 0 := by simp [Fin.ext_iff]
  simp [vec, Pi.single_apply, h]
theorem h_vec (c c' : F) : (stdH M m).h (vec m c) (vec m c') = algebraMap F E (1 + c * c') := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
  change ∑ i, vec m c i * M.L.cj (vec m c' i) = _
  rw [Finset.sum_eq_add (0 : Fin (m + 2)) 1 h01]
  · rw [vec_zero, vec_zero, vec_one, vec_one]
    simp [map_add, map_mul]
  · intro i _ hi
    simp [vec, Pi.single_apply, hi.1, hi.2]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro h
    exact absurd (Finset.mem_univ _) h
def frame (c : F) : FrameD (stdH M m) 0 where
  f _ := vec m c
  es := Fin.elim0
  T := -(1 + c * c)
  h_iso a b h := by
    rcases h with h | h <;> exact absurd (Subsingleton.elim (α := Fin 1) _ _) h
  h_zz := by rw [h_vec, map_neg, neg_neg]
  h_ss i := i.elim0
  h_es i := i.elim0
  h_sz i := i.elim0
def pair : FPair (stdH M m) 0 := ⟨frame M m 0, frame M m (theta M)⟩
theorem theta_int : theta M ∈ 𝒪[F] := by
  rcases h : M.split with _ | g <;> simp only [theta, h]
  · exact one_mem _
  · exact g.q.2
theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])
theorem alg_mem {c : F} (hc : c ∈ 𝒪[F]) : algebraMap F E c ∈ M.L.O := by
  rw [M.L.O_def]
  have e : algebraMap F E c = algebraMap 𝒪[F] E ⟨c, hc⟩ := by
    rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
    rfl
  rw [e]
  exact isIntegral_algebraMap
def inn (c : F) : Submodule M.L.O ((stdH M m).Wb (r := 0) (frame M m c).f) :=
  Submodule.span M.L.O (Set.range fun i : Fin (m + 2) =>
    (stdH M m).mkW (r := 0) (frame M m c).f ⟨Pi.single i 1, mem_perp_zero _ _⟩)
theorem mem_inn (c : F) (x : (stdH M m).perp ((stdH M m).X (r := 0) (frame M m c).f)) :
    (stdH M m).mkW (r := 0) (frame M m c).f x ∈ inn M m c ↔ ∀ i, x.1 i ∈ M.L.O := by
  constructor
  · intro hx

    suffices key : ∀ w ∈ inn M m c, ∃ y : (stdH M m).perp ((stdH M m).X (r := 0) (frame M m c).f),
        (stdH M m).mkW (r := 0) (frame M m c).f y = w ∧ ∀ i, y.1 i ∈ M.L.O by
      obtain ⟨y, hy, hyO⟩ := key _ hx
      have hxy : y = x := mkW_inj _ hy
      rw [← hxy]
      exact hyO
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      refine ⟨_, rfl, fun j => ?_⟩
      change (Pi.single i (1 : E) : Fin (m + 2) → E) j ∈ M.L.O
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => exact ⟨0, map_zero _, fun j => zero_mem _⟩
    | add w w' _ _ hw hw' =>
      obtain ⟨y, rfl, hy⟩ := hw
      obtain ⟨y', rfl, hy'⟩ := hw'
      exact ⟨y + y', map_add _ _ _, fun j => add_mem (hy j) (hy' j)⟩
    | smul a w _ hw =>
      obtain ⟨y, rfl, hy⟩ := hw
      refine ⟨(a : E) • y, (map_smul _ _ _).trans rfl, fun j => ?_⟩
      change (a : E) * y.1 j ∈ M.L.O
      exact mul_mem a.2 (hy j)
  · intro hx
    have hsum : x = ∑ i, x.1 i • (⟨Pi.single i 1, mem_perp_zero _ _⟩ :
        (stdH M m).perp ((stdH M m).X (r := 0) (frame M m c).f)) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    change ((⟨x.1 i, hx i⟩ : M.L.O) : E) • _ ∈ inn M m c
    exact Submodule.smul_mem _ (⟨x.1 i, hx i⟩ : M.L.O) (Submodule.subset_span ⟨i, rfl⟩)
theorem vec_mem {c : F} (hc : c ∈ 𝒪[F]) (i) : vec (E := E) m c i ∈ M.L.O := by
  simp only [vec, Pi.add_apply]
  refine Subring.add_mem _ ?_ ?_
  · rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · rw [Pi.single_apply]
    split_ifs
    exacts [alg_mem M hc, zero_mem _]
theorem isInner {c : F} (hc : c ∈ 𝒪[F]) : (frame M m c).IsInner (inn M m c) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ?_, ?_⟩
  · rw [mem_inn]
    constructor
    · intro hx y hy
      rw [mem_inn] at hy
      change ∑ i, x.1 i * M.L.cj (y.1 i) ∈ M.L.O
      exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hx i) (cj_mem M (hy i))
    · intro h i
      have hi := h ⟨Pi.single i 1, mem_perp_zero _ _⟩ ((mem_inn M m c _).mpr fun j => by
        show (Pi.single i (1 : E) : Fin (m + 2) → E) j ∈ M.L.O
        rw [Pi.single_apply]
        split_ifs
        exacts [one_mem _, zero_mem _])
      change (stdH M m).h x.1 (Pi.single i 1) ∈ M.L.O at hi
      rwa [stdH_single] at hi
  · refine ⟨⟨vec m c, mem_perp_zero _ _⟩, rfl, (mem_inn M m c _).mpr (vec_mem M m hc), ?_⟩
    intro a y hy hxy
    rw [mem_inn] at hy
    rw [← map_smul] at hxy
    have e := congrArg (fun u => u.1 0) (mkW_inj _ hxy)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, vec_zero] at e
    exact isUnit_iff_exists_inv.mpr ⟨⟨y.1 0, hy 0⟩, Subtype.ext e.symm⟩
def term : Term (Fin (m + 2) → E) M 0 :=
  ⟨Submodule.span M.L.O {v | ∀ i, v i ∈ M.L.O}, (pair M m).A.f, (pair M m).B.f,
    (pair M m).A.T, (pair M m).B.T⟩
def datum : Datum (pair M m) where
  L := inn M m 0
  L' := inn M m (theta M)
  hL := isInner M m (zero_mem _)
  hL' := isInner M m (theta_int M)
  io := {p | ∃ g, M.split = some g ∧ p ∈ (stdH M m).iotaGraph g (term M m)}
  io_L h := by ext p; simp [h]
end Model
end GlobalTheory.NonGenericLocalCheck


