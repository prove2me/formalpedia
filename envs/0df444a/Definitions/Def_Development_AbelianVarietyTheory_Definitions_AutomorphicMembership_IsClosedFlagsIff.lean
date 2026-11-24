-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:37.980804+00:00
-- url     : https://prove2.me/theorems/be3f2938-095e-425a-8200-4440ad413a17
-- title:
--   Is Closed Flags Iff
-- statement:
--   Definitions and structural lemmas for Is Closed Flags Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsClosedFlagsIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_FullFlag_exists_isAdapted_of_isLocalRing
import Theorems.Thm_GlobalTheory_FullFlag_isAdapted_iff
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
namespace GlobalTheory.FlagPts
variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def Frames : Type := ∀ i, Basis (Fin (finrank k (V i))) k (V i)
def regFns : Subalgebra k (Frames k V → k) :=
  Algebra.adjoin k ({f | ∃ (i : ι) (φ : Dual k (V i)) (a : Fin (finrank k (V i))), f = fun b => φ (b i a)} ∪
    {f | ∃ (i : ι) (v : V i) (a : Fin (finrank k (V i))), f = fun b => (b i).repr v a})
instance instTopFrames : TopologicalSpace (Frames k V) := .generateFrom {s | ∃ f ∈ regFns k V, s = {b | f b ≠ 0}}
def Flags : Type := ∀ i, FullFlag k (V i) (finrank k (V i))
variable {k V}
def Frames.flags (b : Frames k V) : Flags k V := fun i => FullFlag.ofBasis (b i)
theorem flags_surjective : Function.Surjective (Frames.flags (k := k) (V := V)) := fun F => by
  choose b hb using fun i => (F i).exists_isAdapted_of_isLocalRing
  exact ⟨b, funext fun i => FullFlag.isAdapted_iff.1 (hb i)⟩
instance : TopologicalSpace (Flags k V) := .coinduced Frames.flags inferInstance
instance [∀ i, FiniteDimensional k (V i)] : Nonempty (Flags k V) := ⟨Frames.flags fun i => finBasis k (V i)⟩
theorem isClosed_zero {f : Frames k V → k} (hf : f ∈ regFns k V) : IsClosed {b | f b = 0} :=
  isOpen_compl_iff.1 (isOpen_generateFrom_of_mem ⟨f, hf, rfl⟩)
theorem isClosed_flags_iff {s : Set (Flags k V)} : IsClosed s ↔ IsClosed (Frames.flags ⁻¹' s) := isClosed_coinduced
def Flags.step (F : Flags k V) (i : ι) (n : ℕ) : Submodule k (V i) :=
  (F i).sub ⟨min n (finrank k (V i)), Nat.lt_succ_of_le (min_le_right _ _)⟩
theorem mem_step_flags {b : Frames k V} {i : ι} {n : ℕ} {v : V i} :
    v ∈ b.flags.step i n ↔ ∀ a : Fin (finrank k (V i)), n ≤ (a : ℕ) → (b i).repr v a = 0 := by
  refine (mem_basis_flag_iff _ _ _).trans (forall_congr' fun a => imp_congr_left ?_)
  have := a.2
  rw [Fin.le_def, Fin.val_castSucc]
  simp only
  omega
theorem step_flags_le {b : Frames k V} {i : ι} {n : ℕ} {P : Submodule k (V i)} :
    b.flags.step i n ≤ P ↔ ∀ a : Fin (finrank k (V i)), (a : ℕ) < n → b i a ∈ P := by
  refine ((b i).flag_le_iff).trans (forall_congr' fun a => imp_congr_left ?_)
  have := a.2
  rw [Fin.lt_def, Fin.val_castSucc]
  simp only
  omega
theorem finrank_step (F : Flags k V) (i : ι) (n : ℕ) : finrank k (F.step i n) = min n (finrank k (V i)) := by
  obtain ⟨b, rfl⟩ := flags_surjective F
  change finrank k (Submodule.span k (b i '' _)) = _
  rw [Set.image_eq_range]
  refine (finrank_span_eq_card ((b i).linearIndependent.comp _ Subtype.val_injective)).trans ?_
  rw [Fintype.card_subtype]
  simp only [Set.mem_setOf_eq, Fin.lt_def, Fin.val_castSucc, Fin.card_filter_val_lt]
  omega
theorem Flags.ext {F F' : Flags k V} (h : ∀ i n, F.step i n = F'.step i n) : F = F' :=
  funext fun i => FullFlag.ext (funext fun n => by
    have := h i n
    simpa only [Flags.step, min_eq_left (Nat.lt_succ_iff.1 n.2)] using this)
def between (n : ℕ) (A B : ∀ i, Submodule k (V i)) : Closeds (Flags k V) where
  carrier := {F | ∀ i, A i ≤ F.step i n ∧ F.step i n ≤ B i}
  isClosed' := by
    refine isClosed_flags_iff.2 ?_
    change IsClosed {b : Frames k V | ∀ i, A i ≤ b.flags.step i n ∧ b.flags.step i n ≤ B i}
    simp only [Set.setOf_forall, Set.setOf_and]
    refine isClosed_iInter fun i => IsClosed.inter (X := Frames k V) ?_ ?_
    · simp only [SetLike.le_def, mem_step_flags, Set.setOf_forall]
      exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun a => isClosed_iInter fun _ =>
        isClosed_zero (Algebra.subset_adjoin (.inr ⟨i, v, a, rfl⟩))
    · have e (v : V i) : v ∈ B i ↔ ∀ φ ∈ (B i).dualAnnihilator, φ v = 0 := by
        rw [← Submodule.mem_dualCoannihilator, Subspace.dualAnnihilator_dualCoannihilator_eq]
      simp only [step_flags_le, e, Set.setOf_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun _ => isClosed_iInter fun φ => isClosed_iInter fun _ =>
        isClosed_zero (Algebra.subset_adjoin (.inl ⟨i, φ, a, rfl⟩))
def dim (s : Closeds (Flags k V)) : ℕ := ((topologicalKrullDim (s : Set (Flags k V))).unbotD 0).toNat
example (n : ℕ) : between (k := k) (V := V) n ⊥ ⊤ = ⊤ := Closeds.ext (Set.eq_univ_of_forall fun _ _ => ⟨bot_le, le_top⟩)
example (n : ℕ) (i : ι) (h : n < finrank k (V i)) (F : Flags k V) : F ∉ between n ⊤ ⊤ := fun hF => by
  have := finrank_step F i n
  rw [top_le_iff.1 (hF i).1, finrank_top] at this
  omega
end GlobalTheory.FlagPts


