-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
-- name    : SharpIntermediateSubgroupBounds_QBinomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:40:41.516269+00:00
-- url     : https://prove2.me/theorems/1dfeb273-dbc3-4a80-b014-671e74024599
-- title:
--   QBinomial
-- statement:
--   Definitions and structural lemmas for QBinomial, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
def qBinom (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)
@[simp] theorem qBinom_zero_zero (q : ℕ) : qBinom q 0 0 = 1 := rfl
@[simp] theorem qBinom_zero_succ (q k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl
@[simp] theorem qBinom_succ_zero (q n : ℕ) : qBinom q (n + 1) 0 = 1 := rfl
@[simp] theorem qBinom_succ_succ (q n k : ℕ) :
    qBinom q (n + 1) (k + 1) =
      qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl
theorem qBinom_eq_zero_of_lt (q : ℕ) : ∀ {n k : ℕ}, n < k → qBinom q n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => by simp
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
      rw [qBinom_succ_succ]
      have hnk : n < k := by omega
      have hnks : n < k + 1 := by omega
      simp [qBinom_eq_zero_of_lt q hnk, qBinom_eq_zero_of_lt q hnks]
@[simp] theorem qBinom_self (q : ℕ) : ∀ n : ℕ, qBinom q n n = 1
  | 0 => by simp
  | n + 1 => by
      rw [qBinom_succ_succ]
      simp [qBinom_self q n, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
def qFactorial (q n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (q ^ (i + 1) - 1)
@[simp] theorem qFactorial_zero (q : ℕ) : qFactorial q 0 = 1 := by
  simp [qFactorial]
abbrev LinearIndependentFrames (K V : Type*) [Semiring K] [AddCommMonoid V] [Module K V]
    (k : ℕ) :=
  {s : Fin k → V // LinearIndependent K s}
abbrev FinrankSubspaces (K V : Type*) [Semiring K] [AddCommMonoid V] [Module K V]
    (k : ℕ) :=
  {W : Submodule K V // Module.finrank K W = k}
theorem span_coe_frame_eq_submodule
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (k : ℕ) (W : Submodule K V) (s : Fin k → W)
    (hs : LinearIndependent K s) (hW : Module.finrank K W = k) :
    Submodule.span K (Set.range fun i ↦ (s i : V)) = W := by
  have htop : Submodule.span K (Set.range s) = ⊤ :=
    hs.span_eq_top_of_card_eq_finrank' (by simp [hW])
  change Submodule.span K (Set.range (W.subtype ∘ s)) = W
  rw [Set.range_comp, ← Submodule.map_span, htop, Submodule.map_top,
    Submodule.range_subtype]
noncomputable def linearIndependentFramesEquiv
    (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (k : ℕ) :
    LinearIndependentFrames K V k ≃
      Σ W : FinrankSubspaces K V k, LinearIndependentFrames K W.1 k := by
  let forward : LinearIndependentFrames K V k →
      Σ W : FinrankSubspaces K V k, LinearIndependentFrames K W.1 k := fun s ↦
    ⟨⟨Submodule.span K (Set.range s.1), by
        simpa using finrank_span_eq_card s.2⟩,
      ⟨fun i ↦ ⟨s.1 i, Submodule.subset_span (Set.mem_range_self i)⟩,
        linearIndependent_span s.2⟩⟩
  let backward : (Σ W : FinrankSubspaces K V k,
      LinearIndependentFrames K W.1 k) → LinearIndependentFrames K V k := fun x ↦
    ⟨fun i ↦ (x.2.1 i : V),
      x.2.2.map' x.1.1.subtype (Submodule.ker_subtype x.1.1)⟩
  refine Equiv.ofBijective forward ⟨?_, ?_⟩
  · intro s t hst
    have := congrArg backward hst
    exact Subtype.ext (congrArg Subtype.val this)
  · intro x
    refine ⟨backward x, ?_⟩
    rcases x with ⟨W, s⟩
    have hfirst : (forward (backward ⟨W, s⟩)).1 = W :=
      Subtype.ext (span_coe_frame_eq_submodule k W.1 s.1 s.2 W.2)
    have hsub :
        Submodule.span K (Set.range fun i ↦ ((s.1 i : W.1) : V)) = W.1 :=
      congrArg Subtype.val hfirst
    apply Sigma.ext hfirst
    simp only [forward, backward]
    apply (Subtype.heq_iff_coe_heq ?_ ?_).2
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      apply (Subtype.heq_iff_coe_eq ?_).2
      · rfl
      · intro x
        change x ∈ Submodule.span K (Set.range fun i ↦ ((s.1 i : W.1) : V)) ↔ x ∈ W.1
        rw [hsub]
    · exact congrArg (fun U : Submodule K V ↦ Fin k → U) hsub
    · apply Function.hfunext
        (congrArg (fun U : Submodule K V ↦ Fin k → U) hsub)
      intro x y hxy
      congr! 2
      funext z
      rw [hsub]
def frameProd (q n k : ℕ) : ℕ :=
  ∏ i : Fin k, (q ^ n - q ^ i.val)
@[simp] theorem frameProd_zero (q n : ℕ) : frameProd q n 0 = 1 := by
  simp [frameProd]
def framePower (q k : ℕ) : ℕ := ∏ i : Fin k, q ^ i.val
@[simp] theorem framePower_zero (q : ℕ) : framePower q 0 = 1 := by
  simp [framePower]
noncomputable def submoduleEquivSigmaFinrank
    (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    Submodule K V ≃
      Σ k : Fin (Module.finrank K V + 1), FinrankSubspaces K V k.val where
  toFun W := ⟨⟨Module.finrank K W, Nat.lt_succ_of_le W.finrank_le⟩, ⟨W, rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨k, W⟩
    rcases W with ⟨W, hW⟩
    have hk : (⟨Module.finrank K W, Nat.lt_succ_of_le W.finrank_le⟩ :
        Fin (Module.finrank K V + 1)) = k := Fin.ext hW
    cases hk
    rfl
def totalQBinom (q n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), qBinom q n k.val
end SharpIntermediateSubgroupBounds


