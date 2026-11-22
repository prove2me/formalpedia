-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:17.607347+00:00
-- url     : https://prove2.me/theorems/a9d83f3a-992d-481a-b545-772eea8c57f1
-- title:
--   Diagonal Top Block
-- statement:
--   Definitions and structural lemmas for Diagonal Top Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
section general
variable {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
noncomputable def form (P : Finset α) (k : α → α → ℂ) (U V : α → H) : ℂ :=
  ∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪U p, V p'⟫_ℂ
lemma form_self_nonneg (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) (V : α → H) :
    0 ≤ (form P k V V).re := by
  classical
  let S : Submodule ℂ H := Submodule.span ℂ (V '' (P : Set α))
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (P.finite_toSet.image V)
  let b := stdOrthonormalBasis ℂ S
  have hmem : ∀ p ∈ P, V p ∈ S := fun p hp => Submodule.subset_span ⟨p, hp, rfl⟩
  let a : Fin (Module.finrank ℂ S) → α → ℂ := fun i p => ⟪((b i : S) : H), V p⟫_ℂ
  have hin : ∀ p ∈ P, ∀ p' ∈ P, ⟪V p, V p'⟫_ℂ = ∑ i, conj (a i p) * a i p' := by
    intro p hp p' hp'
    have h := b.sum_inner_mul_inner ⟨V p, hmem p hp⟩ ⟨V p', hmem p' hp'⟩
    simp only [Submodule.coe_inner] at h
    rw [← h]
    refine sum_congr rfl fun i _ => ?_
    simp only [a, inner_conj_symm]
  have e : form P k V V = ∑ i, ∑ p ∈ P, ∑ p' ∈ P, conj (a i p) * k p p' * a i p' := by
    unfold form
    symm
    rw [Finset.sum_comm]
    refine sum_congr rfl fun p hp => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun p' hp' => ?_
    rw [hin p hp p' hp', mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [e, Complex.re_sum]
  exact sum_nonneg fun i _ => hk.2 (a i)
@[instance_reducible]
noncomputable def core (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) :
    PreInnerProductSpace.Core ℂ (α → H) where
  inner U V := form P k U V
  conj_inner_symm U V := by
    unfold form
    simp only [map_sum, map_mul, inner_conj_symm]
    rw [sum_comm]
    refine sum_congr rfl fun p hp => sum_congr rfl fun p' hp' => ?_
    rw [hk.1 p' hp' p hp]
  re_inner_nonneg V := form_self_nonneg P k hk V
  add_left U V X := by
    simp only [form, Pi.add_apply, inner_add_left, mul_add, sum_add_distrib]
  smul_left U V r := by
    simp only [form, Pi.smul_apply, inner_smul_left, mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun p' _ => by ring
end general
section points
variable {E : Type} [DecidableEq E]
def ls (p : Pt E) : ℕ := (p.getLast?.map Prod.fst).getD 0
end points
end Formalism.FourierDecayAlt.P.TA1
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.TA Finset Filter Topology TA1
open scoped InnerProductSpace ComplexConjugate
end Formalism.FourierDecayAlt.P


