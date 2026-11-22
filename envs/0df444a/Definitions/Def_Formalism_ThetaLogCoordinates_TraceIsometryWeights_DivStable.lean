-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DivStable
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_DivStable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:16.212534+00:00
-- url     : https://prove2.me/theorems/cbaa6710-a891-44a4-83a9-69816118c296
-- title:
--   Div Stable
-- statement:
--   Definitions and structural lemmas for Div Stable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/DivStable.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset
section gen
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
def GlRel (E : ι → ι → Module.End K W) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)
def Om (E : ι → ι → Module.End K W) (S : Finset ι) (z : ι) : ℕ → Module.End K W
  | 0 => 1
  | q + 1 => ∑ i ∈ S, E z i * Om E S z q * E i z
def Pstep (E : ι → ι → Module.End K W) (S : Finset ι) (z : ι) (l : ℕ) : Module.End K W :=
  ∑ q ∈ range (l + 1),
    (((-1 : K) ^ q * (S.card.factorial : K)) / (((q + S.card).factorial : K) * (q.factorial : K))) • Om E S z q
def InvOp (E : ι → ι → Module.End K W) (l : ℕ) : List ι → Module.End K W
  | [] => 1
  | z :: L => Pstep E L.toFinset z l * InvOp E l L
def homAct {V : Type} [AddCommGroup V] [Module K V] (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W)
    (a b : ι) : Module.End K (V →ₗ[K] W) where
  toFun := fun φ => EW a b ∘ₗ φ - φ ∘ₗ EV a b
  map_add' := by
    intro φ ψ; ext x; simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]; abel
  map_smul' := by
    intro c φ; ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply, smul_sub]
def DivStable (E : ι → ι → Module.End K W) (M : AddSubgroup W) : Prop :=
  ∀ a b, a ≠ b → ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : K))⁻¹ • ((E a b) ^ k) x ∈ M
def HomLat {V : Type} [AddCommGroup V] [Module K V] (L : AddSubgroup V) (M : AddSubgroup W) :
    AddSubgroup (V →ₗ[K] W) where
  carrier := {φ | ∀ x ∈ L, φ x ∈ M}
  add_mem' := fun {φ ψ} hφ hψ x hx => by rw [LinearMap.add_apply]; exact M.add_mem (hφ x hx) (hψ x hx)
  zero_mem' := fun x _ => by rw [LinearMap.zero_apply]; exact M.zero_mem
  neg_mem' := fun {φ} hφ x hx => by rw [LinearMap.neg_apply]; exact M.neg_mem (hφ x hx)
end gen
def ZpClosed (p : ℕ) [Fact p.Prime] {W : Type} [AddCommGroup W] [Module ℚ_[p] W] (M : AddSubgroup W) : Prop :=
  ∀ c : ℚ_[p], ‖c‖ ≤ 1 → ∀ x ∈ M, c • x ∈ M
end Formalism.InvariantFactorPaths.PW


