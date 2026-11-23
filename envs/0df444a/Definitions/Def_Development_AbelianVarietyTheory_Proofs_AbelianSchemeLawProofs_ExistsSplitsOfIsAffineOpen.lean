-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:15.856315+00:00
-- url     : https://prove2.me/theorems/9a446dff-b7e7-434f-815b-9b25f5df7751
-- title:
--   Exists Splits Of Is Affine Open
-- statement:
--   Definitions and structural lemmas for Exists Splits Of Is Affine Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace GlobalTheory.KuennethOne
variable {Z : Scheme.{0}}
noncomputable def rs {U V : Z.Opens} (h : U ≤ V) : Γ(Z, V) →+* Γ(Z, U) :=
  (Z.presheaf.map (homOfLE h).op).hom
variable {I : Type} (V : I → Z.Opens) (φ : ∀ a b, Γ(Z, V a ⊓ V b))
def IsCocycle : Prop :=
  ∀ a b d (N : Z.Opens) (ha : N ≤ V a) (hb : N ≤ V b) (hd : N ≤ V d),
    rs (le_inf ha hb) (φ a b) + rs (le_inf hb hd) (φ b d) = rs (le_inf ha hd) (φ a d)
def Splits (O : Z.Opens) (ψ : ∀ a, Γ(Z, O ⊓ V a)) : Prop :=
  ∀ a b (N : Z.Opens) (hO : N ≤ O) (ha : N ≤ V a) (hb : N ≤ V b),
    rs (le_inf ha hb) (φ a b) = rs (le_inf hO ha) (ψ a) - rs (le_inf hO hb) (ψ b)
def IsDiff {O O' P : Z.Opens} (ψ : ∀ a, Γ(Z, O ⊓ V a)) (ψ' : ∀ a, Γ(Z, O' ⊓ V a))
    (hO : P ≤ O) (hO' : P ≤ O') (c : Γ(Z, P)) : Prop :=
  ∀ a (M : Z.Opens) (hM : M ≤ P) (ha : M ≤ V a),
    rs hM c = rs (le_inf (hM.trans hO) ha) (ψ a) - rs (le_inf (hM.trans hO') ha) (ψ' a)
variable {V φ}
end GlobalTheory.KuennethOne


