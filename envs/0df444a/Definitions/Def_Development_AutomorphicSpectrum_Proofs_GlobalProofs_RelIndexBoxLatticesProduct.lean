-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:34.174259+00:00
-- url     : https://prove2.me/theorems/f81477a0-988d-494a-a869-789ed352a64a
-- title:
--   Rel Index Box Lattices Product
-- statement:
--   Definitions and structural lemmas for Rel Index Box Lattices Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV
section Line
variable {F : Type} [Field F]
def line (O : Subring F) (c : F) : AddSubgroup F :=
  O.toAddSubgroup.map (AddMonoidHom.mulLeft c)
end Line
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
end Local
section Box
variable {F : Type} [Field F]
abbrev Idx {n : ℕ} (β : Fin n → ℕ) : Type := {p : Fin n × Fin n // β p.1 ≤ β p.2}
noncomputable def ext0 {n : ℕ} (β : Fin n → ℕ) : (Idx β → F) →+ Matrix (Fin n) (Fin n) F where
  toFun x := Matrix.of fun a b => if hab : β a ≤ β b then x ⟨(a, b), hab⟩ else 0
  map_zero' := by
    ext a b
    simp
  map_add' x y := by
    ext a b
    by_cases hab : β a ≤ β b <;> simp [hab]
end Box
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex


