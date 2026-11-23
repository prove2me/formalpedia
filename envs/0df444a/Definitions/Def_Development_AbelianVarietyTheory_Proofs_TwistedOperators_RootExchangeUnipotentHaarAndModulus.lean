-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:23.356259+00:00
-- url     : https://prove2.me/theorems/79be530a-1d74-40f0-a5d9-11fcde6a56db
-- title:
--   Root Exchange Unipotent Haar And Modulus
-- statement:
--   Definitions and structural lemmas for Root Exchange Unipotent Haar And Modulus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Theorems.Thm_GlobalTheory_RootEx_Model_coord_embedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
namespace GlobalTheory.RootEx.VolN
section Alg
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
def lm (P : ι → ι → Prop) (h : Matrix ι ι k) :
    Matrix {rs : ι × ι // P rs.1 rs.2} {rs : ι × ι // P rs.1 rs.2} k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then h a.1.1 b.1.1 else 0
def rm (P : ι → ι → Prop) (h : Matrix ι ι k) :
    Matrix {rs : ι × ι // P rs.1 rs.2} {rs : ι × ι // P rs.1 rs.2} k :=
  Matrix.of fun a b => if a.1.1 = b.1.1 then h b.1.2 a.1.2 else 0
def ext0 (P : ι → ι → Prop) [DecidableRel P] (e : {rs : ι × ι // P rs.1 rs.2} → k) : Matrix ι ι k :=
  Matrix.of fun r s => if h : P r s then e ⟨(r, s), h⟩ else 0
end Alg
section Grp
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
abbrev Up (n : Type) (c p : ℕ) : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s => lev p r < lev p s
abbrev Ix (n : Type) (c p : ℕ) : Type := {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}
def co (p : ℕ) (g : N k n c p) : Ix n c p → k := fun rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2
theorem co_mkNel (p : ℕ) (e : Ix n c p → k) : co p (mkNel p e) = e := by
  funext rs
  change mkN p e _ _ = _
  simp [mkN, rs.2]
theorem mkNel_co (p : ℕ) (g : N k n c p) : mkNel p (co p g) = g := by
  ext r s
  change mkN p (co p g) r s = _
  by_cases h : lev p r < lev p s
  · simp [mkN, h, co]
  · simp only [mkN, Matrix.of_apply, dif_neg h]
    exact (mem_N_iff.1 g.2 r s (not_lt.1 h)).symm
def InR (p : ℕ) (g : GL (n ⊕ Fin c) k) : Prop :=
  ∀ r s, lev p s ≤ lev p r → (r.isRight ∨ s.isRight) → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
end Grp
section Meas
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
def coEquiv (p : ℕ) : (Ix n c p → k) ≃ᵐ N k n c p where
  toFun := mkNel p
  invFun := co p
  left_inv := co_mkNel p
  right_inv := mkNel_co p
  measurable_toFun := by
    have h := (coord_embedding (k := k) (n := n) (c := c) p).1
    refine (h.measurable_comp_iff).1 ?_
    have : (co (k := k) (n := n) (c := c) p) ∘ mkNel p = id := funext (co_mkNel p)
    exact this ▸ measurable_id
  measurable_invFun := (coord_embedding (k := k) (n := n) (c := c) p).1.measurable
end Meas
end GlobalTheory.RootEx.VolN


