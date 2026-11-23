-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:00.526795+00:00
-- url     : https://prove2.me/theorems/f4944e09-7757-4aec-9c74-25bff5e67252
-- title:
--   Det Of Block Diag
-- statement:
--   Definitions and structural lemmas for Det Of Block Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DetOfBlockDiag.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def embF (v : Ent X → ℂ) (τ : X.Ψ) (x c : Fin r) : ℂ := if h : c < x then v ⟨τ, ⟨(x, c), h⟩⟩ else 0
def lmulL (N : Frame X.Ψ r) : (Ent X → ℂ) →ₗ[ℂ] (Ent X → ℂ) where
  toFun v e := ∑ x, N e.1 e.2.1.1 x * embF X v e.1 x e.2.1.2
  map_add' v w := by
    funext e
    simp only [Pi.add_apply, embF]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  map_smul' a v := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, embF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
def rmulL (b : Frame X.Ψ r) : (Ent X → ℂ) →ₗ[ℂ] (Ent X → ℂ) where
  toFun v e := ∑ y, embF X v e.1 e.2.1.1 y * b e.1 y e.2.1.2
  map_add' v w := by
    funext e
    simp only [Pi.add_apply, embF]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  map_smul' a v := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, embF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf


