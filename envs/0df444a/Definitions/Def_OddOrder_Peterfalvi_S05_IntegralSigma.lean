-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_IntegralSigma
-- name    : OddOrder_Peterfalvi_S05_IntegralSigma
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:06:51.190764+00:00
-- url     : https://prove2.me/theorems/c09e3805-b040-499d-8af0-0fdf929760ec
-- title:
--   Peterfalvi §5: the (3.2) $\sigma$-isometry as an integral character map
-- statement:
--   Formalizes the $\sigma$-isometry of Peterfalvi (3.2) as a $\mathbb{Z}$-valued character map (Peterfalvi, *Character Theory for the Odd Order Theorem*, §3). The file is a bridge leaf on the Feit–Thompson critical path.
--
--   Main declarations: `sigmaIntegral` (Peterfalvi (3.2), integral form).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_IntegralSigma.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_IntegralSigma.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_SigmaIsometry
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

variable (hyp : TICyclicHypothesis G) [Fintype hyp.W]
  [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
  (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)

/-- **Peterfalvi (3.2), integral form.**  The ℂ-linear σ-isometry
(`TICyclicHypothesis.sigma`) re-viewed as an integral (ℤ-linear) character map
on the virtual-character lattice.  This is the concrete
`S07.IntegralCharacterMap ↥W G` that `S15.Hypothesis.tau3` is pinned to. -/
noncomputable def sigmaIntegral :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap hyp.W G :=
  (hyp.sigma hVeq app).restrictScalars ℤ

@[simp] theorem sigmaIntegral_apply (φ : ClassFunction hyp.W ℂ) :
    hyp.sigmaIntegral hVeq app φ = hyp.sigma hVeq app φ :=
  rfl

/-- **Peterfalvi (3.2)(c)** for the integral map: it is the identity on `V`. -/
theorem sigmaIntegral_apply_of_mem_V (α : ClassFunction hyp.W ℂ) {v : G}
    (hv : v ∈ hyp.V) :
    hyp.sigmaIntegral hVeq app α v = α ⟨v, hyp.V_subset_W hv⟩ :=
  hyp.sigma_apply_of_mem_V hVeq app α hv

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05


