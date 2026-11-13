-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:53:04.453645+00:00
-- url     : https://prove2.me/theorems/c54692e9-9c60-4d17-aeb8-bf6704a20291
-- title:
--   Peterfalvi (3.2.d): canonicalization at the hypothesis level
-- statement:
--   Provides a canonicalization result for Hypothesis (13.1): a class function orthogonal to $\eta$ vanishes as in Peterfalvi (3.2.d).
--
--   Main declarations: `Hypothesis.vanish_of_inner_eta_eq_zero` (Peterfalvi (3.2.d)).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Peterfalvi (3.2.d)** (hypothesis-level): a class function of `G` orthogonal to the whole
`η`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — every irreducible of `G` off the
`σ`-image vanishes on `Ŵ`, and the `η_{ij} = ω_{ij}^{τ₃}` enumerate the image.  Faithful
producer; the honest supply is `S05.eq_zero_of_mem_V_of_inner_chiFam_eq_zero` (proven) through
the spine's `ω`-grid ↔ character-pair identification (`gridEquivE`/`omegaProdChar` — the
issue-2033 threading pattern; the grid here is `Fin q × Fin p`-indexed while the S05 family is
hom-pair-indexed, and the enumerations correspond along `w1CharEquiv`/`chi2enum`). -/
theorem Hypothesis.vanish_of_inner_eta_eq_zero [Finite G] (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ)
    (horth : ∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) χ = 0)
    {w : G} (hwW : w ∈ hyp.W) (hnot : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G)) :
    χ w = 0 := by
  refine hyp.eta_complete_vanish χ (fun i j => ?_) w hwW hnot
  rw [← hyp.eta_eq_tau_omega]
  exact horth i j

end OddOrder.Peterfalvi.S15


