-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_OmegaSigmaGrid
-- name    : OddOrder_Peterfalvi_S05_OmegaSigmaGrid
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:10:46.6309+00:00
-- url     : https://prove2.me/theorems/76299a16-d722-4658-a997-41c603d9c607
-- title:
--   Peterfalvi §5: the $\omega^\sigma$-grid (the $\sigma$-image of the $\omega$-grid)
-- statement:
--   Formalizes the $\omega^\sigma$-grid of Peterfalvi (3.6), the $\sigma$-image of the (3.3) $\omega$-grid (Peterfalvi, *Character Theory for the Odd Order Theorem*, §3). The file is a bridge leaf on the Feit–Thompson critical path.
--
--   Main declarations: `omegaSigmaGrid` (Peterfalvi (3.6) `ω^σ`-grid).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_OmegaSigmaGrid.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_OmegaSigmaGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_IntegralSigma
import Definitions.Def_OddOrder_Peterfalvi_S05_OmegaGrid

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

variable (hyp : TICyclicHypothesis G) [Fintype hyp.W]
  [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
  (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
  [NeZero (Nat.card hyp.W1)] [NeZero (Nat.card hyp.W2)]

/-- **Peterfalvi (3.6) `ω^σ`-grid** = `σ(ω)`: the integral-σ image of the (3.3)
ω-grid, the virtual characters `ω_{ij}^σ` of `G`.  This is the family that
`S15.Hypothesis.eta` is pinned to (`S12.CharacterParameters.omegaSigma` uses the
aligned sibling `S12.Hypothesis.alignedOmegaSigmaGrid`). -/
noncomputable def omegaSigmaGrid :
    Fin (Nat.card hyp.W1) → Fin (Nat.card hyp.W2) → ClassFunction G ℂ :=
  fun i j => hyp.sigmaIntegral hVeq app (hyp.omegaGrid i j)

@[simp] theorem omegaSigmaGrid_apply (i : Fin (Nat.card hyp.W1))
    (j : Fin (Nat.card hyp.W2)) :
    hyp.omegaSigmaGrid hVeq app i j = hyp.sigmaIntegral hVeq app (hyp.omegaGrid i j) :=
  rfl

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05


