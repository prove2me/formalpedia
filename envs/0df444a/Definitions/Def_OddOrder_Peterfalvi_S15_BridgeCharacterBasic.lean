-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacterBasic
-- name    : OddOrder_Peterfalvi_S15_BridgeCharacterBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:16.105776+00:00
-- url     : https://prove2.me/theorems/be9c3bd2-60b4-4086-9d20-549a90249de1
-- title:
--   Peterfalvi §15: the bridge character, opening layer
-- statement:
--   The opening layer of the (13.18) bridge character: the induced trivial character, the virtual characters $\beta_j$ and the genuine $S$-side Dade image.
--
--   Main declarations: `indPW1` (The induced trivial character); `betaGrid` (Peterfalvi (13.18) `S`-side virtual character); `tauSbetaGrid` (The genuine `S`-side Dade image); `GammaGrid` (Peterfalvi (13.18) residual).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The induced trivial character** `Ind_{P⋊W₁}^S(1)` of the subgroup `P ⋊ W₁ ≤ S`, the
positive part of the (13.18) bridge character `β_j`.  Its squared `S`-norm is the Frobenius
value `(u−1)/q + 1` (`norm_induce_one_frobenius` composed with the `S̄ = S/P = U⋊W₁` inflation). -/
noncomputable def indPW1 [Finite G] (hyp : Hypothesis (G := G)) : ClassFunction ↥hyp.S ℂ :=
  ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
    (trivialClassFunction ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S))

/-- **Peterfalvi (13.18) `S`-side virtual character** `β_j := Ind_{P⋊W₁}^S(1) − μ_{0j}`
(Coq `PFsection13.FTtypeP_bridge`).  The induced trivial character `indPW1 hyp` of `P ⋊ W₁ ≤ S`
minus the base-row grid irreducible `μ_{0j} = hyp.mu 0 j`. -/
noncomputable def betaGrid [Finite G] (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ClassFunction ↥hyp.S ℂ :=
  indPW1 hyp - hyp.mu ⟨0, hyp.q_prime.pos⟩ j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The genuine `S`-side Dade image** `τ_S(β_{#1})` of the (13.18) bridge character at column
`#1`.  Uses the honest (13.2.e) Dade isometry `τ_S = dadeIntegralCharacterMap (hyp.dadeHypS0 hG) …`
— the `S`-instance of the (5.3) Dade map — **NOT** the off-path `= 0` placeholder `hyp.tauS`. -/
noncomputable def tauSbetaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction G ℂ :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData)
    (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18) residual** `Γ := τ_S(β_{#1}) − 1_G + η_{01}` (Coq
`PFsection13.FTtypeP_bridge_gap`).  `η_{01} = hyp.eta 0 1` is the (3.3) grid image `τ₃(ω_{01})`;
`1_G = constOne G`.  Note `Γ` does not depend on the column `j` of `βData`. -/
noncomputable def GammaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction G ℂ :=
  tauSbetaGrid hG hyp - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
    + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩

end OddOrder.Peterfalvi.S15


