-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:32:50.271736+00:00
-- url     : https://prove2.me/theorems/568505e4-36bb-4d18-95d3-fcebe4cbab5c
-- title:
--   Peterfalvi (14.13)–(14.16): $\beta$ vanishing and the case (b) contradiction data
-- statement:
--   Formalizes the non-conjugate hypothesis of Peterfalvi (14.13), the two alternatives of (14.14), and the carrier for the case (b) contradiction of (14.16).
--
--   Main declarations: `NonConjugateHypothesis` (Peterfalvi (14.13)); `OrthogonalitySwitchData` (Peterfalvi (14.14)); `CaseBContradictionData` (Faithful §16 carrier for the (14.16) case-(b) contradiction inputs).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.13)**: the final comparison case assumes `L` and `M` are
not conjugate and sets `h = |H|`. -/
structure NonConjugateHypothesis (hyp : Hypothesis (G := G)) where
  Ldata : LHypothesis hyp
  Mdata : MHypothesis hyp
  not_conj : ¬ ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
  h : ℕ
  h_eq_card_H : h = Nat.card ↥Ldata.H

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The two alternatives of **Peterfalvi (14.14)**. -/
structure OrthogonalitySwitchData {hyp : Hypothesis (G := G)}
    (nc : NonConjugateHypothesis hyp) where
  caseA : Prop
  caseA_bound :
    caseA →
      (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))
  caseB : Prop
  caseB_params : caseB → hyp.base.q = 3 ∧ hyp.base.p = 5
  /-- **Peterfalvi (14.14.b), the case-(b) pairing**: in case (b) the L-side `β` pairs
  nontrivially with the M-side coherent test image — the first branch of the (7.9)
  dichotomy (`pairing_dichotomy`), packaged with its coherence bundles.  This carries
  the "(β_L^τ, ψ^{τ₁}) ≠ 0" half of Pf's case-(b) *definition*, which the `(q,p) = (3,5)`
  conclusion alone cannot recover; the (14.16) contradiction consumes it through
  `caseB_contradiction_data`. -/
  caseB_pairing :
    caseB →
      haveI := hyp.base.finiteG
      ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
      ∃ (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M),
        ClassFunction.inner
          ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal nc.Mdata.M_maximal
              nc.not_conj).first.beta)
          ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal nc.Mdata.M_maximal
              nc.not_conj).secondZetaImage) ≠ 0

namespace OrthogonalitySwitchData

/-- **Faithful §16 carrier for the (14.16) case-(b) contradiction inputs.**

Under case-(b) of (14.14) (`(β_L^τ, ψ^{τ₁}) ≠ 0`, `q = 3`, `p = 5`) and the two strict gap
inequalities, the §16 character theory supplies (Pf (14.16), p.92):

* `betaL_expansion` — the (14.11.2)-style signed `η`-grid expansion `β_L^τ = Σ_{ij} ±η_ij − χ_L`
  (`χ_L = φ^{τ₁}` or `−φ̄^{τ₁}`), derived from `(13.19.c)` applied on both the S- and T-sides
  (`exists_typeI_eta_axes_odd_of_caseB_gap`) plus the vanishing of `β_L^τ` on `W − (W₁ ∪ W₂)`;
* `eta_orthogonal_psi` — `(η_ij, ψ^{τ₁}) = 0`: `ψ^{τ₁}` is the unit-norm component removed from the
  `η`-grid in the M-side expansion (14.11.2), hence orthogonal to the whole grid;
* `chiL_orthogonal_psi` — `(χ_L, ψ^{τ₁}) = 0`: by (4.1), `L^{τ₁}` is orthogonal to `M^{τ₁}`, and
  `χ_L ∈ L^{τ₁}`, `ψ^{τ₁} ∈ M^{τ₁}`;
* `pairing_ne_zero` — `(β_L^τ, ψ^{τ₁}) ≠ 0`, the defining property of case-(b) (14.14.b).

The genuine character theory (the expansion via (14.11.2)/(13.19.c), the orthogonalities via
(14.11.2)/(4.1), and the case-(b) pairing via (14.14)) is isolated here; the contradiction itself
is then the pure inner-product computation `(β_L^τ, ψ^{τ₁}) = 0`. -/
structure CaseBContradictionData {hyp : Hypothesis (G := G)}
    (nc : NonConjugateHypothesis hyp) [Fintype G] [Invertible (Nat.card G : ℂ)] where
  /-- The L-side virtual character `β_L^τ`. -/
  betaL : ClassFunction G ℂ
  /-- The removed unit-norm L-side character `χ_L` (`= φ^{τ₁}` or `−φ̄^{τ₁}`). -/
  chiL : ClassFunction G ℂ
  /-- The M-side test character `ψ^{τ₁}` (the coherent `ν`-image of the distinguished
  `ζ` — carried as a field so the whole datum is bundle-local; the (14.16) contradiction
  is a pure inner-product computation in the four fields and never needs the anchor
  `ψ^{τ₁} = nc.Mdata.tau1 nc.Mdata.psi` itself). -/
  psiImg : ClassFunction G ℂ
  /-- The `±1` signs of the `η`-grid expansion. -/
  signs : Fin hyp.base.q → Fin hyp.base.p → ℤ
  signs_pm_one : ∀ i j, signs i j = 1 ∨ signs i j = -1
  /-- **(14.16)** signed `η`-grid expansion `β_L^τ = Σ_{ij} ε_ij η_ij − χ_L`. -/
  betaL_expansion :
    betaL =
      (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j) - chiL
  /-- **(14.11.2)**: `ψ^{τ₁}` is orthogonal to the `η`-grid. -/
  eta_orthogonal_psi : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    ClassFunction.inner (hyp.base.eta i j) psiImg = 0
  /-- **(4.1)**: `χ_L ∈ L^{τ₁}` is orthogonal to `ψ^{τ₁} ∈ M^{τ₁}`. -/
  chiL_orthogonal_psi :
    ClassFunction.inner chiL psiImg = 0
  /-- **(14.14.b)**: the case-(b) nonzero pairing `(β_L^τ, ψ^{τ₁}) ≠ 0`. -/
  pairing_ne_zero :
    ClassFunction.inner betaL psiImg ≠ 0

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16


