-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_TypeDetermination
-- name    : OddOrder_Peterfalvi_S13_TypeDetermination
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:32:32.777604+00:00
-- url     : https://prove2.me/theorems/aa4b3c84-228e-4f33-8c45-f65a33ee3a73
-- title:
--   Peterfalvi (13.2.a): type determination and the $\kappa$-ordered maximal pair
-- statement:
--   Formalizes statement (13.2.a) with its §11 input (11.9.b) (Peterfalvi, *Character Theory for the Odd Order Theorem*, Section 13). The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_TypeDetermination.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_TypeDetermination.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_Noncoherence

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

namespace Peterfalvi.S13

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

/-- **Peterfalvi (11.3), unconditional**: `𝒮(H₀C)` is not coherent — `S_H0C_not_coherent`
re-founded on the unconditional Theorem (10.8) (`S12.S_not_coherent_unconditional`, whose
partner supply is assembled internally; issue 1020 Phase 3).  If `𝒮(H₀C)` were coherent,
Theorem (6.3) (`coherent_S_of_coherent_SH0C`) would make the full family `𝒮` coherent. -/
theorem S_H0C_not_coherent_unconditional {G : Type*} [Group G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (s13hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0) :=
  fun hcoh => OddOrder.Peterfalvi.S12.S_not_coherent_unconditional hG s13hyp.base
    (coherent_S_of_coherent_SH0C hG s13hyp
      (OddOrder.Peterfalvi.S12.isTypeIIIorIV_unconditional hG s13hyp.base) hcoh)

/-- **Peterfalvi (11.9.b), unconditional** — `w₂ < w₁` for the §10 hypothesis on a type-III/IV
maximal subgroup: the refuter core `exists_zeta_residual_not_orthogonal_H0C_of_refuter`
instantiated at the unconditional (11.3) (`S_H0C_not_coherent_unconditional`), composed with
the coherence-free reduction `w2_lt_w1_of_residual_not_orthogonal`.  This is the honest heir
of the retired legacy `w2_lt_w1_of_hypothesis_H0C` (whose (11.3) routed through the
partner-sorried `S12.S_not_coherent`), and the `feitThompson`-spine consumer via
`card_kappaHall_lt_of_isTypeIIIorIV` below (issue 1020 Phase 3). -/
theorem w2_lt_w1_of_hypothesis_H0C_unconditional {G : Type*} [Group G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1) :
    hyp.w2 < hyp.w1 := by
  obtain ⟨ζ, hζS, hζirr, hζ1, h118⟩ :=
    exists_zeta_residual_not_orthogonal_H0C_of_refuter hG hyp htype hM2 hHcard
      (fun s13hyp => S_H0C_not_coherent_unconditional hG s13hyp)
  exact OddOrder.Peterfalvi.S12.w2_lt_w1_of_residual_not_orthogonal hG hyp hζS hζirr hζ1 h118

end Peterfalvi.S13

end OddOrder


