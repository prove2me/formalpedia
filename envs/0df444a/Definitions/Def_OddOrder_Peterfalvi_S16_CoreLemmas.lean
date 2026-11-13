-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
-- name    : OddOrder_Peterfalvi_S16_CoreLemmas
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:23:10.574677+00:00
-- url     : https://prove2.me/theorems/8b4aaeeb-b8da-4e61-bef4-e2bf9ada43d2
-- title:
--   Peterfalvi (14.1): Section 16 core lemmas
-- statement:
--   Formalizes Hypothesis (14.1), continuing Hypothesis (13.1) into Section 16, and the associated concrete Frobenius group $H=P\rtimes U$.
--
--   Main declarations: `Hypothesis` (Peterfalvi (14.1)); `factHypothesisPPrime` (`p` is prime, as an instance keyed on the Section 16 hypothesis, so that statements mentioning…); `fieldNormalizerFrobeniusGroup` (The concrete Frobenius group `H = P \rtimes U` from BG Appendix C, with Peterfalvi Section 16…); `fieldNormalizerNormOneUnits` (The concrete norm-one unit group used as the BG complement before transport through the…).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_CoreLemmas.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_CoreLemmas.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.1)**: Section 16 continues Hypothesis (13.1) and assumes
`q < p`. -/
structure Hypothesis where
  base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)
  /-- **Peterfalvi (4.3)--(4.9), canonical T-side ν-grid supply.**

  Section 16 is the first layer where the abstract grid in `base` is identified with the
  canonical certain-type construction.  Keeping that identification as an explicit carrier
  field avoids the false generic assertion that every `S15.Hypothesis` determines its ν-grid
  up to row translation (issue 9096). -/
  nuGridSupply :
    @OddOrder.Peterfalvi.S15.NuGridSupplyData G _ base.finiteG base
  q_lt_p : base.q < base.p

namespace Hypothesis

/-- `p` is prime, as an instance keyed on the Section 16 hypothesis, so that statements
mentioning `GaloisField hyp.base.p hyp.base.q` elaborate without a local `letI`. -/
instance factHypothesisPPrime (hyp : Hypothesis (G := G)) : Fact hyp.base.p.Prime :=
  ⟨hyp.base.p_prime⟩

end Hypothesis

/-- The concrete Frobenius group `H = P \rtimes U` from BG Appendix C,
with Peterfalvi Section 16 parameters. -/
abbrev fieldNormalizerFrobeniusGroup (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup hyp.base.p hyp.base.q

/-- The concrete norm-one unit group used as the BG complement before transport
through the field-normalizer embedding. -/
abbrev fieldNormalizerNormOneUnits (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q

/-- The additive kernel of the concrete BG Frobenius group, with the local
`Fact p.Prime` bundled into the abbreviation. -/
abbrev fieldNormalizerAdditiveGroup (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q

/-- The concrete `p`-power Frobenius on the additive kernel of BG's model
`P ⋊ U`, written multiplicatively via `Multiplicative`. -/
noncomputable def fieldNormalizerAdditiveFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerAdditiveGroup hyp →* fieldNormalizerAdditiveGroup hyp where
  toFun x := Multiplicative.ofAdd (x.toAdd ^ hyp.base.p)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp [hyp.base.p_prime.ne_zero]
  map_mul' x y := by
    let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    apply Multiplicative.toAdd.injective
    exact (OddOrder.BG.AppC.NormSet.add_pow_p
      hyp.base.p hyp.base.q x.toAdd y.toAdd).symm

/-- The concrete `p`-power Frobenius on the norm-one complement. -/
noncomputable def fieldNormalizerNormOneFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerNormOneUnits hyp →* fieldNormalizerNormOneUnits hyp where
  toFun u := u ^ hyp.base.p
  map_one' := by simp
  map_mul' u v := by
    rw [mul_pow]

/-- The concrete `p`-power Frobenius of BG's semidirect product
`P ⋊ U`: it sends `(x,u)` to `(x^p,u^p)`. -/
noncomputable def fieldNormalizerFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerFrobeniusGroup hyp :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  SemidirectProduct.map
    (fieldNormalizerAdditiveFrobeniusHom (G := G) hyp)
    (fieldNormalizerNormOneFrobeniusHom (G := G) hyp)
    (by
      intro u
      ext x
      apply Multiplicative.toAdd.injective
      change (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) * x) ^ hyp.base.p =
            (((u ^ hyp.base.p : fieldNormalizerNormOneUnits hyp) :
                  (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * x ^ hyp.base.p
      simpa [map_pow] using
        (mul_pow (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q)) x hyp.base.p))

@[simp]
theorem fieldNormalizerFrobeniusHom_inl (hyp : Hypothesis (G := G))
    (x : fieldNormalizerAdditiveGroup hyp) :
    fieldNormalizerFrobeniusHom hyp (SemidirectProduct.inl x) =
      SemidirectProduct.inl (Multiplicative.ofAdd (x.toAdd ^ hyp.base.p)) := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerFrobeniusHom, fieldNormalizerAdditiveFrobeniusHom]

@[simp]
theorem fieldNormalizerFrobeniusHom_inr (hyp : Hypothesis (G := G))
    (u : fieldNormalizerNormOneUnits hyp) :
    fieldNormalizerFrobeniusHom hyp
        (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) =
      SemidirectProduct.inr (u ^ hyp.base.p) := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerFrobeniusHom, fieldNormalizerNormOneFrobeniusHom]

/-- The two conclusions of **Peterfalvi (14.2)**, packaged in the form consumed by BG Appendix C.

This is BG's own `AppC.FieldNormalizerData` — hypothesis (B) of Theorem C together with condition
(A) — *pinned* to Peterfalvi's subgroups: the four `_eq` fields record that the abstract `P`, `U`,
`W₂`, `Q` are Section 16's `data.P`, `.U`, `.W2`, `.Q`.  The Lemma C.1--C.3 development is
stated against the abstract parent; the pins are only needed where Section 16 facts about
`hyp.base.*` meet it. -/
structure FieldNormalizerData (hyp : Hypothesis (G := G)) extends
    OddOrder.BG.AppC.FieldNormalizerData hyp.base.p hyp.base.q G where
  /-- The abstract `P = σ(P)` is Peterfalvi's `P`. -/
  P_eq : P = hyp.base.P
  /-- The abstract `U = σ(U)` is Peterfalvi's `U`. -/
  U_eq : U = hyp.base.U
  /-- The abstract `W₂ = σ(P₀)` is Peterfalvi's `W₂`. -/
  W2_eq : W2 = hyp.base.W2
  /-- The abstract `Q` is Peterfalvi's `Q`. -/
  Q_eq : Q = hyp.base.Q

end OddOrder.Peterfalvi.S16


