-- Prove2me | Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms
-- name    : OddOrder_BG_AppC_LemmaC3_NormalForms
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:24:11.046321+00:00
-- url     : https://prove2.me/theorems/1a3653f6-5f57-455d-b2e3-e7469c4d84b6
-- title:
--   Bender–Glauberman Appendix C, Lemma C.3 Step 4: relations (C.4)–(C.7) and the (C.5) normal forms
-- statement:
--   Formalizes relations (C.4)–(C.7) of Step 4 in Bender–Glauberman Appendix C, Lemma C.3 (§3, pp. 148–152). The three connector words in relation (C.4) are single commutator swaps inside the abelian group $Q$, each rewriting a connector so that the neighbouring $t$-powers telescope, turning $M_1M_2M_3$ into relation (C.4); each $M_i$ is then written in the normal form $u_is_iv_i$ of (C.5).
--
--   Main definitions: `Step4C5NormalForms` (the normal-form package for the three factors), `factor1`, `factor2`, `factor3` (the normal-form factors $u_is_iv_i$), `frobenius` (relation (C.8) as closure of the package under Frobenius), and `w1` ($w_1=v_2^{t^{-1}}u_3$, from the rearrangement leading to (C.7)).
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_NormalForms.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_LemmaC3_NormalForms.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- The first BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^3)⁻¹ a⁻¹`. -/
theorem step4M1_eq_sigma_inr
    (data : FieldNormalizerData p q G)
    (a : NormSet.normOneUnits p q) :
    data.step4M1 a =
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) := by
  unfold step4M1
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    3 a⁻¹]
  simp [map_inv]

/-- The second BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^2)⁻¹ (a b⁻¹)`. -/
theorem step4M2_eq_sigma_inr
    (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) :
    data.step4M2 a b =
      data.s ^ (3 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-1 : ℤ) := by
  unfold step4M2
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    2 (a * b⁻¹)]
  simp [map_mul, map_inv]

/-- The third BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = tConj⁻¹ b`. -/
theorem step4M3_eq_sigma_inr
    (data : FieldNormalizerData p q G)
    (b : NormSet.normOneUnits p q) :
    data.step4M3 b =
      data.s ^ (2 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-3 : ℤ) := by
  unfold step4M3
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 b]
  group

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` normal-form package for the three
terms appearing in the already-proved relation `(C.4)`.  The `hM*` fields state
the Step 1 normal forms of BG's named factors, and the `right*` fields record the
corresponding mod-`P` complement readings. -/
structure Step4C5NormalForms (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) where
  c1 : ZMod p
  c2 : ZMod p
  c3 : ZMod p
  u1 : NormSet.normOneUnits p q
  v1 : NormSet.normOneUnits p q
  u2 : NormSet.normOneUnits p q
  v2 : NormSet.normOneUnits p q
  u3 : NormSet.normOneUnits p q
  v3 : NormSet.normOneUnits p q
  hM1 :
    data.step4M1 a =
      data.sigma (SemidirectProduct.inr u1 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c1) *
          data.sigma (SemidirectProduct.inr v1 : NormSet.normOneFrobeniusGroup p q)
  hM2 :
    data.step4M2 a b =
      data.sigma (SemidirectProduct.inr u2 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c2) *
          data.sigma (SemidirectProduct.inr v2 : NormSet.normOneFrobeniusGroup p q)
  hM3 :
    data.step4M3 b =
      data.sigma (SemidirectProduct.inr u3 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c3) *
          data.sigma (SemidirectProduct.inr v3 : NormSet.normOneFrobeniusGroup p q)
  right1 : (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u1 * v1
  right2 : (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹) = u2 * v2
  right3 : (data.tConjNormOneUnitsAut ^ 1)⁻¹ b = u3 * v3

namespace Step4C5NormalForms

/-- The first normal-form factor `u₁ s₁ v₁` from `(C.5)`. -/
noncomputable def factor1 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q) *
    data.sigma (primeLineElement p q forms.c1) *
      data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q)

/-- The second normal-form factor `u₂ s₂ v₂` from `(C.5)`. -/
noncomputable def factor2 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u2 : NormSet.normOneFrobeniusGroup p q) *
    data.sigma (primeLineElement p q forms.c2) *
      data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q)

/-- The third normal-form factor `u₃ s₃ v₃` from `(C.5)`. -/
noncomputable def factor3 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q) *
    data.sigma (primeLineElement p q forms.c3) *
      data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q)

/-- BG Appendix C `(C.8)` applied to the first `(C.5)` normal form. -/
theorem hM1_frobenius
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.step4M1 (a ^ p) =
      data.sigma (SemidirectProduct.inr (forms.u1 ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c1) *
          data.sigma (SemidirectProduct.inr (forms.v1 ^ p) :
            NormSet.normOneFrobeniusGroup p q) := by
  have hneutral :
      data.s ^ (1 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
                NormSet.normOneFrobeniusGroup p q) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q forms.c1) *
            data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q) := by
    have h := forms.hM1
    rw [data.step4M1_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (1 : ℤ)) (r := (-2 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
    (u := forms.u1) (v := forms.v1) (c := forms.c1) hneutral
  rw [data.step4M1_eq_sigma_inr]
  simpa [map_pow, map_inv] using hpow

/-- BG Appendix C `(C.8)` applied to the second `(C.5)` normal form. -/
theorem hM2_frobenius
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.step4M2 (a ^ p) (b ^ p) =
      data.sigma (SemidirectProduct.inr (forms.u2 ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c2) *
          data.sigma (SemidirectProduct.inr (forms.v2 ^ p) :
            NormSet.normOneFrobeniusGroup p q) := by
  have hneutral :
      data.s ^ (3 : ℤ) *
            data.sigma
              (SemidirectProduct.inr
                ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
                NormSet.normOneFrobeniusGroup p q) *
          data.s ^ (-1 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u2 : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q forms.c2) *
            data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q) := by
    have h := forms.hM2
    rw [data.step4M2_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (3 : ℤ)) (r := (-1 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹))
    (u := forms.u2) (v := forms.v2) (c := forms.c2) hneutral
  rw [data.step4M2_eq_sigma_inr]
  simpa [map_pow, map_mul, map_inv, mul_pow] using hpow

/-- BG Appendix C `(C.8)` applied to the third `(C.5)` normal form. -/
theorem hM3_frobenius
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.step4M3 (b ^ p) =
      data.sigma (SemidirectProduct.inr (forms.u3 ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c3) *
          data.sigma (SemidirectProduct.inr (forms.v3 ^ p) :
            NormSet.normOneFrobeniusGroup p q) := by
  have hneutral :
      data.s ^ (2 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
                NormSet.normOneFrobeniusGroup p q) *
          data.s ^ (-3 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q forms.c3) *
            data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q) := by
    have h := forms.hM3
    rw [data.step4M3_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (2 : ℤ)) (r := (-3 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b)
    (u := forms.u3) (v := forms.v3) (c := forms.c3) hneutral
  rw [data.step4M3_eq_sigma_inr]
  simpa [map_pow] using hpow

/-- BG Appendix C `(C.8)` as closure of the whole `(C.5)` normal-form package
under the concrete `p`-power Frobenius. -/
noncomputable def frobenius
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    Step4C5NormalForms data (a ^ p) (b ^ p) where
  c1 := forms.c1
  c2 := forms.c2
  c3 := forms.c3
  u1 := forms.u1 ^ p
  v1 := forms.v1 ^ p
  u2 := forms.u2 ^ p
  v2 := forms.v2 ^ p
  u3 := forms.u3 ^ p
  v3 := forms.v3 ^ p
  hM1 := forms.hM1_frobenius
  hM2 := forms.hM2_frobenius
  hM3 := forms.hM3_frobenius
  right1 := by
    have h := congrArg (fun x => x ^ p) forms.right1
    simpa [map_pow, map_inv, mul_pow] using h
  right2 := by
    have h := congrArg (fun x => x ^ p) forms.right2
    simpa [map_pow, map_mul, map_inv, mul_pow] using h
  right3 := by
    have h := congrArg (fun x => x ^ p) forms.right3
    simpa [map_pow, mul_pow] using h

end Step4C5NormalForms

namespace Step4C5NormalForms

/-- BG `w₁ = v₂^{t⁻¹} u₃` from the rearrangement leading to `(C.7)`. -/
noncomputable def w1 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    NormSet.normOneUnits p q :=
  data.tConjNormOneUnitsAut forms.v2 * forms.u3

/-- BG `w₂ = v₃ u₁^{t⁻²}` from the rearrangement leading to `(C.7)`. -/
noncomputable def w2 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    NormSet.normOneUnits p q :=
  forms.v3 * (data.tConjNormOneUnitsAut ^ 2) forms.u1

/-- BG `w₃ = v₁ u₂^t` from the rearrangement leading to `(C.7)`. -/
noncomputable def w3 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    NormSet.normOneUnits p q :=
  forms.v1 * (data.tConjNormOneUnitsAut ^ 1)⁻¹ forms.u2

end Step4C5NormalForms

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC


