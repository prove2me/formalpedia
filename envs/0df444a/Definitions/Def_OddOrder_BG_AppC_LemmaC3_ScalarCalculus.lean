-- Prove2me | Definitions.Def_OddOrder_BG_AppC_LemmaC3_ScalarCalculus
-- name    : OddOrder_BG_AppC_LemmaC3_ScalarCalculus
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:22:06.683197+00:00
-- url     : https://prove2.me/theorems/0d2fd385-6c28-4191-9f51-66ead525bb27
-- title:
--   Bender–Glauberman Appendix C, Lemma C.3 Step 4: the scalar calculus and the words $M_1,M_2,M_3$
-- statement:
--   Sets up the scalar calculus of Step 4 of Bender–Glauberman Appendix C, Lemma C.3 (§3, pp. 148–152). BG writes the prime-field line multiplicatively as $s^x:=\sigma(\mathrm{inl}(x))$ for a scalar $x\in\mathbb{F}_{p^q}$, so that $s^xs^y=s^{x+y}$, and conjugating by $\sigma(\mathrm{inr}\,a)$ for $a\in U$ scales the exponent. The file runs this calculus through the first relations of Step 4.
--
--   Main definitions: `sScalar` (the line element $s^x$), `unitVal` (the field value of a norm-one unit), and the three words `step4M1`, `step4M2`, `step4M3` (the factors $M_1,M_2,M_3$ of relation (C.5)).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_LemmaC3_ScalarCalculus.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- BG Appendix C prime-field-line scalar `s^x`: the additive-line element
`σ(inl(ofAdd x))` for a field scalar `x ∈ 𝔽_{p^q}`.  The distinguished generator is
`s = s^1`, and `s^x · s^y = s^{x+y}`. -/
noncomputable def sScalar (data : FieldNormalizerData p q G)
    (x : GaloisField p q) : G :=
  data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd x))

/-- The field value `↑a ∈ 𝔽_{p^q}` of a norm-one unit `a ∈ U`. -/
def unitVal (a : NormSet.normOneUnits p q) :
    GaloisField p q :=
  ((a : (GaloisField p q)ˣ) : GaloisField p q)

/-- **Backward conjugation rewrite**: `(t^n)⁻¹ · σ(inr u) · t^n = σ(inr ((tConj^n)⁻¹ u))`.
This is the inverse-direction companion of
`t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow` (S16), giving BG's
right-conjugation `(u)^{t^n} = t⁻ⁿ u tⁿ` directly.  It lets the BG (C.4) connector
`q`-swap telescoping be carried out on the backward `tConj⁻³` form of `M₁`. -/
theorem t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    (data : FieldNormalizerData p q G)
    (n : ℕ) (u : NormSet.normOneUnits p q) :
    (data.t ^ n)⁻¹ *
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.t ^ n =
      data.sigma
        (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) :
          NormSet.normOneFrobeniusGroup p q) := by
  have hself : (data.tConjNormOneUnitsAut ^ n) ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) = u := by
    simp
  have h := data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow n
    ((data.tConjNormOneUnitsAut ^ n)⁻¹ u)
  rw [hself] at h
  rw [← h]; group

/-- BG Appendix C `(C.8)` normal-form transport in neutral form: applying the
concrete `p`-power Frobenius to a `(C.5)` equation keeps the prime-line factor
fixed and raises the three complement terms to their `p`-th powers. -/
theorem frobenius_step4_sigma_inr_decomposition
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w u v : NormSet.normOneUnits p q) (c : ZMod p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v : NormSet.normOneFrobeniusGroup p q)) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ p) :
            NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr (u ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr (v ^ p) :
            NormSet.normOneFrobeniusGroup p q) := by
  let g := primeLineGenerator p q
  let W : NormSet.normOneFrobeniusGroup p q := SemidirectProduct.inr w
  let U : NormSet.normOneFrobeniusGroup p q := SemidirectProduct.inr u
  let V : NormSet.normOneFrobeniusGroup p q := SemidirectProduct.inr v
  let S : NormSet.normOneFrobeniusGroup p q := primeLineElement p q c
  have hleft_sigma :
      data.sigma (g ^ m * W * g ^ r) =
        data.s ^ m * data.sigma W * data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_sigma :
      data.sigma (U * S * V) = data.sigma U * data.sigma S * data.sigma V := by
    rw [map_mul, map_mul]
  have hH : g ^ m * W * g ^ r = U * S * V := by
    apply data.sigma_injective
    calc
      data.sigma (g ^ m * W * g ^ r) =
          data.s ^ m * data.sigma W * data.s ^ r := hleft_sigma
      _ = data.sigma U * data.sigma S * data.sigma V := hdec
      _ = data.sigma (U * S * V) := hright_sigma.symm
  have hpowH := congrArg (frobeniusHom p q) hH
  have hpowH' :
      g ^ m * (SemidirectProduct.inr (w ^ p) : NormSet.normOneFrobeniusGroup p q) *
          g ^ r =
        (SemidirectProduct.inr (u ^ p) : NormSet.normOneFrobeniusGroup p q) *
          primeLineElement p q c *
            (SemidirectProduct.inr (v ^ p) : NormSet.normOneFrobeniusGroup p q) := by
    simpa [W, U, V, S, g, map_mul, map_pow,
      frobeniusHom_primeLineGenerator,
      frobeniusHom_inr,
      frobeniusHom_primeLineElement] using hpowH
  have hleft_pow_sigma :
      data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ p) : NormSet.normOneFrobeniusGroup p q) *
              g ^ r) =
        data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ p) :
            NormSet.normOneFrobeniusGroup p q) *
            data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_pow_sigma :
      data.sigma
          ((SemidirectProduct.inr (u ^ p) : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c *
              (SemidirectProduct.inr (v ^ p) : NormSet.normOneFrobeniusGroup p q)) =
        data.sigma (SemidirectProduct.inr (u ^ p) : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q c) *
            data.sigma (SemidirectProduct.inr (v ^ p) :
              NormSet.normOneFrobeniusGroup p q) := by
    rw [map_mul, map_mul]
  calc
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ p) :
            NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
        data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ p) : NormSet.normOneFrobeniusGroup p q) *
              g ^ r) := hleft_pow_sigma.symm
    _ = data.sigma
          ((SemidirectProduct.inr (u ^ p) : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c *
              (SemidirectProduct.inr (v ^ p) :
                NormSet.normOneFrobeniusGroup p q)) := by
      rw [hpowH']
    _ = data.sigma (SemidirectProduct.inr (u ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr (v ^ p) :
            NormSet.normOneFrobeniusGroup p q) := hright_pow_sigma

/-- BG Appendix C, Lemma C.3 Step 4 first `(C.5)` factor
`M₁ = s · (a⁻¹)^{t^3} · s⁻²`, in BG's backward conjugation convention. -/
noncomputable def step4M1 (data : FieldNormalizerData p q G)
    (a : NormSet.normOneUnits p q) : G :=
  data.s *
      ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
    (data.s⁻¹) ^ 2

/-- BG Appendix C, Lemma C.3 Step 4 second `(C.5)` factor
`M₂ = s³ · (ab⁻¹)^{t^2} · s⁻¹`. -/
noncomputable def step4M2 (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) : G :=
  data.s ^ 3 *
      ((data.t⁻¹) ^ 2 *
        (data.sigma (SemidirectProduct.inr a) *
          (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
    data.s⁻¹

/-- BG Appendix C, Lemma C.3 Step 4 third `(C.5)` factor
`M₃ = s² · b^t · s⁻³`. -/
noncomputable def step4M3 (data : FieldNormalizerData p q G)
    (b : NormSet.normOneUnits p q) : G :=
  data.s ^ 2 *
      (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
    (data.s⁻¹) ^ 3

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC


