-- Prove2me | Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
-- name    : OddOrder_BG_AppC_LemmaC3_Step4Capstone
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:25.290744+00:00
-- url     : https://prove2.me/theorems/5399894b-fbc7-49c1-9e9f-128ce129711d
-- title:
--   Bender–Glauberman Appendix C, Lemma C.3 Step 4: relations (C.9), (C.10) and the capstone
-- statement:
--   Formalizes relations (C.9) and (C.10) and the capstone of Step 4 in Bender–Glauberman Appendix C, Lemma C.3 (§3, pp. 148–152). Pushing (C.7) through the $U$-side bookkeeping gives (C.9): either the third normal-form factor $w_3$ is trivial, in which case $w_1w_2^{p-1}=1$ forces $w=1$ and yields (C.10), or the Step 3 intersection is all of $PU$, which is contradictory.
--
--   The one definition is `Step4Capstone`, the capstone statement $s_1=s^{-1}$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_LemmaC3_Step4Capstone.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_NormalForms

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- **BG Appendix C, Lemma C.3 Step 4 capstone `s₁ = s⁻¹`**, as a statement: for
every norm-one unit `a` whose inverse field value `↑a⁻¹` lies in `E` (so that BG's
companion `b = 2 - ↑a⁻¹` is again a norm-one value), the `k = 3` first normal form
of `s · σ(inr ((tConj⁻³)(a⁻¹))) · s⁻²` has central prime-line factor `s⁻¹`.  This is
the remaining mathematical content; it follows from the (C.2)–(C.10) chain and the
kernel/fixed-point-free argument inside `End ⁅Q, P₀⁆`.

We use the **backward** conjugation `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`, so that
`σ(inr ((tConj⁻³)(a⁻¹))) = t⁻³ σ(inr a⁻¹) t³` matches BG's `(a⁻¹)^{t³}` exactly (BG's
right-conjugation convention `x^{t^k} = t⁻ᵏ x tᵏ`).  This makes the BG (C.4) connector
`q`-swap telescoping (`qⱼ = s⁻ʲtʲ ∈ Q`) port directly; the downstream
`normSetE_eq_inv_of_twisted_normOne_step` is `φ`-agnostic (it only needs `φ^p = 1`,
and `((tConj^3)⁻¹)^p = 1`). -/
def Step4Capstone (data : FieldNormalizerData p q G) : Prop :=
  ∀ a : NormSet.normOneUnits p q,
    unitVal a⁻¹ ∈ NormSet.normSetE p q →
      ∃ u₁ v₁ : NormSet.normOneUnits p q,
        data.s *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr u₁) *
          data.sigma (primeLineElement p q (-1 : ZMod p)) *
            data.sigma (SemidirectProduct.inr v₁)

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC


