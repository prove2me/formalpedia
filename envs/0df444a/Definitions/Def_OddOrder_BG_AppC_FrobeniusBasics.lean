-- Prove2me | Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics
-- name    : OddOrder_BG_AppC_FrobeniusBasics
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:48:38.684195+00:00
-- url     : https://prove2.me/theorems/c581f382-e751-44a0-a9fe-fbd555a962dc
-- title:
--   Bender–Glauberman Appendix C: basic facts about $H=P\rtimes U$ and its prime-field line
-- statement:
--   Elementary $(p,q)$-level facts about the Frobenius group $H=P\rtimes U$ of Bender–Glauberman Appendix C and its prime-field line $P_0$, used throughout the development of Lemmas C.1–C.3. They previously appeared only through Peterfalvi's Section 16 hypothesis but do not depend on that configuration.
--
--   Main definitions: `additiveFrobeniusHom` (the $p$-power Frobenius on the additive kernel of the model $P\rtimes U$), `normOneUnitsFrobeniusHom` (the $p$-power Frobenius on the norm-one complement) and `frobeniusHom` (the induced Frobenius endomorphism of $P\rtimes U$).
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_FrobeniusBasics.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_FrobeniusBasics.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_HypothesisB

namespace OddOrder.BG.AppC

/-- The scalar `1` element is the distinguished prime-line generator. -/
theorem primeLineElement_one (p q : ℕ) [Fact p.Prime] :
    primeLineElement p q 1 = primeLineGenerator p q := by
  simp [primeLineElement, primeLineGenerator]

/-- The distinguished generator lies in the concrete prime-field line `P₀`. -/
theorem primeLineGenerator_mem (p q : ℕ) [Fact p.Prime] :
    primeLineGenerator p q ∈ primeLine p q := by
  dsimp [primeLineGenerator, primeLine, OddOrder.BG.AppC.primeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  exact Submodule.subset_span (by simp)

/-- The distinguished generator of `P₀` is nontrivial. -/
theorem primeLineGenerator_ne_one (p q : ℕ) [Fact p.Prime] :
    primeLineGenerator p q ≠ 1 := by
  intro h
  have hfield : (1 : GaloisField p q) = 0 :=
    ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h)
  exact one_ne_zero hfield

/-- The distinguished generator of `P₀` has order dividing `p`. -/
theorem primeLineGenerator_pow_p (p q : ℕ) [Fact p.Prime] :
    (primeLineGenerator p q) ^ p = 1 := by
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q)
      p]
    exact ZMod.charP p
  dsimp [primeLineGenerator]
  let inlHom :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup p q →*
        NormSet.normOneFrobeniusGroup p q := SemidirectProduct.inl
  rw [← map_pow inlHom, ← map_one inlHom, SemidirectProduct.inl_inj]
  rw [← ofAdd_nsmul]
  congr
  simp

/-- The concrete `p`-power Frobenius on the additive kernel of BG's model
`P ⋊ U`, written multiplicatively via `Multiplicative`. -/
noncomputable def additiveFrobeniusHom (p q : ℕ) [Fact p.Prime] :
    NormSet.additiveFieldGroup p q →* NormSet.additiveFieldGroup p q where
  toFun x := Multiplicative.ofAdd (x.toAdd ^ p)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp [(Fact.out : Nat.Prime p).ne_zero]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact (OddOrder.BG.AppC.NormSet.add_pow_p
      p q x.toAdd y.toAdd).symm

/-- The concrete `p`-power Frobenius on the norm-one complement. -/
noncomputable def normOneUnitsFrobeniusHom (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneUnits p q →* NormSet.normOneUnits p q where
  toFun u := u ^ p
  map_one' := by simp
  map_mul' u v := by
    rw [mul_pow]

/-- The concrete `p`-power Frobenius of BG's semidirect product
`P ⋊ U`: it sends `(x,u)` to `(x^p,u^p)`. -/
noncomputable def frobeniusHom (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneFrobeniusGroup p q →* NormSet.normOneFrobeniusGroup p q :=
  SemidirectProduct.map
    (additiveFrobeniusHom p q)
    (normOneUnitsFrobeniusHom p q)
    (by
      intro u
      ext x
      apply Multiplicative.toAdd.injective
      change (((u : (GaloisField p q)ˣ) :
              GaloisField p q) * x) ^ p =
            (((u ^ p : NormSet.normOneUnits p q) :
                  (GaloisField p q)ˣ) :
                GaloisField p q) * x ^ p
      simpa [map_pow] using
        (mul_pow (((u : (GaloisField p q)ˣ) :
          GaloisField p q)) x p))

@[simp]
theorem frobeniusHom_inl (p q : ℕ) [Fact p.Prime]
    (x : NormSet.additiveFieldGroup p q) :
    frobeniusHom p q (SemidirectProduct.inl x) =
      SemidirectProduct.inl (Multiplicative.ofAdd (x.toAdd ^ p)) := by
  simp [frobeniusHom, additiveFrobeniusHom]

@[simp]
theorem frobeniusHom_inr (p q : ℕ) [Fact p.Prime]
    (u : NormSet.normOneUnits p q) :
    frobeniusHom p q
        (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) =
      SemidirectProduct.inr (u ^ p) := by
  simp [frobeniusHom, normOneUnitsFrobeniusHom]

/-- The concrete Frobenius fixes the prime-field line pointwise. -/
theorem frobeniusHom_primeLineElement (p q : ℕ) [Fact p.Prime] (c : ZMod p) :
    frobeniusHom p q (primeLineElement p q c) = primeLineElement p q c := by
  rw [primeLineElement, frobeniusHom_inl, SemidirectProduct.inl_inj]
  change (algebraMap (ZMod p) (GaloisField p q) c) ^ p =
    algebraMap (ZMod p) (GaloisField p q) c
  rw [← map_pow, ZMod.pow_card]

/-- The concrete Frobenius fixes the distinguished prime-line generator. -/
theorem frobeniusHom_primeLineGenerator (p q : ℕ) [Fact p.Prime] :
    frobeniusHom p q (primeLineGenerator p q) = primeLineGenerator p q := by
  simpa [primeLineElement_one] using frobeniusHom_primeLineElement p q 1

end OddOrder.BG.AppC


