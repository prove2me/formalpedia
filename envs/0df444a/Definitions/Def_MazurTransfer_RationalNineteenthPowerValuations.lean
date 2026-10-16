-- Prove2me | Definitions.Def_MazurTransfer_RationalNineteenthPowerValuations
-- name    : MazurTransfer_RationalNineteenthPowerValuations
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-16T05:29:45.418386+00:00
-- url     : https://prove2.me/theorems/44009ba8-6540-4e35-b9e1-ccaf98de32a9
-- title:
--   Rational nineteenth-power classes and prime valuation coordinates
-- statement:
--   Let $C=\mathbb Q^\times/(\mathbb Q^\times)^{19}$. For each prime $q$, let $\bar v_q:C\to\mathbb F_{19}$ be the ordinary $q$-adic valuation reduced modulo $19$. Set
--
--   $$C_{13}=\bigcap_{q\text{ prime},\ q\ne13}\ker(\bar v_q).$$
--
--
--   This interface defines the quotient, its canonical $\mathbb F_{19}$ vector-space structure, and its prime valuation coordinates; it does not assert a dimension bound.
-- source:
--   Derived arithmetic lemma for the MazurTorsion order-13 descent. Primary arithmetic sources: Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/Data/Nat/Factorization/Defs.lean, Nat.prod_factorization_pow_eq_self and Nat.factorization_def (https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Factorization/Defs.lean); Mathlib/NumberTheory/Padics/PadicVal/Basic.lean, padicValRat_def and padicValRat.mul (https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean). The dimension statement is the derived one-prime power-class bound proved here.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0. Design boundary: publish the checked rational nineteenth-power quotient and valuation interface. Named downstream consumer: the actual selected pi Selmer dimension bound. -/
import Mathlib

noncomputable section
namespace MazurTransfer.RationalNineteenthPowerClasses

abbrev PowerClasses := ℚˣ ⧸ (powMonoidHom 19 : ℚˣ →* ℚˣ).range

def classOf : ℚˣ →* PowerClasses := QuotientGroup.mk' _

theorem classOf_eq_iff_power_ratio (a d : ℚˣ) :
    classOf a = classOf d ↔ ∃ b : ℚˣ, b ^ 19 = a / d :=
  QuotientGroup.eq_iff_div_mem

theorem classOf_eq_one_iff (a : ℚˣ) : classOf a = 1 ↔ ∃ b : ℚˣ, b ^ 19 = a :=
  QuotientGroup.eq_one_iff a

theorem pow_nineteen (x : PowerClasses) : x ^ 19 = 1 := by
  refine Quotient.inductionOn x ?_
  intro a
  change (QuotientGroup.mk a : PowerClasses) ^ 19 = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨a, rfl⟩

def powerClassesZModModule : Module (ZMod 19) (Additive PowerClasses) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    exact pow_nineteen x.toMul)

end MazurTransfer.RationalNineteenthPowerClasses
end

noncomputable section
namespace MazurTransfer.RationalNineteenthPowerValuations
open RationalNineteenthPowerClasses
local instance : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

def unitValuationHom (p : ℕ) (hp : p.Prime) : ℚˣ →* Multiplicative (ZMod 19) :=
  letI : Fact p.Prime := ⟨hp⟩
  { toFun := fun a => Multiplicative.ofAdd ((padicValRat p (a : ℚ) : ℤ) : ZMod 19)
    map_one' := by
      apply Multiplicative.toAdd.injective
      change ((padicValRat p 1 : ℤ) : ZMod 19) = 0
      simp
    map_mul' := by
      intro a b
      apply Multiplicative.toAdd.injective
      change ((padicValRat p ((a * b : ℚˣ) : ℚ) : ℤ) : ZMod 19) =
        ((padicValRat p (a : ℚ) : ℤ) : ZMod 19) + ((padicValRat p (b : ℚ) : ℤ) : ZMod 19)
      rw [Units.val_mul, padicValRat.mul (Units.ne_zero a) (Units.ne_zero b), Int.cast_add] }

theorem unitValuation_nineteenth_power (p : ℕ) (hp : p.Prime) (a : ℚˣ) :
    unitValuationHom p hp (a ^ 19) = 1 := by
  rw [map_pow]
  apply Multiplicative.toAdd.injective
  change (19 : ℕ) • (unitValuationHom p hp a).toAdd = 0
  rw [nsmul_eq_mul]
  change (19 : ZMod 19) * (unitValuationHom p hp a).toAdd = 0
  rw [show (19 : ZMod 19) = 0 by decide, zero_mul]

theorem nineteenth_powers_le_valuation_kernel (p : ℕ) (hp : p.Prime) :
    (powMonoidHom 19 : ℚˣ →* ℚˣ).range ≤ (unitValuationHom p hp).ker := by
  intro x hx
  obtain ⟨a, ha⟩ := hx
  apply MonoidHom.mem_ker.mpr
  rw [← ha]
  exact unitValuation_nineteenth_power p hp a

def valuationClassHom (p : ℕ) (hp : p.Prime) : PowerClasses →* Multiplicative (ZMod 19) :=
  QuotientGroup.lift (powMonoidHom 19 : ℚˣ →* ℚˣ).range (unitValuationHom p hp)
    (nineteenth_powers_le_valuation_kernel p hp)

def valuationLinearMap (p : ℕ) (hp : p.Prime) : Additive PowerClasses →ₗ[ZMod 19] ZMod 19 :=
  (valuationClassHom p hp).toAdditiveLeft.toZModLinearMap 19

theorem valuationLinearMap_classOf (p : ℕ) (hp : p.Prime) (a : ℚˣ) :
    valuationLinearMap p hp (Additive.ofMul (classOf a)) = ((padicValRat p (a : ℚ) : ℤ) : ZMod 19) := rfl

end MazurTransfer.RationalNineteenthPowerValuations
end

noncomputable section
namespace MazurTransfer.RationalThirteenPowerClassBound
open RationalNineteenthPowerClasses RationalNineteenthPowerValuations
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

def thirteenSupport : Submodule (ZMod 19) (Additive PowerClasses) :=
  ⨅ (q : ℕ) (hq : q.Prime) (_ : q ≠ 13), (valuationLinearMap q hq).ker

theorem mem_thirteenSupport (x : Additive PowerClasses) :
    x ∈ thirteenSupport ↔ ∀ (q : ℕ) (hq : q.Prime), q ≠ 13 → valuationLinearMap q hq x = 0 := by
  simp only [thirteenSupport, Submodule.mem_iInf, LinearMap.mem_ker]

def thirteenCoordinate : thirteenSupport →ₗ[ZMod 19] ZMod 19 :=
  (valuationLinearMap 13 (by decide)).comp thirteenSupport.subtype

end MazurTransfer.RationalThirteenPowerClassBound
end

#print axioms MazurTransfer.RationalNineteenthPowerValuations.valuationClassHom


