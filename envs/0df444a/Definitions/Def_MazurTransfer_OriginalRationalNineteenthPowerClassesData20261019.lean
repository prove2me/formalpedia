-- Prove2me | Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerClassesData20261019
-- name    : MazurTransfer_OriginalRationalNineteenthPowerClassesData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T20:03:33.068502+00:00
-- url     : https://prove2.me/theorems/abd53ba5-6302-4070-acf1-75407603022e
-- title:
--   Original rational nineteenth-power quotient and F19 module
-- statement:
--   Retain the original quotient of rational units by nineteenth powers, its class map and its induced F19 module. The intrinsic exponent certificate is needed to construct that module. Four complete original types, three whole constructor values and two generated structural proof types are checked independently. Named downstream consumer: rational power-class valuation coordinates and the original selected pi Selmer radicand map.
-- source:
--   MazurTheorem RationalNineteenthPowerClasses by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original quotient of nonzero rationals by nineteenth powers, its quotient map and induced F19 module. The intrinsic exponent certificate is retained to define that same module. Equality and prime-support arithmetic are separate theorem interfaces.
Named downstream consumer: the original rational prime valuation maps, thirteen-supported power classes and actual pi Selmer radicand injection.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the genuine multiplicative quotient of nonzero rationals
by nineteenth powers, with its induced F19 module and exact equality
criterion. No restriction on rational prime support is asserted.
Named downstream consumer: the canonical rational radicand map from the
actual selected pi Selmer subspace.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.RationalNineteenthPowerClasses

abbrev PowerClasses := ℚˣ ⧸ (powMonoidHom 19 : ℚˣ →* ℚˣ).range

def classOf : ℚˣ →* PowerClasses := QuotientGroup.mk' _





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
#print axioms MazurTransfer.RationalNineteenthPowerClasses.PowerClasses
#print axioms MazurTransfer.RationalNineteenthPowerClasses.classOf
#print axioms MazurTransfer.RationalNineteenthPowerClasses.pow_nineteen
#print axioms MazurTransfer.RationalNineteenthPowerClasses.powerClassesZModModule


