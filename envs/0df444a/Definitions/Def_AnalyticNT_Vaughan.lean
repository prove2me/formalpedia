-- Prove2me | Definitions.Def_AnalyticNT_Vaughan
-- name    : AnalyticNT_Vaughan
-- status  : Definition
-- author  : @Patrick
-- created : 2026-09-07T03:55:54.668668+00:00
-- url     : https://prove2.me/theorems/d652addf-fa9e-471b-84d5-b04b97c8941b
-- title:
--   Vaughan truncations and weighted arithmetic sums
-- statement:
--   The four pieces of Vaughan’s identity, complementary Möbius and von Mangoldt truncations, additive characters, and finite weighted sums. The identity and any numerical bounds are separate theorems.
-- source:
--   Vaughan, An elementary method in prime number theory (1980); adapted from Gershon Bialer, https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/ext/analytic_nt/AnalyticNT/Vaughan/Identity.lean, with arbitrary-weight extension.

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license; source and modifications are documented in
third_party/ternary_goldbach/NOTICE and vaughan_provenance.json in the contribution repository.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace AnalyticNT.Vaughan
open scoped ArithmeticFunction

noncomputable def vaughanLow (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ V then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

noncomputable def muTruncated (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

noncomputable def muHigh (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

noncomputable def lambdaHigh (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if V < n then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

noncomputable def vaughanS1 (U : ℕ) : ArithmeticFunction ℝ :=
  muTruncated U * ArithmeticFunction.log

noncomputable def vaughanS2 (U V : ℕ) : ArithmeticFunction ℝ :=
  muTruncated U *
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - lambdaHigh V))

noncomputable def vaughanS3 (U V : ℕ) : ArithmeticFunction ℝ :=
  lambdaHigh V *
    (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))

noncomputable def addChar (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α * n)

noncomputable def expSum (F : ArithmeticFunction ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), (F n : ℂ) * addChar α n

noncomputable def weightedSum (F : ArithmeticFunction ℝ) (s : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ s, (F n : ℂ) * w n

end AnalyticNT.Vaughan


