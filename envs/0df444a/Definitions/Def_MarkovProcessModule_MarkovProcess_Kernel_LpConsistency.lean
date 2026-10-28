-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_LpConsistency
-- name    : MarkovProcessModule_MarkovProcess_Kernel_LpConsistency
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:53:20.65191+00:00
-- url     : https://prove2.me/theorems/38802c0b-3e68-4b3c-9cb4-afd862c06d0a
-- title:
--   MarkovProcess.Kernel.LpConsistency
-- statement:
--   # Cross-exponent consistency of kernel integral operators
--
--   The finite- and infinite-exponent operators are packages of the same raw
--   kernel integral.  Consequently their representatives agree almost everywhere
--   whenever their inputs do, even when the inputs and outputs inhabit different
--   `Lp` types.
--
--   Complete pinned Lean module MarkovProcess.Kernel.LpConsistency by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/LpConsistency.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_Lp

/-!
# Cross-exponent consistency of kernel integral operators

The finite- and infinite-exponent operators are packages of the same raw
kernel integral.  Consequently their representatives agree almost everywhere
whenever their inputs do, even when the inputs and outputs inhabit different
`Lp` types.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- Finite-exponent kernel operators at possibly different exponents have
almost-everywhere equal representatives on almost-everywhere equal inputs. -/
theorem kernelLpFinite_consistent
    (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (p q : NNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp ℝ (p : ℝ≥0∞) μ) (g : Lp ℝ (q : ℝ≥0∞) μ)
    (hfg : f =ᵐ[μ] g) :
    kernelLpFinite μ κ hκ hκμ p f =ᵐ[μ]
      kernelLpFinite μ κ hκ hκμ q g := by
  exact (coeFn_kernelLpFinite μ κ hκ hκμ p f).trans
    ((kernelIntegral_congr_ae hκμ hfg).trans
      (coeFn_kernelLpFinite μ κ hκ hκμ q g).symm)

/-- The finite-exponent and infinite-exponent packages have almost-everywhere
equal representatives on almost-everywhere equal inputs. -/
theorem kernelLpFinite_consistent_top
    (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal) [Fact (1 ≤ p)]
    (f : Lp ℝ (p : ℝ≥0∞) μ) (g : Lp ℝ ∞ μ)
    (hfg : f =ᵐ[μ] g) :
    kernelLpFinite μ κ hκ hκμ p f =ᵐ[μ]
      kernelLpTop μ κ hκ hκμ g := by
  exact (coeFn_kernelLpFinite μ κ hκ hκμ p f).trans
    ((kernelIntegral_congr_ae hκμ hfg).trans
      (coeFn_kernelLpTop μ κ hκ hκμ g).symm)

/-- Symmetric orientation of `kernelLpFinite_consistent_top`. -/
theorem kernelLpTop_consistent_finite
    (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal) [Fact (1 ≤ p)]
    (f : Lp ℝ ∞ μ) (g : Lp ℝ (p : ℝ≥0∞) μ)
    (hfg : f =ᵐ[μ] g) :
    kernelLpTop μ κ hκ hκμ f =ᵐ[μ]
      kernelLpFinite μ κ hκ hκμ p g := by
  exact (coeFn_kernelLpTop μ κ hκ hκμ f).trans
    ((kernelIntegral_congr_ae hκμ hfg).trans
      (coeFn_kernelLpFinite μ κ hκ hκμ p g).symm)

end MarkovProcess


