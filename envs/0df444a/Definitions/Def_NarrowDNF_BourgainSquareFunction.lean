-- Prove2me | Definitions.Def_NarrowDNF_BourgainSquareFunction
-- name    : NarrowDNF_BourgainSquareFunction
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T08:01:18.101973+00:00
-- url     : https://prove2.me/theorems/99d497dd-58a2-431c-806e-30ee46045a37
-- title:
--   Biased Fourier synthesis and low-degree square functions with random signs
-- statement:
--   On a finite coordinate set $I$, let $\chi_{p,S}$ be the biased product characters. For a coefficient family $(a_S)$, Fourier synthesis is the finite sum $\sum_{S\subseteq I}a_S\chi_{p,S}(x)$.
--
--   For a function $f$, the squared low-degree square function at $x$ is
--   $$\mathcal S_{p,k}(f)(x)=\sum_{|S|\le k}\bigl(\widehat f_p(S)\chi_{p,S}(x)\bigr)^2.$$
--   This is already a sum of squares; no square root is taken in its definition, and the empty Fourier support is included.
--
--   The signed-noise construction introduces a second Boolean cube $y$ at unbiased parameter $1/2$. It applies the tensor-noise operator to $f$ with multipliers $\rho_i=\operatorname{standardBit}(1/2,y_i)/3$, hence $\rho_i\in\{-1/3,1/3\}$. The variables $y$ supply independent signs in later moment arguments, while $x$ remains the input on the original biased cube. These definitions are used to derive dimension-free low-degree estimates from signed-noise contractions and uniform-cube hypercontractivity.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainSquareFunction.lean#L48-L50
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainSquareFunction.lean#L104-L107
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainSquareFunction.lean#L17-L19

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainNoise
import Definitions.Def_NarrowDNF_Fourier

namespace NarrowDNF.BourgainSquareFunction
end NarrowDNF.BourgainSquareFunction


/-!
# Dimension-free low-degree square functions

This file derives the square functions needed in Bourgain's argument from
actual signed-noise contractions and the proved uniform-cube Bonami theorem.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Synthesis in the finite biased orthonormal basis. -/
def synthesis (p : ℝ) (a : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ s, a s * Fourier.character p s x









/-- Signed noise on the original cube, parametrized by a separate unbiased cube. -/
def signedNoise (p : ℝ) (f : (ι → Bool) → ℝ) (y x : ι → Bool) : ℝ :=
  BourgainNoise.tensorNoise p (fun i => Fourier.standardBit (1/2) (y i) / 3) f x











/-- Squared low-degree square function. -/
def squareFunction (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) : ℝ :=
  ∑ s ∈ (Finset.univ.filter fun s => Fourier.degree s ≤ k),
    (Fourier.coefficient p f s * Fourier.character p s x)^2









































end NarrowDNF.BourgainSquareFunction


