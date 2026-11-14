-- Prove2me | Definitions.Def_NarrowDNF_UniformHypercontractivity
-- name    : NarrowDNF_UniformHypercontractivity
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T08:01:18.962194+00:00
-- url     : https://prove2.me/theorems/3bb41510-ede7-4506-bd86-664106d7ee15
-- title:
--   Finite fourth-moment contraction and tensor-product noise operators
-- statement:
--   For a finite set $\alpha$, weights $w:\alpha\to\mathbb R$, and an operator $T$ on real-valued functions, define the $2$-to-$4$ contraction property by
--   $$\forall f,\quad\sum_x w(x)(Tf(x))^4\le\left(\sum_x w(x)f(x)^2\right)^2.$$
--   No linearity, normalization, or positivity assumption is included in this proposition; later tensorization results supply their stated hypotheses.
--
--   A one-bit kernel acts by $T_Kf(b)=\sum_c w(c)K(b,c)f(c)$. Its product-cube version uses the product kernel $\prod_i w(y_i)K(x_i,y_i)$, and the bundle separately records product weights and coordinate relabeling. Uniform one-bit noise preserves the mean and multiplies the mean-zero difference by $\rho$:
--   $$T_\rho f(b)=\frac{f(0)+f(1)}2+(\rho\ \text{if }b=1,\ \text{else }-\rho)\frac{f(1)-f(0)}2.$$
--   The biased spectral kernel is $K_{p,\rho}(b,c)=1+\rho\psi_p(b)\psi_p(c)$, using the normalized centered Bernoulli bit $\psi_p$. The sharp uniform parameter is explicitly $\sqrt{1/3}$. These objects support the separate finite hypercontractive estimates.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L274-L276
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L326-L327
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L130-L132
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L24-L25
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L163-L164
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L166-L168
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L170-L171
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L173-L178

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier

namespace NarrowDNF.Hypercontractivity
end NarrowDNF.Hypercontractivity


/-!
# Finite L2-to-L4 hypercontractivity and its uniform-cube specialization

The moment formulation avoids fractional powers during tensorization.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Hypercontractivity

attribute [local instance] Classical.decEq

variable {α β : Type*} [Fintype α] [Fintype β]

def Contract24 (w : α → ℝ) (T : (α → ℝ) → α → ℝ) : Prop :=
  ∀ f, (∑ x, w x * (T f x)^4) ≤ (∑ x, w x * (f x)^2)^2







/-- One-bit uniform noise in its mean/difference decomposition. -/
def uniformBitNoise (ρ : ℝ) (f : Bool → ℝ) (b : Bool) : ℝ :=
  (f false + f true) / 2 + (if b then ρ else -ρ) * (f true - f false) / 2





def productWeight {ι : Type*} [Fintype ι] (w : Bool → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, w (x i)

def productOperator {ι : Type*} [Fintype ι] (w : Bool → ℝ)
    (K : Bool → Bool → ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ y : ι → Bool, (∏ i, w (y i) * K (x i) (y i)) * f y

def kernelOperator (w : Bool → ℝ) (K : Bool → Bool → ℝ)
    (f : Bool → ℝ) (b : Bool) : ℝ := ∑ c : Bool, w c * K b c * f c

/-- Relabel the coordinate type, preserving all input bits. -/
def cubeEquiv {ι κ : Type*} (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp











/-- The normalized Bernoulli spectral-noise kernel. -/
def standardKernel (p ρ : ℝ) (b c : Bool) : ℝ :=
  1 + ρ * Fourier.standardBit p b * Fourier.standardBit p c









/-- The sharp uniform parameter, written to simplify its exact square. -/
def sharpRho : ℝ := Real.sqrt (1/3)











end NarrowDNF.Hypercontractivity


