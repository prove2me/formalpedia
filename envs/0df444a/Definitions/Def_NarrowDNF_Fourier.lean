-- Prove2me | Definitions.Def_NarrowDNF_Fourier
-- name    : NarrowDNF_Fourier
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:39.121204+00:00
-- url     : https://prove2.me/theorems/ed2f9b60-2c93-41d4-a7f7-da1cbbdd4a1f
-- title:
--   Normalized biased Walsh characters, Fourier components, and coordinate residuals
-- statement:
--   For $0<p<1$, the normalized centered Bernoulli bit is $\psi_p(b)=(b-p)/\sqrt{p(1-p)}$, with Boolean values read as $0$ and $1$. A support mask $s:I\to\{0,1\}$ selects the tensor character
--   $$\chi_{p,s}(x)=\prod_{i:s_i=1}\psi_p(x_i).$$
--   For $f:\{0,1\}^I\to\mathbb R$ on a finite cube, define $\widehat f_p(s)=\mathbb E_{\mu_p}[f(x)\chi_{p,s}(x)]$ and $\deg(s)=|\{i:s_i=1\}|$. An explicit mask-to-subset equivalence provides the same coefficients and characters indexed by finite coordinate subsets $S$. The component $f_S(x)$ is $\widehat f_p(S)\chi_{p,S}(x)$.
--
--   Conditional coordinate averaging is $M_i f(x)=(1-p)f(x^{i\leftarrow0})+p f(x^{i\leftarrow1})$, and the residual is $f-M_i f$. These are finite-sum definitions underlying the biased Fourier expansion and resampling-influence identities. Orthogonality and expansion properties use their stated bias hypotheses in separate theorem nodes.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L261-L270
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L272-L274
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L276-L278
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L54-L55
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L503-L505
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L57-L59
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L61-L62
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L20-L22
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L152-L154
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L156-L158
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L24-L25

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier


/-!
# Finite biased Fourier expansion

A basis index is a Boolean support mask. Its true coordinates are exactly the
usual subset index. All expectations use Bernoulli product weights, and the
normalization of influence is independent resampling rather than bit flipping.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Fourier

/-- Centered normalized Bernoulli bit. -/
def standardBit (p : ℝ) (b : Bool) : ℝ :=
  (if b then 1-p else -p) / Real.sqrt (p * (1-p))

/-- The two one-coordinate orthonormal functions: constant and centered bit. -/
def bitBasis (p : ℝ) (s b : Bool) : ℝ := if s then standardBit p b else 1







section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tensor basis indexed by the coordinates selected by a Boolean support mask. -/
def character (p : ℝ) (s x : ι → Bool) : ℝ := ∏ i, bitBasis p (s i) (x i)

/-- Fourier coefficient in the real biased orthonormal basis. -/
def coefficient (p : ℝ) (f : (ι → Bool) → ℝ) (s : ι → Bool) : ℝ :=
  ProductMeasure.expectation p (fun x => f x * character p s x)

/-- Spectral degree, equivalently the cardinality of the support subset. -/
def degree (s : ι → Bool) : ℕ := (Finset.univ.filter fun i => s i = true).card













/-- Conditional averaging in one input coordinate. -/
def coordinateMean (p : ℝ) (f : (ι → Bool) → ℝ) (i : ι) (x : ι → Bool) : ℝ :=
  (1-p) * f (Function.update x i false) + p * f (Function.update x i true)

/-- The component removed by conditional averaging in a coordinate. -/
def coordinateResidual (p : ℝ) (f : (ι → Bool) → ℝ) (i : ι) (x : ι → Bool) : ℝ :=
  f x - coordinateMean p f i x
























/-- Explicit equivalence between support masks and the paper's subset indices. -/
def maskEquivFinset : (ι → Bool) ≃ Finset ι where
  toFun s := Finset.univ.filter fun i => s i = true
  invFun S i := decide (i ∈ S)
  left_inv s := by
    funext i
    simp
  right_inv S := by
    ext i
    simp

/-- The same Fourier coefficient indexed by a finite subset. -/
def setCoefficient (p : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  coefficient p f (maskEquivFinset.symm S)

/-- The same basis function indexed by a finite subset. -/
def setCharacter (p : ℝ) (S : Finset ι) (x : ι → Bool) : ℝ :=
  character p (maskEquivFinset.symm S) x






































/-- Generalized Walsh component in the subset-indexed Fourier decomposition. -/
def component (p : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) (x : ι → Bool) : ℝ :=
  setCoefficient p f S * setCharacter p S x















end Cube
end NarrowDNF.Fourier


