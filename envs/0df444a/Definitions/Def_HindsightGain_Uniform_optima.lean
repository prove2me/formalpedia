-- Prove2me | Definitions.Def_HindsightGain_Uniform_optima
-- name    : HindsightGain_Uniform_optima
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:38.722422+00:00
-- url     : https://prove2.me/theorems/2cb64735-7323-4ce6-88db-4f14f253df76
-- title:
--   Weighted optima, convex bodies and exact retention expectation
-- statement:
--   For a model $(K,A)$, nonnegative weights $a=(a_i)$ and $K=\prod_iK_i$, set
--   $$f_{A,a}(x)=\sum_{|e|=r}\Bigl(\prod_{i\in e}a_i\Bigr)A_e(x_e),\qquad \operatorname{Val}_A(a)=\max_{x\in K}f_{A,a}(x).$$
--   Write $\operatorname{Val}_A=\operatorname{Val}_A(\mathbf1)$ and $\operatorname{Val}_A(S)=\operatorname{Val}_A(\mathbf1_S)$. The coefficient norm is $\|A\|_F=(\sum_e\sum_a(A_e)_a^2)^{1/2}$. The restriction $A_U$ sets coefficients outside $U$ to zero, and $Z_a=\prod_i a_i\operatorname{conv}K_i$.
--   For independent retention inside $U$, define
--   $$\mathbb E\operatorname{Val}_A(U_p)=\sum_{S\subseteq U}p^{|S|}(1-p)^{|U|-|S|}\operatorname{Val}_A(S),\qquad F_A(t)=t^{-r}\mathbb E\operatorname{Val}_A(S_t).$$
--   These constructions keep each interaction once and retain negative optimal values. They provide the common interface for convexification and thinning. Maxima are real suprema of concrete polynomial images; the model assumptions ensure attainment and finiteness. $F_A$ is used only at $t>0$. The formulae extend mechanically to other real weights or parameters, without any theorem using those extensions.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, §2, (7), (9)–(10), pp.12–13; §4.1, (25), (27), pp.19–20

import Mathlib
import Definitions.Def_HindsightGain_Uniform_model

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HindsightGain.Uniform

/-- Each unordered interaction is evaluated in increasing variable order. -/
def interaction {n D r : ℕ} (M : Model n D r) (e : Edge n r)
    (x : Fin n → Vec D) : ℝ :=
  ∑ a : Fin r → Fin D, M.A e a * ∏ j, x (e.val.orderEmbOfFin e.property j) (a j)

def objective {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ)
    (x : Fin n → Vec D) : ℝ :=
  ∑ e : Edge n r, (∏ i ∈ e.val, a i) * interaction M e x

def feasible {n D r : ℕ} (M : Model n D r) : Set (Fin n → Vec D) :=
  {x | ∀ i, x i ∈ M.K i}

/-- Compactness and nonemptiness in Model ensure this is an attained finite maximum. -/
def val {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ) : ℝ :=
  sSup (objective M a '' feasible M)

def fullVal {n D r : ℕ} (M : Model n D r) : ℝ := val M (fun _ => 1)

def setVal {n D r : ℕ} (M : Model n D r) (S : Finset (Fin n)) : ℝ :=
  val M (fun i => if i ∈ S then 1 else 0)

def frobeniusSq {n D r : ℕ} (M : Model n D r) : ℝ :=
  ∑ e : Edge n r, ∑ a : Fin r → Fin D, (M.A e a) ^ 2

def frobenius {n D r : ℕ} (M : Model n D r) : ℝ := Real.sqrt (frobeniusSq M)

def restrict {n D r : ℕ} (M : Model n D r) (U : Finset (Fin n)) : Model n D r :=
  { M with A := fun e a => if e.val ⊆ U then M.A e a else 0 }

/-- Equation (9). Scaling is applied to the convex hull, including at a_i = 0. -/
def convexBody {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ) : Set (Fin n → Vec D) :=
  {y | ∀ i, y i ∈ (fun u : Vec D => a i • u) '' convexHull ℝ (M.K i)}

/-- The exact probability mass of independent retention inside U, including the endpoints. -/
def thinningMass {n : ℕ} (U S : Finset (Fin n)) (p : ℝ) : ℝ :=
  if S ⊆ U then p ^ S.card * (1 - p) ^ (U.card - S.card) else 0

def thinningMean {n D r : ℕ} (M : Model n D r) (U : Finset (Fin n)) (p : ℝ) : ℝ :=
  ∑ S ∈ U.powerset, thinningMass U S p * setVal M S

def retentionMean {n D r : ℕ} (M : Model n D r) (p : ℝ) : ℝ :=
  thinningMean M Finset.univ p

/-- Equation (27), used only for t > 0. -/
def compensated {n D r : ℕ} (M : Model n D r) (t : ℝ) : ℝ :=
  retentionMean M t / t ^ r

end HindsightGain.Uniform


