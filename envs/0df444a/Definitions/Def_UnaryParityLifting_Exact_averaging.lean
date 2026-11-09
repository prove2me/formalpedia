-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_averaging
-- name    : UnaryParityLifting_Exact_averaging
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:55.286016+00:00
-- url     : https://prove2.me/theorems/45413509-d0b9-401a-83d8-690157873f92
-- title:
--   Uniform gadget-fiber averaging and the exact gadget constants
-- statement:
--   For a Boolean gadget $g:\{0,1\}^m\to\{0,1\}$ and $N$ blocks, write $g^N(X)_i=g(X_i)$. For a prescribed outer assignment $z$, the fiber consists of all $X$ with $g^N(X)=z$. The averaging operator is
--   $$ (A_gf)(z)=\frac{\sum_{X:g^N(X)=z}f(X)}{|(g^N)^{-1}(z)|}. $$
--   Every theorem using this operator assumes $g$ is surjective, so the denominator is positive and the law samples independent uniform gadget preimages. Unequal fiber sizes are retained.
--
--   Set
--   $$M_g=\max_{b\in\{0,1\}}|g^{-1}(b)|,\quad\delta_g=\frac{2}{mM_g},\quad\rho_g=1-\delta_g,\quad c_g=-\log_2(1-\delta_g/2).$$
--   The error function is $2^{-c_gR}$, with no adjustable exponent. For a non-tautological clause $C$, its falsifying bit at a supported coordinate is the complement of its literal polarity, and
--   $$\theta_C=\prod_{i\in\mathrm{vars}(C)}|g^{-1}(\zeta_C(i))|^{-1}.$$
--   The empty product is one. The normalization budget is $T=(mN+2)S$. The finite sup norm is the maximum absolute function value on the cube, computed through a finite maximum of nonnegative reals.
--
--   These definitions supply the quantitative constants and the operator used in the lifting statements. Outside the surjective domain Lean's division and logarithm are total; no theorem invokes those default values.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.8–10, Definitions 3.1–3.2, equation (3.1), equation (3.3), equation (3.6); p.13, normalization budget

import Mathlib
import Definitions.Def_LiftSAParity_IsOneStifling
import Definitions.Def_LiftSAParity_lift
import Definitions.Def_UnaryParityLifting_Exact_certificateSyntax

namespace UnaryParityLifting.Exact

open scoped BigOperators

/-- One gadget fiber, with its actual cardinality; no balance assumption. -/
def gadgetFiber {m : ℕ} (g : (Fin m → Bool) → Bool) (b : Bool) : Finset (Fin m → Bool) :=
  Finset.univ.filter (fun x => g x = b)

def blockMap {m N : ℕ} (g : (Fin m → Bool) → Bool)
    (X : Fin N × Fin m → Bool) : Fin N → Bool := fun i => g (fun j => X (i, j))

def blockFiber {m N : ℕ} (g : (Fin m → Bool) → Bool)
    (z : Fin N → Bool) : Finset (Fin N × Fin m → Bool) :=
  Finset.univ.filter (fun X => blockMap g X = z)

/-- The finite uniform law of Definition 3.1; only used with surjective g. -/
noncomputable def fiberProbability {m : ℕ} (g : (Fin m → Bool) → Bool)
    (b : Bool) (x : Fin m → Bool) : ℝ :=
  if g x = b then ((gadgetFiber g b).card : ℝ)⁻¹ else 0

/-- Definition 3.2, equation (3.1); the fiber is a product of the independent block fibers. -/
noncomputable def average {m N : ℕ} (g : (Fin m → Bool) → Bool)
    (f : (Fin N × Fin m → Bool) → ℝ) (z : Fin N → Bool) : ℝ :=
  (∑ X ∈ blockFiber g z, f X) / ((blockFiber g z).card : ℝ)

/-- Finite maximum of |f|; the cube is nonempty even with zero coordinates. -/
noncomputable def cubeSup {V : Type*} [Fintype V] [DecidableEq V] (f : (V → Bool) → ℝ) : ℝ :=
  let a : NNReal := Finset.univ.sup (fun z => (⟨|f z|, abs_nonneg (f z)⟩ : NNReal))
  (a : ℝ)

/-- Exactly the constants (3.3). -/
def maxFiber {m : ℕ} (g : (Fin m → Bool) → Bool) : ℕ :=
  max (gadgetFiber g false).card (gadgetFiber g true).card

noncomputable def gadgetDelta {m : ℕ} (g : (Fin m → Bool) → Bool) : ℝ :=
  2 / ((m : ℝ) * (maxFiber g : ℝ))

noncomputable def gadgetRho {m : ℕ} (g : (Fin m → Bool) → Bool) : ℝ := 1 - gadgetDelta g

noncomputable def gadgetExponent {m : ℕ} (g : (Fin m → Bool) → Bool) : ℝ :=
  -Real.logb 2 (1 - gadgetDelta g / 2)

noncomputable def errorBound {m : ℕ} (g : (Fin m → Bool) → Bool) (R : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(gadgetExponent g) * (R : ℝ))

/-- The falsifying bit is the complement of a literal's satisfying value. -/
def falsifyingBit {N : ℕ} (C : LiftSAParity.Clause (Fin N)) (i : Fin N) : Bool :=
  !decide ((i, true) ∈ C)

/-- Exact product from (3.6), including theta = 1 for the empty clause. -/
noncomputable def clauseTheta {m N : ℕ} (g : (Fin m → Bool) → Bool)
    (C : LiftSAParity.Clause (Fin N)) : ℝ :=
  ∏ i ∈ LiftSAParity.clauseVars C,
    ((gadgetFiber g (falsifyingBit C i)).card : ℝ)⁻¹

/-- The normalization budget of Section 4, as an integer before coercion to ℝ. -/
def normalizationBudget (m N S : ℕ) : ℕ := (m * N + 2) * S

end UnaryParityLifting.Exact


