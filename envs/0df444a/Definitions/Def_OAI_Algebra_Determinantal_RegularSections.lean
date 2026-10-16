-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_RegularSections
-- name    : OAI_Algebra_Determinantal_RegularSections
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:08:46.680481+00:00
-- url     : https://prove2.me/theorems/0575d222-c923-416c-9f7a-fdda5ce05d6d
-- title:
--   Good homogeneous systems, bordered Jacobians and roots on an affine chart
-- statement:
--   This module sets up the counting framework for square homogeneous polynomial systems in projective space. Let $R$ be a commutative ring and $\iota$ a finite set, and put $\hat\iota=\iota\sqcup\{\star\}$. Polynomials live in $R[x_j:j\in\hat\iota]$, so there is one more variable than there are equations. Let $H=(H_i)_{i\in\iota}$ be a system of polynomials and $l\in R^{\hat\iota}$ a coefficient vector.
--
--   1. **Linear form.** $\ell=\sum_{j\in\hat\iota}l_j\,x_j$.
--
--   2. **Normalized system.** The system indexed by $\hat\iota$ consisting of $\ell-1$ at $\star$ and $H_i$ at $i\in\iota$; its common zeros are the zeros of $H$ on the affine chart $\ell=1$.
--
--   3. **Bordered Jacobian.** The $\hat\iota\times\hat\iota$ matrix $J_{H,l}$ of polynomials whose row $\star$ is $(l_j)_{j\in\hat\iota}$ and whose row $i\in\iota$ is $(\partial H_i/\partial x_j)_{j\in\hat\iota}$; it is the Jacobian matrix of the normalized system.
--
--   4. **Bad system and degrees.** The system indexed by $\hat\iota$ consisting of $\ell\cdot\det J_{H,l}$ at $\star$ and $H_i$ at $i$; and, for $e\in\mathbb N^{\iota}$, the degree vector with entry $1+\sum_{i\in\iota}(e_i-1)$ at $\star$ and $e_i$ at $i$, where $e_i-1$ is truncated at $0$. If every $H_i$ is homogeneous of degree $e_i$, the bad system is homogeneous with these degrees.
--
--   5. **Good systems.** Over a field $K$, the pair $(H,l)$ is good if every nonzero $y\in K^{\hat\iota}$ with $H_i(y)=0$ for all $i\in\iota$ satisfies
--   $$
--   \ell(y)\ne0\qquad\text{and}\qquad\det J_{H,l}(y)\ne0,
--   $$
--   where $J_{H,l}(y)$ is the bordered Jacobian evaluated entrywise at $y$. Equivalently, $y=0$ is the only common zero of the bad system.
--
--   6. **Power systems.** Over $\mathbb C$, for $e\in\mathbb N^{\iota}$, the system $H_i=x_i^{e_i}-x_\star^{e_i}$ ($i\in\iota$), together with the coordinate vector $l=\mathbf 1_{\star}$, i.e. $\ell=x_\star$.
--
--   7. **Roots.** Over $\mathbb C$, $\operatorname{Roots}(H,l)=\{y\in\mathbb C^{\hat\iota}: H_i(y)=0\text{ for all }i,\ \ell(y)=1\}$. For the power system, $y\mapsto(y_i)_{i\in\iota}$ is a bijection from $\operatorname{Roots}$ onto $\prod_{i\in\iota}\{z\in\mathbb C: z^{e_i}=1\}$.
--
--   8. **Derivatives of polynomial maps.** For a finite set $\sigma$, $p\in\mathbb C[x_j:j\in\sigma]$ and $x\in\mathbb C^{\sigma}$, the continuous linear functional $v\mapsto\sum_{i\in\sigma}\partial_ip(x)\,v_i$; and for a square system $P=(P_i)_{i\in\sigma}$, the Jacobian matrix $\bigl(\partial_jP_i(x)\bigr)_{i,j\in\sigma}$.
--
--   Goodness says that all projective zeros of $H$ lie off the hyperplane $\ell=0$ and are nondegenerate. For good systems of homogeneous polynomials of degrees $e_i\ge1$ the number of roots on the chart $\ell=1$ equals $\prod_ie_i$; the power system is the good model system, with exactly $\prod_ie_i$ roots by item 7, against which other systems are compared.
--
--   **Formalization Note** Here $\hat\iota$ is `Option ι` with $\star$ = `none`. The definitions are `CI.linear`, `normalized`, `square`, `bad`, `degrees`, `Good`, `powers`, `coordinate` (`Pi.single none 1`), `Roots` (a subtype of `Option ι → ℂ`), `powersRootsEquiv`, `polynomialDerivative` and `jacobian`; `eval_linear`, `eval_coordinate` and `polynomialDerivative_apply` are evaluation formulas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RegularSections.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RegularSections.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts

namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

noncomputable def linear (l : Option ι → R) : MvPolynomial (Option ι) R :=
  ∑ j, C (l j) * X j

noncomputable def normalized (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Option ι → MvPolynomial (Option ι) R := Option.elim' (linear l - 1) H

noncomputable def square (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Matrix (Option ι) (Option ι) (MvPolynomial (Option ι) R) :=
  fun i j => match i with | none => C (l j) | some k => pderiv j (H k)

noncomputable def bad (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Option ι → MvPolynomial (Option ι) R := Option.elim' (linear l * (square H l).det) H

def degrees (e : ι → ℕ) : Option ι → ℕ := Option.elim' (1 + ∑ i, (e i - 1)) e

lemma eval_linear (l y : Option ι → R) : eval y (linear l) = ∑ j, l j * y j := by
  simp [linear]

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

def Good (H : ι → MvPolynomial (Option ι) K) (l : Option ι → K) : Prop :=
  ∀ y : Option ι → K, y ≠ 0 → (∀ i, eval y (H i) = 0) →
    eval y (linear l) ≠ 0 ∧ (square H l |>.map (eval y)).det ≠ 0

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

noncomputable def powers (e : ι → ℕ) : ι → MvPolynomial (Option ι) ℂ :=
  fun i => X (some i) ^ e i - X none ^ e i
noncomputable def coordinate : Option ι → ℂ := Pi.single none 1

lemma eval_coordinate (y : Option ι → ℂ) : eval y (linear (coordinate (ι := ι))) = y none := by
  simp [linear, coordinate, Pi.single_apply]

def Roots (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ) :=
  {y : Option ι → ℂ // (∀ i, eval y (H i) = 0) ∧ eval y (linear l) = 1}

noncomputable def powersRootsEquiv (e : ι → ℕ) :
    Roots (powers e) coordinate ≃ (∀ i, {z : ℂ // z ^ e i = 1}) where
  toFun y i := ⟨y.val (some i), by
    have h0 : y.val none = 1 := by simpa only [eval_coordinate] using y.property.2
    simpa [powers, h0, sub_eq_zero] using y.property.1 i⟩
  invFun z := ⟨Option.elim' 1 (fun i => (z i).val), by
    constructor
    · intro i
      simp [powers, (z i).property]
    · simp only [eval_coordinate, Option.elim'_none]⟩
  left_inv y := by
    apply Subtype.ext
    funext j
    cases j with
    | none =>
      have h0 : y.val none = 1 := by simpa only [eval_coordinate] using y.property.2
      exact h0.symm
    | some i => rfl
  right_inv z := by funext i; rfl

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

noncomputable def polynomialDerivative (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    (σ → ℂ) →L[ℂ] ℂ :=
  ∑ i, MvPolynomial.eval x (pderiv i p) • ContinuousLinearMap.proj i

@[simp] lemma polynomialDerivative_apply (p : MvPolynomial σ ℂ) (x v : σ → ℂ) :
    polynomialDerivative p x v = ∑ i, MvPolynomial.eval x (pderiv i p) * v i := by
  classical
  simp [polynomialDerivative]

noncomputable def jacobian (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ) : Matrix σ σ ℂ :=
  fun i j => eval x (pderiv j (P i))

end
end PermanentBorder.CI

namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open Topology Set

end PermanentBorder.Polar

end OAI


