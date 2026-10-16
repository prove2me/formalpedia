-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
-- name    : OAI_Algebra_Determinantal_RankTransfer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:17:15.721453+00:00
-- url     : https://prove2.me/theorems/35f36a54-259b-4541-9b15-9f8c8ff4ef58
-- title:
--   Generic polar systems, polar families of hypersurfaces, and affine normalization charts
-- statement:
--   This file collects the objects used to pass from generic to concrete polar systems of a polynomial and to work with them in an affine chart.
--
--   **Notation.** Let $\tau$ be a finite set with $m$ elements. Put $\tau_\circ=\{\circ\}\sqcup\tau$ and $\Pi_\tau=\{\star\}\sqcup\tau_\circ=\{\star,\circ\}\sqcup\tau$, a set of $m+2$ indices. For a field $K$, a polynomial $f\in K[y_p : p\in\Pi_\tau]$, a matrix of directions $w=(w_{ip})_{i\in\tau,\,p\in\Pi_\tau}$ and a coefficient vector $l=(l_p)_{p\in\Pi_\tau}$, define the polar derivatives and the linear form
--   $$P^w_i f=\sum_{p\in\Pi_\tau} w_{ip}\,\partial_p f\quad(i\in\tau),\qquad \lambda_l=\sum_{p\in\Pi_\tau} l_p\,y_p .$$
--   Let $S(w,l,f)$ be the $\Pi_\tau\times\Pi_\tau$ matrix of polynomials whose row $\star$ is the gradient $(\partial_p f)_p$, whose row $\circ$ is the constant vector $(l_p)_p$, and whose row $i\in\tau$ is the gradient $(\partial_p P^w_i f)_p$. The *bad polar system* $B(w,l,f)$ is the family indexed by $\Pi_\tau$ with
--   $$B_\star=f,\qquad B_\circ=\lambda_l\cdot\det S(w,l,f),\qquad B_i=P^w_i f\quad(i\in\tau).$$
--
--   1. **Universal bad polar system.** Let $K$ be a field (in the formalization assumed algebraically closed of characteristic $0$), and let $W_{ip}$ ($i\in\tau$, $p\in\Pi_\tau$) and $\Lambda_p$ ($p\in\Pi_\tau$) be independent indeterminates, indexed together by $\tau_\circ\times\Pi_\tau$ ($\Lambda_p$ corresponds to the index $(\circ,p)$). For $f\in K[y_p : p\in\Pi_\tau]$, the universal system is $B(W,\Lambda,f)$: a family of $m+2$ polynomials in the variables $y_p$ with coefficients in the parameter ring $K[W,\Lambda]$, the coefficients of $f$ being regarded as constants. Specializing $W\mapsto w$ and $\Lambda\mapsto l$ gives back $B(w,l,f)$.
--   2. **Polar family of a hypersurface.** For $w\in\mathbb{C}^{\tau\times\Pi_\tau}$ and $f\in\mathbb{C}[y_p : p\in\Pi_\tau]$, the family $H^w(f)$ indexed by $\tau_\circ$ is $H^w(f)_\circ=f$ and $H^w(f)_i=P^w_if$ for $i\in\tau$: the polynomial together with its $m$ polar derivatives, i.e. $m+1$ polynomials in $m+2$ variables.
--   3. **Degree vector.** For $r\in\mathbb{N}$, the vector on $\tau_\circ$ given by $\circ\mapsto r$ and $i\mapsto r-1$ (truncated subtraction); these are the degrees of the members of $H^w(f)$ when $f$ is homogeneous of degree $r$.
--   4. **Row swap.** The permutation of $\Pi_\tau$ that exchanges $\star$ and $\circ$ and fixes every $i\in\tau$. Permuting the rows of $S(w,l,f)$ by it gives the Jacobian-type matrix of $H^w(f)$ whose first row is $l$ and whose other rows are the gradients of $f$ and of the $P^w_if$.
--   5. **Coordinate splitting.** For a finite set $\iota$ put $\iota_\star=\{\star\}\sqcup\iota$. For $l\in\mathbb{C}^{\iota_\star}$ with $l_\star\neq0$, the $\mathbb{C}$-linear automorphism of $\mathbb{C}^{\iota_\star}$
--   $$y\longmapsto\Bigl(\sum_{j\in\iota_\star}l_jy_j,\ (y_i)_{i\in\iota}\Bigr),\qquad\text{with inverse}\qquad z\longmapsto\Bigl(\frac{z_\star-\sum_{i\in\iota}l_iz_i}{l_\star},\ (z_i)_{i\in\iota}\Bigr),$$
--   which replaces the $\star$-coordinate by the value of the linear form $y\mapsto\sum_j l_jy_j$.
--   6. **Insertion.** The continuous linear map $\mathbb{C}^\iota\to\mathbb{C}^{\iota_\star}$, $v\mapsto(0,v)$, which puts $0$ into the $\star$-coordinate.
--   7. **Affine normalization chart.** For a continuous linear automorphism $e$ of $\mathbb{C}^{\iota_\star}$, the map $\mathbb{C}^\iota\to\mathbb{C}^{\iota_\star}$, $z\mapsto e^{-1}(1,z)$. It is an injective parametrization of the affine hyperplane $\{y : e(y)_\star=1\}$; when $e$ is a coordinate splitting as in item 5 (which is automatically continuous), this is the affine chart $\sum_jl_jy_j=1$.
--
--   These objects are used to count the solutions of the polar system $f=P^w_1f=\dots=P^w_mf=0$ of a homogeneous polynomial $f$ in an affine chart. The universal system lets a surjectivity statement for Macaulay matrices, established over the generic parameters, be specialized to concrete values of the directions $w$ and of the linear form $l$; the chart maps turn solutions in projective space into zeros of square polynomial systems on $\mathbb{C}^\iota$.
--
--   **Formalization Note** $\Pi_\tau$ is `PolarVars τ = Option (Option τ)` with $\star$ = `none` and $\circ$ = `some none`; $\tau_\circ$ and $\iota_\star$ are `Option τ` and `Option ι`. The objects are `universalBadPolar` (that is, `badPolarSystem` applied to the indeterminates `X (some i, j)`, `X (none, j)` of `MvPolynomial (Option τ × PolarVars τ) K` and to `map C f`), `hypersurfacePolars`, `hypersurfaceDegrees`, `swapFirstRows`, `coordinateSplit` (a `LinearEquiv`), `optionInsert` (with the simp lemmas `optionInsert_none` and `optionInsert_some`) and `affineNormChart`. The characteristic-zero and algebraic-closedness assumptions are section hypotheses that the construction itself does not use.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RankTransfer.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RankTransfer.lean by skeleton subtraction
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
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters

section Generic
variable {K τ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

noncomputable def universalBadPolar (f : MvPolynomial (PolarVars τ) K) :
    PolarVars τ → MvPolynomial (PolarVars τ) (MvPolynomial P K) :=
  badPolarSystem (fun i j => X (some i,j)) (fun j => X (none,j)) (map C f)

end Generic
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters
open scoped Classical
variable {τ : Type*} [Fintype τ]

noncomputable def hypersurfacePolars (w : τ → PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) : Option τ → MvPolynomial (PolarVars τ) ℂ :=
  Option.elim' f (polarPolynomial w f)

def hypersurfaceDegrees (r : ℕ) : Option τ → ℕ := Option.elim' r (fun _ => r-1)

def swapFirstRows : Equiv.Perm (PolarVars τ) where
  toFun := Option.elim' (some none) (Option.elim' none (fun i => some (some i)))
  invFun := Option.elim' (some none) (Option.elim' none (fun i => some (some i)))
  left_inv := by rintro (_ | (_ | i)) <;> rfl
  right_inv := by rintro (_ | (_ | i)) <;> rfl

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

noncomputable def coordinateSplit (l : Option ι → ℂ) (h : l none ≠ 0) :
    (Option ι → ℂ) ≃ₗ[ℂ] (Option ι → ℂ) where
  toFun y := Option.elim' (∑ j, l j * y j) (fun i => y (some i))
  invFun z := Option.elim' ((z none - ∑ i, l (some i) * z (some i)) / l none)
    (fun i => z (some i))
  left_inv y := by
    funext i
    cases i with
    | none => simp only [Option.elim'_none, Option.elim'_some, Fintype.sum_option]
              field_simp
              ring
    | some i => rfl
  right_inv z := by
    funext i
    cases i with
    | none => simp only [Option.elim'_none, Option.elim'_some, Fintype.sum_option]
              field_simp
              ring
    | some i => rfl
  map_add' y z := by
    funext i
    cases i <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext i
    cases i with
    | none =>
      change (∑ j, l j * (c * y j)) = c * ∑ j, l j * y j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    | some i => rfl

noncomputable def optionInsert : (ι → ℂ) →L[ℂ] (Option ι → ℂ) :=
  ContinuousLinearMap.pi (fun i => match i with
    | none => 0
    | some j => ContinuousLinearMap.proj j)

omit [Fintype ι] in
@[simp] lemma optionInsert_none (v : ι → ℂ) : optionInsert v none = 0 := rfl
omit [Fintype ι] in
@[simp] lemma optionInsert_some (v : ι → ℂ) (i : ι) : optionInsert v (some i) = v i := rfl

noncomputable def affineNormChart
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) : Option ι → ℂ :=
  e.symm (Option.elim' 1 z)

end PermanentBorder.Polar

end OAI


