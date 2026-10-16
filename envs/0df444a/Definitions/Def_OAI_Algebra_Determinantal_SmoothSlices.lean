-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
-- name    : OAI_Algebra_Determinantal_SmoothSlices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:10:48.526067+00:00
-- url     : https://prove2.me/theorems/7097d7ff-3e16-4725-bfa2-2aa7642d88de
-- title:
--   Root families over a parameter set and Macaulay matrices of polynomial systems
-- statement:
--   This module introduces families of root sets over a complex parameter and the Macaulay matrices that certify membership of all forms of a given degree in an ideal. Let $\iota$ be a finite set and $\hat\iota=\iota\sqcup\{\star\}$; for a system $H=(H_i)_{i\in\iota}$ in $\mathbb C[x_j:j\in\hat\iota]$ and $l\in\mathbb C^{\hat\iota}$ write $\ell(y)=\sum_jl_jy_j$ and $\operatorname{Roots}(H,l)=\{y\in\mathbb C^{\hat\iota}: H_i(y)=0\text{ for all }i,\ \ell(y)=1\}$.
--
--   1. **Evaluation of the linear form.** For $l\in\mathbb C^{\hat\iota}$, the $\mathbb C$-linear functional $y\mapsto\ell(y)=\sum_{j\in\hat\iota}l_jy_j$ on $\mathbb C^{\hat\iota}$.
--
--   2. **Families of roots.** Let $t\mapsto H_t=(H_{t,i})_{i\in\iota}$ and $t\mapsto l_t\in\mathbb C^{\hat\iota}$ be families indexed by $t\in\mathbb C$, and let $s\subseteq\mathbb C$. The total space is
--   $$
--   \mathcal Z_s=\bigl\{(t,y)\in s\times\mathbb C^{\hat\iota}:\ H_{t,i}(y)=0\text{ for all }i,\ \ \ell_t(y)=1\bigr\},
--   $$
--   with the projection $(t,y)\mapsto t$ onto $s$. For each $t\in s$, the map $(t,y)\mapsto y$ is a bijection from the fiber over $t$ onto $\operatorname{Roots}(H_t,l_t)$.
--
--   3. **Monomials of a fixed degree.** For a set $\sigma$ and $d\in\mathbb Z$, the set of exponent vectors $m\in\mathbb N^{\sigma}$ (finitely supported) with $\sum_vm_v=d$; it is empty if $d<0$ and finite when $\sigma$ is finite.
--
--   4. **Macaulay matrix.** Let $K$ be a commutative ring, $\sigma$ a finite set of variables, $\iota$ a finite index set, $F_i\in K[x_v:v\in\sigma]$ and $e_i\in\mathbb Z$ for $i\in\iota$, and $D\in\mathbb Z$. The Macaulay matrix in degree $D$ has rows indexed by the exponents $m$ with $|m|=D$, columns indexed by the pairs $(i,t)$ with $i\in\iota$ and $|t|=D-e_i$, and entries
--   $$
--   \mathrm{Mac}_D\bigl[m,(i,t)\bigr]=\text{the coefficient of }x^{m}\text{ in }F_i\,x^{t}.
--   $$
--   The Macaulay combination of a vector $b=(b_{i,t})$ is the polynomial $\sum_{(i,t)}b_{i,t}\,F_i\,x^{t}$.
--
--   When the systems are homogeneous of fixed degrees, depend continuously differentiably on $t$, and are good for every $t\in s$, the projection from the total space is proper and a local homeomorphism, so the number of roots is constant over a connected parameter set. When each $F_i$ is homogeneous of degree $e_i$, the Macaulay matrix is the matrix of $b\mapsto\sum_{(i,t)}b_{i,t}F_ix^{t}$ onto the forms of degree $D$, and it is surjective exactly when every homogeneous polynomial of degree $D$ lies in the ideal $(F_i)_{i\in\iota}$; surjectivity is thus a finite linear-algebra certificate that the system has no nonzero common zero.
--
--   **Formalization Note** The definitions are `CI.linearEval`, `CI.FamilyRoots` (a subtype of `s × (Option ι → ℂ)`), `CI.familyProjection`, `CI.familyFiberEquiv`, `SliceParameters.DegreeIndex` (with the instances `degreeIndex_finite` and `degreeIndex_fintype`), `macaulayMatrix` and `macaulayCombination`; $\hat\iota$ is `Option ι`. Degrees are integers, so a negative degree gives an empty index set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SmoothSlices.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SmoothSlices.lean by skeleton subtraction
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

namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

noncomputable def linearEval (l : Option ι → ℂ) : (Option ι → ℂ) →ₗ[ℂ] ℂ :=
  { toFun := fun y => eval y (linear l)
    map_add' := by intro x y; simp [eval_linear, mul_add, Finset.sum_add_distrib]
    map_smul' := by intro c y; simp [eval_linear, Finset.mul_sum, mul_left_comm, mul_add] }

@[simp] lemma linearEval_apply (l y : Option ι → ℂ) :
    linearEval l y = eval y (linear l) := by
  rfl

abbrev FamilyRoots (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) :=
  {z : s × (Option ι → ℂ) // (∀ i, eval z.2 (H z.1.val i) = 0) ∧
    eval z.2 (linear (l z.1.val)) = 1}

def familyProjection (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) : FamilyRoots H l s → s := fun z => z.val.1

noncomputable def familyFiberEquiv (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) (t : s) :
    (familyProjection H l s ⁻¹' {t}) ≃ Roots (H t.val) (l t.val) where
  toFun z := ⟨z.val.val.2, by
    have ht : z.val.val.1 = t := z.property
    simpa only [← ht] using z.val.property⟩
  invFun y := ⟨⟨(t,y.val),y.property⟩,rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext z.property.symm rfl
  right_inv _ := rfl

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

abbrev DegreeIndex (σ : Type*) (d : ℤ) := {s : σ →₀ ℕ // (s.degree : ℤ) = d}

instance degreeIndex_finite {σ : Type*} [Finite σ] (d : ℤ) : Finite (DegreeIndex σ d) := by
  apply Set.Finite.to_subtype
  apply (Finsupp.finite_of_degree_le d.toNat).subset
  intro s hs
  change s.degree ≤ d.toNat
  rw [← hs]
  simp

noncomputable instance degreeIndex_fintype {σ : Type*} [Finite σ] (d : ℤ) :
    Fintype (DegreeIndex σ d) := Fintype.ofFinite _

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

noncomputable def macaulayMatrix (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ) :
    Matrix (DegreeIndex σ D) (Σ i : ι, DegreeIndex σ (D-e i)) K :=
  fun s t => (F t.1 * monomial t.2.val 1).coeff s.val

noncomputable def macaulayCombination (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) : MvPolynomial σ K :=
  ∑ t, b t • (F t.1 * monomial t.2.val 1)

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

end Surjectivity
end PermanentBorder.SliceParameters

end OAI


