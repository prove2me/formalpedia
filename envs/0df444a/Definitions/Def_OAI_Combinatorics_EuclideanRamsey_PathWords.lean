-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
-- name    : OAI_Combinatorics_EuclideanRamsey_PathWords
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:36:22.143997+00:00
-- url     : https://prove2.me/theorems/d223d03b-7eaf-4824-8575-12249aeaeae1
-- title:
--   Unit words, weighted paths and string families built from scaled congruent copies of a configuration
-- statement:
--   Throughout, $E_\infty$ denotes the real vector space of finitely supported real sequences $x=(x_0,x_1,x_2,\dots)$ with inner product $\langle x,y\rangle=\sum_n x_ny_n$ and norm $\|x\|=\langle x,x\rangle^{1/2}$; it contains an isometric copy of every $\mathbb{R}^d$. Let $\Gamma=F(E_\infty)$ be the free group whose generators $[z]$ are the points $z\in E_\infty$ (the *letter group*), and fix a configuration $a=(a_i)_{i\in\iota}$ of points of $E_\infty$. Tuples $w\in\Gamma^\iota$ are multiplied coordinatewise. A point family $b=(b_i)_{i\in\iota}$ is a *congruent copy* of $a$ if $\|b_i-b_j\|=\|a_i-a_j\|$ for all $i,j$.
--
--   1. **Unit words.** $\mathrm{UW}_a(w,n)$, for $w\in\Gamma^\iota$ and $n\in\mathbb{N}$, is the smallest relation such that every constant tuple $(g)_{i\in\iota}$ with $g\in\Gamma$ satisfies $\mathrm{UW}_a((g)_i,0)$; for every congruent copy $b$ of $a$ the letter tuple satisfies $\mathrm{UW}_a(([b_i])_i,1)$; and $\mathrm{UW}_a(u,m)$, $\mathrm{UW}_a(v,n)$ imply $\mathrm{UW}_a(uv,m+n)$. The degree $n$ counts the copy letters used.
--   2. **Unit words as a graded path system.** A *graded path system* on $\Gamma^\iota$ is a relation $\mathrm{Holds}(w,n)$ that contains every constant tuple in degree $0$ and is closed under products with degrees adding; its *monoid* is $\{w:\ \mathrm{Holds}(w,n)\text{ for some }n\}\le\Gamma^\iota$. The unit words form such a system.
--   3. **Copies of weight $u$.** For $u\in\mathbb{R}$, a family $b$ is a *copy of $a$ of weight $u$* if $u\ge 0$ and
--   $$\|b_i-b_j\|^2=u\,\|a_i-a_j\|^2\qquad\text{for all } i,j\in\iota,$$
--   that is, $b$ is congruent to $a$ scaled by the factor $\sqrt u$.
--   4. **Weighted paths.** $\mathrm{Path}_a(w,\lambda)$, with $\lambda\in\mathbb{R}$, is the smallest relation containing all constant tuples with weight $0$ and all letter tuples $([b_i])_i$ of copies $b$ of weight $u$ with weight $u$, and closed under products with weights adding.
--   5. **Pair groups.** For $i\ne j$ let $\Pi_{ij}\le\Gamma\times\Gamma$ be the image of the unit-word monoid under $w\mapsto(w_i,w_j)$; it is closed under inverses, hence a subgroup, and it contains the diagonal $\{(g,g):g\in\Gamma\}$. Its left slice $\{g\in\Gamma:\ (g,1)\in\Pi_{ij}\}$ is a normal subgroup of $\Gamma$. Two auxiliary facts are recorded: any two points $z,z'$ with $\|z'-z\|=\|a_j-a_i\|$ extend to a congruent copy $b$ of $a$ with $b_i=z$, $b_j=z'$; and for $i\ne j$ every unit word $u$ admits a unit word $v$ with $u_iv_i=u_jv_j=1$.
--   6. **Strings, energy and string families.** Let $\mathcal S$ be the free monoid of finite strings of points of $E_\infty$. For strings $x=(x_1,\dots,x_p)$ and $y=(y_1,\dots,y_q)$ the energy is
--   $$\mathcal E(x,y)=\sum_{t=1}^{\min(p,q)}\|x_t-y_t\|^2,$$
--   so $\mathcal E(x,x)=0$. A family $(x_i)_{i\in\iota}$ of strings is a *string family of weight $u$* if all $x_i$ have the same length and $\mathcal E(x_i,x_j)=u\,\|a_i-a_j\|^2$ for all $i,j$.
--
--   Paths in the free group are the combinatorial certificates behind the sufficiency direction of the Euclidean Ramsey classification. A string family of weight $1$ becomes a congruent copy of $a$ once the letters of each string are placed in mutually orthogonal blocks of coordinates of $E_\infty$, and the pair groups are where the augmentation kernel of $\Gamma$ is shown to be covered by unit words.
--
--   **Formalization Note** `FiniteEuclidean` is `ℕ →₀ ℝ` with its $\ell^2$ inner product, `LetterGroup` is `FreeGroup FiniteEuclidean`, and `Strings` is `FreeMonoid FiniteEuclidean`. `UnitWords`, `Path` are inductive predicates, `unitGraded` packages `UnitWords` as a `GradedPaths` structure, and `CopyPath a u b` is item 3. `pairHom`, `pairGroup`, `pairLeft` (with instance `pairLeft_normal`) take a proof of `i ≠ j`; `extend_pair_E`, `unit_pair_inverse` and `pairGroup_diag` are the auxiliary lemmas. `stringEnergy` is defined by recursion on lists and stops at the shorter list.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamsey mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions

namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

namespace EuclideanRamsey
open scoped BigOperators
abbrev LetterGroup := FreeGroup FiniteEuclidean
variable {ι : Type uIndex}

inductive UnitWords (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℕ → Prop
  | diag (g : LetterGroup) : UnitWords a (fun _ => g) 0
  | copy (b : ι → FiniteEuclidean) (h : ∀ i j,‖b i-b j‖=‖a i-a j‖) :
      UnitWords a (fun i => FreeGroup.of (b i)) 1
  | mul {u v m n} : UnitWords a u m → UnitWords a v n → UnitWords a (u*v) (m+n)
def unitGraded (a : ι → FiniteEuclidean) : GradedPaths ι LetterGroup where
  Holds := UnitWords a
  diag := .diag
  mul := .mul

def CopyPath (a : ι → FiniteEuclidean) (u : ℝ) (b : ι → FiniteEuclidean) : Prop :=
  0≤u ∧ ∀ i j,‖b i-b j‖^2=u*‖a i-a j‖^2

inductive Path (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℝ → Prop
  | diag (g : LetterGroup) : Path a (fun _ => g) 0
  | copy {u : ℝ} (b : ι → FiniteEuclidean) (h : CopyPath a u b) :
      Path a (fun i => FreeGroup.of (b i)) u
  | mul {u v lmb μ} : Path a u lmb → Path a v μ → Path a (u*v) (lmb+μ)
lemma extend_pair_E (a : ι → FiniteEuclidean) (i j : ι) (z z' : FiniteEuclidean)
    (h : ‖z'-z‖=‖a j-a i‖) :
    ∃ b : ι → FiniteEuclidean,b i=z ∧ b j=z' ∧ ∀ k l,‖b k-b l‖=‖a k-a l‖ := by
  let v := a j-a i
  let w := z'-z
  let R := (ℝ ∙ (v-w))ᗮ.reflection
  refine ⟨fun k => z+R (a k-a i),by simp,?_,?_⟩
  · have he : R v=w := Submodule.reflection_sub h.symm
    simpa [v,w] using congrArg (fun t => z+t) he
  · intro k l
    simp only [add_sub_add_left_eq_sub,← map_sub,sub_sub_sub_cancel_right,
      LinearIsometryEquiv.norm_map]

lemma unit_pair_inverse (a : ι → FiniteEuclidean) : PairInverse (unitGraded a).monoid := by
  intro i j _ u hu
  obtain ⟨m,hm⟩ := hu
  change UnitWords a u m at hm
  suffices ∃ v n,UnitWords a v n ∧ v i=(u i)⁻¹ ∧ v j=(u j)⁻¹ by
    obtain ⟨v,n,hv,hi,hj⟩ := this
    exact ⟨v,⟨n,hv⟩,by rw [hi]; exact mul_inv_cancel _,by rw [hj]; exact mul_inv_cancel _⟩
  induction hm with
  | diag g => exact ⟨_,0,.diag g⁻¹,rfl,rfl⟩
  | copy b hb =>
    obtain ⟨c,hci,hcj,hc⟩ := extend_pair_E a i j (b j) (b i) (by
      rw [hb i j,norm_sub_rev (a i) (a j)])
    let x := FreeGroup.of (b i)
    let y := FreeGroup.of (b j)
    refine ⟨(fun _ => x⁻¹)*(fun k => FreeGroup.of (c k))*(fun _ => y⁻¹),1,?_,?_,?_⟩
    · simpa using ((UnitWords.diag x⁻¹).mul (.copy c hc)).mul (.diag y⁻¹)
    · simp [x,y,hci]
    · simp [x,y,hcj]
  | @mul u v m n hu hv ihu ihv =>
    obtain ⟨u',m',hu',hui,huj⟩ := ihu
    obtain ⟨v',n',hv',hvi,hvj⟩ := ihv
    exact ⟨v'*u',n'+m',hv'.mul hu',by simp [hui,hvi],by simp [huj,hvj]⟩

def pairHom (i j : ι) : (ι → LetterGroup) →* LetterGroup×LetterGroup where
  toFun u := (u i,u j)
  map_one' := rfl
  map_mul' _ _ := rfl

def pairGroup (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j) : Subgroup (LetterGroup×LetterGroup) where
  toSubmonoid := (unitGraded a).monoid.map (pairHom i j)
  inv_mem' := by
    rintro _ ⟨u,hu,rfl⟩
    obtain ⟨v,hv,hi,hj⟩ := unit_pair_inverse a i j hij u hu
    exact ⟨v,hv,Prod.ext (by
      change v i=(u i)⁻¹
      apply mul_left_cancel (a:=u i)
      simpa using hi) (by
      change v j=(u j)⁻¹
      apply mul_left_cancel (a:=u j)
      simpa using hj)⟩
lemma pairGroup_diag (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j) (g : LetterGroup) :
    (g,g)∈pairGroup a i j hij := by
  classical
  exact ⟨_,(unitGraded a).diagonal g,rfl⟩

def pairLeft (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j) : Subgroup LetterGroup :=
  (pairGroup a i j hij).comap (MonoidHom.inl LetterGroup LetterGroup)
instance pairLeft_normal (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j) :
    (pairLeft a i j hij).Normal := by
  constructor
  intro g hg k
  change (k*g*k⁻¹,1)∈pairGroup a i j hij
  have h := (pairGroup a i j hij).mul_mem
    ((pairGroup a i j hij).mul_mem (pairGroup_diag a i j hij k) hg)
    (pairGroup_diag a i j hij k⁻¹)
  simpa using h

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
abbrev Strings := FreeMonoid FiniteEuclidean

def stringEnergy : List FiniteEuclidean → List FiniteEuclidean → ℝ
  | x::l,y::k => ‖x-y‖^2+stringEnergy l k
  | _,_ => 0
@[simp] lemma stringEnergy_self (l : List FiniteEuclidean) : stringEnergy l l=0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [stringEnergy,ih]
variable {ι : Type uIndex}
def StringFamily (a : ι → FiniteEuclidean) (u : ℝ) (x : ι → Strings) : Prop :=
  (∀ i j,(x i).toList.length=(x j).toList.length) ∧
  ∀ i j,stringEnergy (x i).toList (x j).toList=u*‖a i-a j‖^2
end EuclideanRamsey

end

end OAI


