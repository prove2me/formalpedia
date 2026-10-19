-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyCircle
-- name    : OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyCircle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:59:22.401192+00:00
-- url     : https://prove2.me/theorems/d5687b71-9136-48f3-a998-ba2efb05da4c
-- title:
--   Unit words, weighted paths and string families built from scaled congruent copies of a configuration
-- statement:
--   Let $E$ be the real inner product space of finitely supported real sequences $x=(x_0,x_1,x_2,\dots)$ (all but finitely many $x_n$ vanish), with $\langle x,y\rangle=\sum_{n\ge 0}x_ny_n$ and $\|x\|=\langle x,x\rangle^{1/2}$; it contains an isometric copy of every Euclidean space $\mathbb{R}^d$. Let $\Gamma$ be the free group on the set $E$ (the *letter group*); the generator belonging to a point $z\in E$ is written $[z]$. Fix an index set $\iota$ and a configuration $a=(a_i)_{i\in\iota}$ of points of $E$. Tuples $w\in\Gamma^\iota$ are multiplied coordinatewise. A family $b=(b_i)_{i\in\iota}$ of points of $E$ is a *congruent copy* of $a$ if $\|b_i-b_j\|=\|a_i-a_j\|$ for all $i,j\in\iota$.
--
--   1. **Unit words.** $\mathrm{UW}_a(w,n)$, for $w\in\Gamma^\iota$ and $n\in\mathbb{N}$, is the smallest relation such that: every constant tuple $(g)_{i\in\iota}$ with $g\in\Gamma$ satisfies $\mathrm{UW}_a\bigl((g)_i,0\bigr)$; for every congruent copy $b$ of $a$ the letter tuple satisfies $\mathrm{UW}_a\bigl(([b_i])_{i\in\iota},1\bigr)$; and $\mathrm{UW}_a(u,m)$ together with $\mathrm{UW}_a(v,n)$ implies $\mathrm{UW}_a(uv,m+n)$. The degree counts the copy letters used.
--   2. **Unit words as a graded path system.** A graded path system on $\Gamma^\iota$ is a relation between tuples and natural-number grades that holds for every constant tuple at grade $0$ and is closed under products with grades adding. The unit words form such a system; the tuples that are unit words of some degree form a submonoid of $\Gamma^\iota$, the *unit-word monoid*.
--   3. **Copies of weight $u$.** For $u\in\mathbb{R}$, a family $b=(b_i)_{i\in\iota}$ in $E$ is a *copy of $a$ of weight $u$* if $u\ge 0$ and
--   $$\|b_i-b_j\|^2=u\,\|a_i-a_j\|^2\qquad\text{for all } i,j\in\iota,$$
--   that is, $b$ is congruent to $a$ scaled by the factor $\sqrt u$.
--   4. **Weighted paths.** $\mathrm{Path}_a(w,\lambda)$, for $w\in\Gamma^\iota$ and $\lambda\in\mathbb{R}$, is the smallest relation that contains every constant tuple with weight $0$, contains the letter tuple $([b_i])_{i\in\iota}$ with weight $u$ for every copy $b$ of $a$ of weight $u$, and is closed under products with weights adding.
--   5. **Pair groups.** For indices $i\neq j$, let $\pi_{ij}:\Gamma^\iota\to\Gamma\times\Gamma$ be the homomorphism $w\mapsto(w_i,w_j)$, and let $\Pi_{ij}$ be the image of the unit-word monoid under $\pi_{ij}$. It is closed under inverses, hence a subgroup of $\Gamma\times\Gamma$, and it contains every diagonal pair $(g,g)$. Its left slice $\{g\in\Gamma:\ (g,1)\in\Pi_{ij}\}$ is a normal subgroup of $\Gamma$. Two auxiliary facts are proved along the way: for all $i,j\in\iota$ and all $z,z'\in E$ with $\|z'-z\|=\|a_j-a_i\|$ there is a congruent copy $b$ of $a$ with $b_i=z$ and $b_j=z'$ (obtained from $a$ by a translation and a reflection); and for $i\neq j$, every element $v$ of the unit-word monoid admits an element $b$ of that monoid with $v_ib_i=1$ and $v_jb_j=1$.
--   6. **Strings, energy and string families.** Let $\mathcal{S}$ be the free monoid of finite strings of points of $E$. For strings $x=(x_1,\dots,x_p)$ and $y=(y_1,\dots,y_q)$ the energy is
--   $$\mathcal{E}(x,y)=\sum_{t=1}^{\min(p,q)}\|x_t-y_t\|^2,$$
--   so that $\mathcal{E}(x,x)=0$. A family $(x_i)_{i\in\iota}$ of strings is a *string family of weight $u$* (with $u\in\mathbb{R}$) if all $x_i$ have the same length and $\mathcal{E}(x_i,x_j)=u\,\|a_i-a_j\|^2$ for all $i,j\in\iota$.
--
--   Paths in the free group are the combinatorial certificates behind the construction of monochromatic congruent copies of $a$. A string family of weight $1$ becomes a congruent copy of $a$ once the letters of each string are placed in mutually orthogonal blocks of coordinates of $E$. The pair groups are the tool used to show that, for an injective configuration, unit words cover the augmentation kernel of $\Gamma$ (the words of total exponent sum $0$) on every pair of coordinates.
--
--   **Formalization Note** `FiniteEuclidean` is `ℕ →₀ ℝ` with the inner product above, `LetterGroup` is `FreeGroup FiniteEuclidean` and `Strings` is `FreeMonoid FiniteEuclidean`. `UnitWords` and `Path` are inductive predicates, `unitGraded a` packages `UnitWords a` as a `GradedPaths` structure, and `CopyPath a u b` is item 3. `pairHom`, `pairGroup` and `pairLeft` (with the instance `pairLeft_normal`) are the objects of item 5, the last two taking a proof of `i ≠ j`; `extend_pair_E`, `unit_pair_inverse` and `pairGroup_diag` are the auxiliary lemmas. `stringEnergy` is defined by recursion on lists and stops at the end of the shorter list; `stringEnergy_self` is the identity $\mathcal{E}(x,x)=0$, and `StringFamily a u x` is item 6.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyCircle

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


