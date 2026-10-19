-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:13:02.24161+00:00
-- url     : https://prove2.me/theorems/7b9ae1c5-8011-46c7-81c9-aaf709533459
-- title:
--   Unit words built from congruent copies of a configuration
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $E$ be the Euclidean space of finitely supported real sequences and $\Gamma$ the free group on the points of $E$, whose generator at $z$ is written $[z]$. Fix a configuration $a=(a_i)_{i\in\iota}$ in $E$. A family $b$ is a congruent copy of $a$ when $\|b_i-b_j\|=\|a_i-a_j\|$ for all $i,j$.
--
--   1. **Unit words.** The least relation on tuples $w\in\Gamma^\iota$ with grades $n$ such that constant tuples have grade $0$, the tuple $([b_i])_i$ of every congruent copy $b$ has grade $1$, and products add grades. It is a graded path system.
--   2. **Extending pairs.** Any two points $z,z'$ with $\|z'-z\|=\|a_j-a_i\|$ extend to a congruent copy $b$ with $b_i=z$ and $b_j=z'$. Consequently unit words have pair inverses.
--   3. **Pair groups.** For $i\ne j$, the image of the unit-word monoid under $u\mapsto(u_i,u_j)$ is a subgroup of $\Gamma\times\Gamma$ containing the diagonal. Its left part $\{g:(g,1)\in\text{pair group}\}$ is a normal subgroup of $\Gamma$.
--   4. **String energy.** For two lists of points, the sum of squared distances between corresponding entries.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseySpherical

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
def stringEnergy : List FiniteEuclidean → List FiniteEuclidean → ℝ
  | x::l,y::k => ‖x-y‖^2+stringEnergy l k
  | _,_ => 0
@[simp] lemma stringEnergy_self (l : List FiniteEuclidean) : stringEnergy l l=0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [stringEnergy,ih]
variable {ι : Type uIndex}
end EuclideanRamsey

end

end OAI


