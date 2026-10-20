-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
-- name    : OAI_NumberTheory_SingleFold_FiniteGeneration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:15:58.076055+00:00
-- url     : https://prove2.me/theorems/4f47fb00-9922-4867-b54d-cfc74811262e
-- title:
--   Height descent and finite generation of $E(\mathbb{Q})$
-- statement:
--   1. **Abstract descent.** Let $A$ be an abelian group with $h:A\to\mathbb{R}_{\ge0}$ having finitely many elements below every bound, satisfying
--   $$
--   h(P+Q)+h(P-Q)=2h(P)+2h(Q),\qquad h(2P)=4h(P),
--   $$
--      and let $F\subseteq A$ be finite with $A=F+2A$. Then $A$ is finitely generated.
--   2. **Application.** For $E:y^2=x^3-25x$ the canonical height has these properties. The eight points $S+\varepsilon G$, with $S\in\{O,T_0,T_5,T_0+T_5\}$ and $\varepsilon\in\{0,1\}$, where $T_0=(0,0)$, $T_5=(5,0)$, $G=(25/4,75/8)$, represent every class of $E(\mathbb{Q})/2E(\mathbb{Q})$.
--
--   Hence $E(\mathbb{Q})$ is a finitely generated abelian group, the Mordell–Weil theorem for this curve.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/FiniteGeneration.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/FiniteGeneration.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight

namespace OAI

namespace SingleFold.HeightDescent

universe u

variable {A : Type u} [AddCommGroup A]

theorem finitely_generated (h : A → ℝ) [Northcott h]
    (hn : ∀ P, 0 ≤ h P)
    (hp : ∀ P Q, h (P+Q)+h (P-Q)=2*h P+2*h Q)
    (hd : ∀ P, h ((2:ℕ) • P)=4*h P)
    (F : Finset A) (hF : ∀ P, ∃ R ∈ F, ∃ Q, P=R+(2:ℕ) • Q) : AddGroup.FG A := by
  classical
  obtain ⟨B,hB⟩ := (F.finite_toSet.image h).bddAbove
  let S : Set A := {P | h P ≤ B}
  have hS : S.Finite := Northcott.finite_le B
  have hR : ∀ R ∈ F, R ∈ AddSubgroup.closure S := by
    intro R hR
    apply AddSubgroup.subset_closure
    exact hB ⟨R,hR,rfl⟩
  have htop : AddSubgroup.closure S = ⊤ := by
    apply top_unique
    intro P _
    by_contra hh
    obtain ⟨P,hP,hmin⟩ := Northcott.exists_min_image h {P | P ∉ AddSubgroup.closure S} ⟨P,hh⟩
    have hPl : B < h P := by
      by_contra hle
      exact hP (AddSubgroup.subset_closure (le_of_not_gt hle))
    obtain ⟨R,hRF,Q,hPQ⟩ := hF P
    have hRB : h R ≤ B := hB ⟨R,hRF,rfl⟩
    have he : P-R=(2:ℕ) • Q := by rw [hPQ]; abel
    have hdQ : 4*h Q ≤ 2*h P+2*h R := by
      have hpara := hp P R
      rw [he,hd] at hpara
      linarith [hn (P+R)]
    have hsmall : h Q < h P := by linarith
    have hQ : Q ∈ AddSubgroup.closure S := by
      by_contra hQ
      have := hmin Q hQ
      linarith
    apply hP
    rw [hPQ]
    exact (AddSubgroup.closure S).add_mem (hR R hRF)
      ((AddSubgroup.closure S).nsmul_mem hQ 2)
  exact ⟨hS.toFinset, by simpa only [Set.Finite.coe_toFinset] using htop⟩

end SingleFold.HeightDescent

namespace SingleFold.CurveRank
open Descent

instance : Northcott CurveHeight.canonicalHeight where
  finite_le B := by
    obtain ⟨c,hc,hbound⟩ := CurveHeight.uniform_height
    apply (Northcott.finite_le (h := CurveHeight.naiveHeight) (2*B+c)).subset
    intro P hP
    have hh := (abs_le.mp (hbound P)).2
    change CurveHeight.canonicalHeight P ≤ B at hP
    change CurveHeight.naiveHeight P ≤ 2*B+c
    linarith

lemma canonical_parallelogram (P Q : E.Point) :
    CurveHeight.canonicalHeight (P+Q) + CurveHeight.canonicalHeight (P-Q) =
      2*CurveHeight.canonicalHeight P + 2*CurveHeight.canonicalHeight Q := by
  obtain ⟨C,hC⟩ := CurveHeight.approximate_parallelogram
  have hh := QuadraticLimit.limit_parallelogram CurveHeight.naiveHeight C
    CurveHeight.naiveHeight_zero hC P Q
  unfold CurveHeight.canonicalHeight
  convert congrArg (fun x : ℝ => (1/2:ℝ)*x) hh using 1 <;> ring

noncomputable def representatives : Finset E.Point := by
  classical
  exact {0,T0,T5,T0+T5} ∪ (({0,T0,T5,T0+T5} : Finset E.Point).image (· + G))

lemma representatives_cover (P : E.Point) : ∃ R ∈ representatives, ∃ Q, P=R+(2:ℕ) • Q := by
  classical
  obtain ⟨S,b,Q,hS,hP⟩ := mod_two_cover P
  have hmem : S ∈ ({0,T0,T5,T0+T5} : Finset E.Point) := by simpa using hS
  refine ⟨S+(if b then G else 0),?_,Q,hP⟩
  cases b
  · simpa only [representatives,Bool.false_eq_true,↓reduceIte,add_zero] using Finset.mem_union_left
      (({0,T0,T5,T0+T5} : Finset E.Point).image (· + G)) hmem
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S,hmem,rfl⟩)

instance : AddGroup.FG E.Point :=
  HeightDescent.finitely_generated CurveHeight.canonicalHeight CurveHeight.canonicalHeight_nonneg
    canonical_parallelogram
    (fun P => by convert CurveHeight.canonicalHeight_nsmul P 2 using 1; norm_num)
    representatives representatives_cover

end SingleFold.CurveRank

end OAI


