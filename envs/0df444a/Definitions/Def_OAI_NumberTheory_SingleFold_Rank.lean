-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_Rank
-- name    : OAI_NumberTheory_SingleFold_Rank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:16:40.817314+00:00
-- url     : https://prove2.me/theorems/b6d82cd5-7f3d-429f-a7b9-573fd4c71c75
-- title:
--   Two-torsion and doubling subgroups for the rank computation
-- statement:
--   For an abelian group $A$:
--
--   1. $2A=\{2P:P\in A\}$ and $A[2]=\{P:2P=0\}$.
--   2. A group isomorphism $A\cong B$ restricts to a bijection $A[2]\cong B[2]$, and
--   $$
--   (\mathbb{Z}^\iota\times T)[2]\cong T[2] .
--   $$
--
--   For $E:y^2=x^3-25x$, the group $E(\mathbb{Q})[2]$ is finite, since its points have canonical height $0$. The points $T_{-5}=(-5,0)$, $G=(25/4,75/8)$ and the $2$-adic valuation $v_2(x(P))$ of the $x$-coordinate (with value $0$ at $O$) are also recorded.
--
--   These are used to compare $E(\mathbb{Q})/2E(\mathbb{Q})$ with $\mathbb{Z}^r\times T$ and to show that the rank is exactly one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Rank.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Rank.lean by skeleton subtraction
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
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration

namespace OAI

namespace SingleFold.AbstractRank

universe u v w

variable (A : Type u) [AddCommGroup A]

def doubleRange : AddSubgroup A := (nsmulAddMonoidHom (α:=A) 2).range

def doubleKernel : AddSubgroup A := (nsmulAddMonoidHom (α:=A) 2).ker

variable {A}

noncomputable def doubleKernel_equiv {B : Type v} [AddCommGroup B] (f : A ≃+ B) :
    doubleKernel A ≃ doubleKernel B where
  toFun x := ⟨f x,by
    change (2:ℕ) • f x=0
    rw [←map_nsmul]
    have hx := x.property
    change (2:ℕ) • (x:A)=0 at hx
    rw [hx,map_zero]⟩
  invFun x := ⟨f.symm x,by
    change (2:ℕ) • f.symm x=0
    rw [←map_nsmul]
    have hx := x.property
    change (2:ℕ) • (x:B)=0 at hx
    rw [hx,map_zero]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

noncomputable def doubleKernel_free_prod_equiv (ι : Type v) (T : Type w) [AddCommGroup T] :
    doubleKernel ((ι → ℤ)×T) ≃ doubleKernel T where
  toFun x := ⟨x.val.2,congrArg Prod.snd x.property⟩
  invFun x := ⟨(0,x.val), Prod.ext (by simp) x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      have hh := congrArg (fun a : (ι → ℤ)×T => a.1 i) x.property
      change (2:ℕ) • x.val.1 i=0 at hh
      simp only [nsmul_eq_mul] at hh
      change 0=x.val.1 i
      omega
    · rfl
  right_inv x := rfl

end SingleFold.AbstractRank

namespace SingleFold.CurveRank
open Descent WeierstrassCurve.Affine.Point

noncomputable instance : Finite (AbstractRank.doubleKernel E.Point) := by
  let S : Set E.Point := {P | CurveHeight.canonicalHeight P ≤ 0}
  have hS : S.Finite := Northcott.finite_le (h := CurveHeight.canonicalHeight) 0
  let f : AbstractRank.doubleKernel E.Point → S := fun P => ⟨P.val,by
    have hh := CurveHeight.canonicalHeight_nsmul P.val 2
    have hp := P.property
    change (2:ℕ) • P.val=0 at hp
    rw [hp,CurveHeight.canonicalHeight_zero] at hh
    norm_num at hh
    change CurveHeight.canonicalHeight P.val ≤ 0
    linarith⟩
  have : Finite S := hS.to_subtype
  exact Finite.of_injective f (by intro x y h; exact Subtype.ext (congrArg (fun z : S => z.val) h))

def Tm5 : E.Point := some (-5) 0 (E.equation_iff_nonsingular.mp (by
  norm_num [WeierstrassCurve.Affine.equation_iff]))

end SingleFold.CurveRank

namespace SingleFold.ValuationRank
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

abbrev E : WeierstrassCurve.Affine ℚ := ⟨0,0,0,-25,0⟩
instance : E.IsElliptic := by
  constructor
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

noncomputable def vx : E.Point → ℤ
  | .zero => 0
  | .some x _ _ => padicValRat 2 x

def G : E.Point := some (25/4) (75/8) (E.equation_iff_nonsingular.mp (by
  norm_num [WeierstrassCurve.Affine.equation_iff]))

end SingleFold.ValuationRank

namespace SingleFold.CurveRank
open Descent

end SingleFold.CurveRank

end OAI


