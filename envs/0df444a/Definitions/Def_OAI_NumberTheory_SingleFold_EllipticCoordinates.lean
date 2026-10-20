-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
-- name    : OAI_NumberTheory_SingleFold_EllipticCoordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:03:56.063678+00:00
-- url     : https://prove2.me/theorems/7a75b900-4cee-4d7a-bf9d-b17161b11e41
-- title:
--   Natural-number coordinates for points of $y^2=x^3-25x$
-- statement:
--   Let $E$ be the elliptic curve $y^2=x^3-25x$ over $\mathbb{Q}$, with point at infinity $O$.
--
--   1. **Point codes.** A point code is a flag together with two rational codes $x,y$. It is valid if both codes are valid and either the flag is $1$ and $x=y=0$ (the point $O$), or the flag is $0$ and
--   $$
--   y^2=x^3-25x .
--   $$
--      Valid codes decode to points of $E(\mathbb{Q})$, and every point has a canonical code. A code occupies $13$ natural coordinates (one flag and $2\times6$ code entries).
--   2. **Addition relation.** $\mathrm{Line}(d,n,x_1,x_2,y_1,x_3,y_3)$ says $d^2(x_3+x_1+x_2)=n^2$ and $d(y_3+y_1)=n(x_1-x_3)$, the chord-tangent rule with slope $n/d$. $\mathrm{AddEq}(a,b,c)$ is the case split of the group law: $c=b$ if $a=O$, $c=a$ if $b=O$, $c=O$ if $b=-a$, the chord through two points with distinct $x$, and the tangent of slope $(3x^2-25)/(2y)$ otherwise.
--   3. **Multiples and heights.** $\mathrm{MulRel}(n,a,b)$ says $a$ and $b$ are the canonical codes of $P$ and $nP$ for some point $P$. The height of a code is $\max(|\text{numerator of }x|,\text{denominator of }x)$, and $\mathrm{WRel}(m,a,v)$ says the code of $m$ times the point of $a$ has height $v$.
--
--   These are the coordinates in which the group law of $E$ is compiled into polynomial equations over $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PointCompiler

section
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

def E : WeierstrassCurve.Affine ℚ := ⟨0,0,0,-25,0⟩
instance : E.IsElliptic := by
  constructor
  norm_num [E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
lemma equation_iff (x y : ℚ) : E.Nonsingular x y ↔ y^2=x^3-25*x := by
  rw [←E.equation_iff_nonsingular]
  simp [WeierstrassCurve.Affine.equation_iff,E,sub_eq_add_neg]

structure Code where
  flag : ℕ
  x : RationalCode
  y : RationalCode

def Code.Valid (c : Code) : Prop := c.x.Valid ∧ c.y.Valid ∧
  ((c.flag=1 ∧ c.x.value=0 ∧ c.y.value=0) ∨
   (c.flag=0 ∧ c.y.value^2=c.x.value^3-25*c.x.value))
noncomputable def Code.toPoint (c : Code) (hc : c.Valid) : E.Point :=
  if h : c.flag=1 then 0 else some c.x.value c.y.value ((equation_iff _ _).mpr (hc.2.2.resolve_left (by tauto)).2)
noncomputable def encode : E.Point → Code
  | .zero => ⟨1,RationalCode.encode 0,RationalCode.encode 0⟩
  | .some x y _ => ⟨0,RationalCode.encode x,RationalCode.encode y⟩
lemma encode_valid (P : E.Point) : (encode P).Valid := by
  cases P with
  | zero => exact ⟨RationalCode.encode_valid _,RationalCode.encode_valid _,Or.inl ⟨rfl,RationalCode.encode_value _,RationalCode.encode_value _⟩⟩
  | some x y hp =>
    refine ⟨RationalCode.encode_valid _,RationalCode.encode_valid _,Or.inr ⟨rfl,?_⟩⟩
    simpa [encode,RationalCode.encode_value] using (equation_iff _ _).mp hp
abbrev Var := Unit ⊕ (Fin 2 × Fin 6)
def fromTuple (z : Var → ℕ) : Code :=
  ⟨z (.inl ()),code (fun j => z (.inr (0,j))),code (fun j => z (.inr (1,j)))⟩
def tuple (c : Code) : Var → ℕ := Sum.elim (fun _ => c.flag) (fun ij => if ij.1=0 then RationalCompiler.tuple c.x ij.2 else RationalCompiler.tuple c.y ij.2)
def Line (d n x₁ x₂ y₁ x₃ y₃ : ℚ) : Prop :=
  d^2*(x₃+x₁+x₂)=n^2 ∧ d*(y₃+y₁)=n*(x₁-x₃)
@[simp] lemma E_addX (x₁ x₂ l : ℚ) : E.addX x₁ x₂ l=l^2-x₁-x₂ := by simp [E]
@[simp] lemma E_addY (x₁ x₂ y₁ l : ℚ) : E.addY x₁ x₂ y₁ l=l*(x₁-(l^2-x₁-x₂))-y₁ := by simp [WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY,E]; ring
@[simp] lemma E_negY (x y : ℚ) : E.negY x y= -y := by simp [E]

def AddEq (a b c : Code) : Prop :=
  (a.flag=1 ∧ c=b) ∨
  (a.flag=0 ∧ b.flag=1 ∧ c=a) ∨
  (a.flag=0 ∧ b.flag=0 ∧ a.x.value=b.x.value ∧ a.y.value+b.y.value=0 ∧ c.flag=1) ∨
  (a.flag=0 ∧ b.flag=0 ∧ a.x.value≠b.x.value ∧ c.flag=0 ∧
    Line (a.x.value-b.x.value) (a.y.value-b.y.value) a.x.value b.x.value a.y.value c.x.value c.y.value) ∨
  (a.flag=0 ∧ b.flag=0 ∧ a.x.value=b.x.value ∧ a.y.value+b.y.value≠0 ∧ c.flag=0 ∧
    Line (2*a.y.value) (3*a.x.value^2-25) a.x.value a.x.value a.y.value c.x.value c.y.value)

variable {ι : Type} [Finite ι]
def At (z : ι×Var → ℕ) (i : ι) : Code := fromTuple (fun k => z (i,k))
def AllValid (z : ι×Var → ℕ) : Prop := ∀ i, (At z i).Valid
def ratMap : (ι×Fin 2)×Fin 6 → ι×Var := fun v => (v.1.1,Sum.inr (v.1.2,v.2))
def values (z : ι×Var → ℕ) : ι×Fin 2 → ℚ := value (z ∘ ratMap)
def xe (i : ι) : Expr (ι×Fin 2) := .var (i,0)
def ye (i : ι) : Expr (ι×Fin 2) := .var (i,1)
end

open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

def MulRel (n : ℕ) (a b : Code) : Prop := ∃ P : E.Point, a=encode P ∧ b=encode (n • P)
variable {α : Type}
def tripleMap (f g h : Var → α) (v : Fin 3×Var) : α := ![f v.2,g v.2,h v.2] v.1
end SingleFold.PointCompiler

namespace SingleFold.Compiler.Semi
variable {α : Type}
end SingleFold.Compiler.Semi

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

def Code.height (a : Code) : ℕ := max (a.x.p+a.x.n) a.x.d
def WRel (m : ℕ) (a : Code) (v : ℕ) : Prop := ∃ b, MulRel m a b ∧ b.height=v
end SingleFold.PointCompiler

end OAI


