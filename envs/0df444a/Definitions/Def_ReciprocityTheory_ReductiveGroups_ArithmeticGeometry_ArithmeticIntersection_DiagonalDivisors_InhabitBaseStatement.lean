-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_InhabitBaseStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_InhabitBaseStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:03.185714+00:00
-- url     : https://prove2.me/theorems/8dc964a2-a432-4b0f-bd29-9baa0a276579
-- title:
--   Inhabit Base Statement
-- statement:
--   Definitions and structural lemmas for Inhabit Base Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/DiagonalDivisors/InhabitBaseStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_ModelsSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AI.T
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
universe u
inductive WBlk | base | det | line0 | line1
  deriving DecidableEq
instance : Fintype WBlk := ⟨{.base, .det, .line0, .line1}, by intro k; cases k <;> simp⟩
inductive YBlk | base | det | line
  deriving DecidableEq
instance : Fintype YBlk := ⟨{.base, .det, .line}, by intro k; cases k <;> simp⟩
def wwIdx (ι ν κ : Type u) : WBlk → Type u
  | .base => ι
  | .det => ν
  | .line0 => κ
  | .line1 => κ
def yyIdx (ι ν κ : Type u) : YBlk → Type u
  | .base => ι
  | .det => ν
  | .line => κ
instance wwIdx.fintype {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ] :
    (k : WBlk) → Fintype (wwIdx ι ν κ k)
  | .base => inferInstanceAs (Fintype ι)
  | .det => inferInstanceAs (Fintype ν)
  | .line0 => inferInstanceAs (Fintype κ)
  | .line1 => inferInstanceAs (Fintype κ)
instance yyIdx.fintype {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ] :
    (k : YBlk) → Fintype (yyIdx ι ν κ k)
  | .base => inferInstanceAs (Fintype ι)
  | .det => inferInstanceAs (Fintype ν)
  | .line => inferInstanceAs (Fintype κ)
def multiConeMap {K : Type*} {ι : K → Type*} {Φ : Type*} [Field Φ] (c : (Σ k, ι k) → Φ) :
    MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Φ :=
  eval₂Hom (Int.castRingHom _) fun p => C (c p) * X p.1
section Models
variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
def IsTwistedDetGen {x : ι → Ω} (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (δ : ν → Ω) :
    Prop :=
  ∀ i, x i ≠ 0 →
    (∀ l, δ l ∈ Submodule.span (chartRing ℤ x i)
      {d | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, d = x i * detE e u w}) ∧
    ∀ u ∈ B.lat i, ∀ w ∈ B.lat i,
      detE e u w ∈ Submodule.span (chartRing ℤ x i) (Set.range fun l => (x i)⁻¹ * δ l)
def wwCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) :
    (Σ k, wwIdx ι ν κ k) → Φ
  | ⟨.base, i⟩ => algebraMap Ω Φ (x i)
  | ⟨.det, l⟩ => algebraMap Ω Φ (δ l)
  | ⟨.line0, k⟩ => lineVal e (φ k) a₀
  | ⟨.line1, k⟩ => lineVal e (φ k) a₁
def yyCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Φ) :
    (Σ k, yyIdx ι ν κ k) → Φ
  | ⟨.base, i⟩ => algebraMap Ω Φ (x i)
  | ⟨.det, l⟩ => algebraMap Ω Φ (δ l)
  | ⟨.line, k⟩ => lineVal e (φ k) a
def wwIdeal (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) :
    Ideal (MRing (wwIdx ι ν κ)) :=
  RingHom.ker (multiConeMap (wwCoord x δ e φ a₀ a₁))
def yyIdeal (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Φ) :
    Ideal (MRing (yyIdx ι ν κ)) :=
  RingHom.ker (multiConeMap (yyCoord x δ e φ a))
def yyEmb (j : Fin 2) : (Σ k, yyIdx ι ν κ k) → (Σ k, wwIdx ι ν κ k)
  | ⟨.base, i⟩ => ⟨.base, i⟩
  | ⟨.det, l⟩ => ⟨.det, l⟩
  | ⟨.line, k⟩ => if j = 0 then ⟨.line0, k⟩ else ⟨.line1, k⟩
def baseIdeal (x : ι → Ω) : Ideal (MRing (fun _ : Unit => ι)) :=
  RingHom.ker (multiConeMap (fun p : (Σ _ : Unit, ι) => x p.2))
def WWArithVarStatement {x : ι → Ω} (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) : Prop :=
  IsTwistedDualSec B φ → IsTwistedDualGen B φ → IsTwistedDetGen B e δ →
    ∀ D : ℕ, IsArithVar (baseIdeal x) D → ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
      (∀ j, IsArithVar (yyIdeal x δ e φ (a j)) (D + 1)) ∧
      IsArithVar (wwIdeal x δ e φ (a 0) (a 1)) (D + 2) ∧
      IsArithVar (wwIdeal x δ e φ (a 0) (a 0)) (D + 1)
def wwDeg (n m : ℕ) : WBlk → ℕ
  | .base => n
  | _ => m
def YYComapStatement (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    Prop :=
  ∀ (a : Fin 2 → Φ) (j : Fin 2),
    (wwIdeal x δ e φ (a 0) (a 1)).comap (rename (yyEmb j) : MRing (yyIdx ι ν κ) →ₐ[ℤ] _).toRingHom =
      yyIdeal x δ e φ (a j)
def toZCycle {α : Type*} (z : α →₀ ℕ) : α →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) z
def DiagDivStatement {x : ι → Ω} (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) : Prop :=
  IsTwistedDualSec B φ → IsTwistedDualGen B φ → IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
      (∃ (n : ℕ) (g h : MRing (wwIdx ι ν κ)), IsMultiHomog g (wwDeg n 1) ∧
        IsMultiHomog h (wwDeg (n + 3) 0) ∧ h ∉ wwIdeal x δ e φ (a 0) (a 1) ∧
        aeval (wwCoord x δ e φ (a 0) (a 1)) g = diagSec a * aeval (wwCoord x δ e φ (a 0) (a 1)) h) ∧
      ∀ (n : ℕ) (g h : MRing (wwIdx ι ν κ)), IsMultiHomog g (wwDeg n 1) →
        IsMultiHomog h (wwDeg (n + 3) 0) → h ∉ wwIdeal x δ e φ (a 0) (a 1) →
        aeval (wwCoord x δ e φ (a 0) (a 1)) g = diagSec a * aeval (wwCoord x δ e φ (a 0) (a 1)) h →
          toZCycle (divCycle (wwIdeal x δ e φ (a 0) (a 1)) g) -
              toZCycle (divCycle (wwIdeal x δ e φ (a 0) (a 1)) h) =
            Finsupp.single (wwIdeal x δ e φ (a 0) (a 0)) 1
end Models
section Degrees
def unitDeg {K : Type*} [DecidableEq K] (k : K) : K → ℤ := Pi.single k 1
def twoXiDeg (j : Fin 2) : WBlk → ℤ :=
  3 • unitDeg .base - unitDeg .det - 2 • unitDeg (if j = 0 then .line0 else .line1)
def llDeg : WBlk → ℤ :=
  unitDeg .det + unitDeg .line0 + unitDeg .line1 - 3 • unitDeg .base
def pullDeg (j : Fin 2) (c : YBlk → ℤ) : WBlk → ℤ
  | .base => c .base
  | .det => c .det
  | .line0 => if j = 0 then c .line else 0
  | .line1 => if j = 0 then 0 else c .line
def twoXiDegY : YBlk → ℤ
  | .base => 3
  | .det => -1
  | .line => -2
end Degrees
section Diagonal
variable {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
def IsHermPull (j : Fin 2) (A : HermLine (yyIdx ι ν κ)) (A' : HermLine (wwIdx ι ν κ)) : Prop :=
  A'.a = pullDeg j A.a ∧ ∀ z, A'.h z = A.h fun p => z (yyEmb j p)
variable (ι ν κ) in

def HermPullStatement : Prop :=
  ∀ (j : Fin 2) (A : HermLine (yyIdx ι ν κ)), ∃ A' : HermLine (wwIdx ι ν κ),
    IsHermPull j A A' ∧ (IsSmoothHerm A → IsSmoothHerm A')
def DiagPullStatement {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  ∀ a₀ : Φ,
    (∀ (s : MRing (yyIdx ι ν κ)) (d : YBlk → ℕ), IsMultiHomog s d →
      divCycle (wwIdeal x δ e φ a₀ a₀) (rename (yyEmb 0) s) =
        divCycle (wwIdeal x δ e φ a₀ a₀) (rename (yyEmb 1) s)) ∧
    (∀ (A : HermLine (yyIdx ι ν κ)) (A₀ A₁ : HermLine (wwIdx ι ν κ)), IsHermPull 0 A A₀ →
      IsHermPull 1 A A₁ → ∀ z ∈ mcPts (wwIdeal x δ e φ a₀ a₀), ∃ c : ℂ, c ≠ 0 ∧
        (∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩) ∧ A₁.h z = ‖c‖ ^ A.a .line * A₀.h z) ∧
    (∀ (s : MRing (yyIdx ι ν κ)) (d : YBlk → ℕ), IsMultiHomog s d →
      ∀ (A : HermLine (yyIdx ι ν κ)) (A₀ A₁ : HermLine (wwIdx ι ν κ)), (∀ k, A.a k = d k) →
        IsHermPull 0 A A₀ → IsHermPull 1 A A₁ → ∀ z ∈ mcPts (wwIdeal x δ e φ a₀ a₀),
          logNorm A₀ (rename (yyEmb 0) s) z = logNorm A₁ (rename (yyEmb 1) s) z)
end Diagonal
def InhabitWWStatement : Prop :=
  ∃ (B : ChartBundle ℤ (fun _ : PUnit.{1} => (1 : ℚ)) 2 (Fin 2 → ℚ))
    (φ : PUnit.{1} ⊕ PUnit.{1} → (Fin 2 → ℚ) →ₗ[ℚ] ℚ) (e : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ)),
    IsTwistedDualSec B φ ∧ IsTwistedDualGen B φ ∧
    IsTwistedDetGen (ν := PUnit.{1}) B e (fun _ => 1) ∧
    ∃ a : Fin 2 → FractionRing (MvPolynomial (Fin 2) ℚ), AlgebraicIndependent ℚ a ∧
      wwIdeal (fun _ : PUnit.{1} => (1 : ℚ)) (fun _ : PUnit.{1} => (1 : ℚ)) e φ (a 0) (a 1) ≠
        wwIdeal (fun _ : PUnit.{1} => (1 : ℚ)) (fun _ : PUnit.{1} => (1 : ℚ)) e φ (a 0) (a 0)
def InhabitBaseStatement : Prop :=
  IsArithVar (baseIdeal (fun _ : PUnit.{1} => (1 : ℚ))) 1
end ReciprocityTheory.ChartRestriction.G.AI.T


