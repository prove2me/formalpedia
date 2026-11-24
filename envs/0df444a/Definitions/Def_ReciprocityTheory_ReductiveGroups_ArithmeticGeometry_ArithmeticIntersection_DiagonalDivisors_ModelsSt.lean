-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_ModelsSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_ModelsSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:00.551303+00:00
-- url     : https://prove2.me/theorems/dc7cf733-34e0-4c23-a9f8-f67ad5acf7a5
-- title:
--   Models St
-- statement:
--   Definitions and structural lemmas for Models St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/DiagonalDivisors/ModelsSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
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
section Defs
variable {o : Type*} {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι κ : Type*}
  {E : Type*} [AddCommGroup E] [Module Ω E] {r : ℕ}
variable {x : ι → Ω}
def dualLat (B : ChartBundle o x r E) (i : ι) : Set (E →ₗ[Ω] Ω) :=
  {ψ | ∀ v ∈ B.lat i, ψ v ∈ chartRing o x i}
def IsTwistedDualSec (B : ChartBundle o x r E) (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  ∀ i, x i ≠ 0 → ∀ k, ∀ v ∈ B.lat i, φ k v ∈ lineLat o x 1 i
def IsTwistedDualGen [Fintype κ] (B : ChartBundle o x r E) (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  ∀ i, x i ≠ 0 → ∀ ψ ∈ dualLat B i, ∃ c : κ → Ω, (∀ k, c k ∈ chartRing o x i) ∧
    ψ = ∑ k, c k • (x i)⁻¹ • φ k
variable {Φ : Type*} [Field Φ] [Algebra Ω Φ]
def detE (e : Module.Basis (Fin 2) Ω E) (u w : E) : Ω :=
  e.repr u 0 * e.repr w 1 - e.repr u 1 * e.repr w 0
def lineVal (e : Module.Basis (Fin 2) Ω E) (ψ : E →ₗ[Ω] Ω) (a : Φ) : Φ :=
  algebraMap Ω Φ (ψ (e 0)) + a * algebraMap Ω Φ (ψ (e 1))
def lineDet (e : Module.Basis (Fin 2) Ω E) (a : Φ) (u : E) : Φ :=
  algebraMap Ω Φ (e.repr u 1) - a * algebraMap Ω Φ (e.repr u 0)
def powVec (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) {m : ℕ}
    (a : Fin m → Φ) : ι × (Fin m → κ) → Φ :=
  segreJoin (fun i => algebraMap Ω Φ (x i)) (fun k => ∏ j, lineVal e (φ (k j)) (a j))
abbrev projVec (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Φ) :
    ι × (Fin 1 → κ) → Φ :=
  powVec x e φ ![a]
abbrev fibreSqVec (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) :
    ι × (Fin 2 → κ) → Φ :=
  powVec x e φ a
variable [Algebra o Φ] [IsScalarTower o Ω Φ]
def tautDualGens (B : ChartBundle o x r E) (e : Module.Basis (Fin 2) Ω E) (a : Φ) (i : ι) :
    Set Φ :=
  {F | ∃ ψ ∈ dualLat B i, F = lineVal e ψ a}
def detGens (B : ChartBundle o x r E) (e : Module.Basis (Fin 2) Ω E) (i : ι) : Set Φ :=
  {F | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, F = algebraMap Ω Φ (detE e u w)}
def diagBundleLat (B : ChartBundle o x r E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (i : ι) (k : Fin 2 → κ) : Submodule (chartRing o (fibreSqVec x e φ a) (i, k)) Φ :=
  Submodule.span _ {F | ∃ F₀ ∈ tautDualGens B e (a 0) i, ∃ F₁ ∈ tautDualGens B e (a 1) i,
    ∃ δ ∈ detGens B e i, F = F₀ * F₁ * δ}
def diagSec (a : Fin 2 → Φ) : Φ := a 1 - a 0
def pullThrough (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ)
    (N : ι → AddSubgroup Ω) (j : Fin 2) (i : ι) (k : Fin 2 → κ) :
    Submodule (chartRing o (fibreSqVec x e φ a) (i, k)) Φ :=
  Submodule.span _ (Submodule.span (chartRing o (projVec x e φ (a j)) (i, ![k j]))
    (algebraMap Ω Φ '' (N i : Set Ω)) : Set Φ)
def IsFrameOn (B : ChartBundle o x r E) (i : ι) (f : Ω) (b : Fin 2 → E) : Prop :=
  f ∈ chartRing o x i ∧ f ≠ 0 ∧ LinearIndependent Ω b ∧
    ∀ v, (∃ n : ℕ, f ^ n • v ∈ B.lat i) ↔
      ∃ c : Fin 2 → Ω, (∀ q, ∃ n : ℕ, f ^ n * c q ∈ chartRing o x i) ∧ v = ∑ q, c q • b q
def frameRing (x : ι → Ω) (i : ι) (f : Ω) : Subalgebra o Ω :=
  Algebra.adjoin o ((chartRing o x i : Set Ω) ∪ {f⁻¹})
def frameCoord (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a : Φ) : Φ :=
  -lineDet e a (b 0) / lineDet e a (b 1)
def frameGen (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a : Fin 2 → Φ) : Φ :=
  lineDet e (a 0) (b 1) * lineDet e (a 1) (b 1) / algebraMap Ω Φ (detE e (b 0) (b 1))
def frameChartRing (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a : Fin 2 → Φ)
    (i : ι) (f : Ω) : Subalgebra o Φ :=
  Algebra.adjoin o (algebraMap Ω Φ '' (frameRing (o := o) x i f : Set Ω) ∪ Set.range fun j => frameCoord e b (a j))
def frameAlpha (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a : Φ) : Φ :=
  lineDet e a (b 1) / algebraMap Ω Φ (detE e (b 0) (b 1))
def frameUnit (x : ι → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (b : Fin 2 → E)
    (a : Fin 2 → Φ) (i : ι) (k : Fin 2 → κ) (j : Fin 2) : Φ :=
  lineVal e (φ (k j)) (a j) / (algebraMap Ω Φ (x i) * frameAlpha e b (a j))
end Defs
section Statements
variable {o : Type*} {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι κ : Type*} [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
  {Φ : Type*} [Field Φ] [Algebra Ω Φ] [Algebra o Φ] [IsScalarTower o Ω Φ]
def PowChartStatement (B : ChartBundle o x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    Prop :=
  IsScalarTower o Ω Φ → IsTwistedDualSec B φ → IsTwistedDualGen B φ → ∀ (m : ℕ) (a : Fin m → Φ), AlgebraicIndependent Ω a →
    ∀ i (k : Fin m → κ), x i ≠ 0 → (∀ j, φ (k j) ≠ 0) →
      chartRing o (powVec x e φ a) (i, k) = Algebra.adjoin o (algebraMap Ω Φ '' (chartRing o x i : Set Ω) ∪
        ⋃ j, {y | ∃ ψ ∈ dualLat B i, y = algebraMap Ω Φ (x i) * lineVal e ψ (a j) / lineVal e (φ (k j)) (a j)})
def DiagSecStatement (B : ChartBundle o x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    Prop :=
  IsScalarTower o Ω Φ → IsTwistedDualSec B φ → IsTwistedDualGen B φ → ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ i k, x i ≠ 0 → (∀ j, φ (k j) ≠ 0) → diagSec a ∈ diagBundleLat B e φ a i k
def FrameChartStatement (B : ChartBundle o x 2 E) (e : Module.Basis (Fin 2) Ω E) : Prop :=
  IsScalarTower o Ω Φ → ∀ (a : Fin 2 → Φ), AlgebraicIndependent Ω a → ∀ i f (b : Fin 2 → E), x i ≠ 0 → IsFrameOn B i f b →
    AlgebraicIndependent Ω (fun j => frameCoord e b (a j)) ∧
    (∀ F₀ ∈ tautDualGens B e (a 0) i, ∀ F₁ ∈ tautDualGens B e (a 1) i, ∀ δ ∈ detGens (Φ := Φ) B e i,
      F₀ * F₁ * δ / frameGen e b a ∈ frameChartRing (o := o) x e b a i f) ∧
    (∃ n : ℕ, algebraMap Ω Φ (f ^ n) * frameGen e b a ∈
      Submodule.span (frameChartRing (o := o) x e b a i f) {F | ∃ F₀ ∈ tautDualGens B e (a 0) i,
        ∃ F₁ ∈ tautDualGens B e (a 1) i, ∃ δ ∈ detGens B e i, F = F₀ * F₁ * δ}) ∧
    diagSec a = frameGen e b a * (frameCoord e b (a 1) - frameCoord e b (a 0))
def FrameLocStatement (B : ChartBundle o x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    Prop :=
  IsScalarTower o Ω Φ → IsTwistedDualSec B φ → IsTwistedDualGen B φ → ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ i f (b : Fin 2 → E) (k : Fin 2 → κ), x i ≠ 0 → IsFrameOn B i f b → (∀ j, φ (k j) ≠ 0) →
      Algebra.adjoin o ((frameChartRing (o := o) x e b a i f : Set Φ) ∪
          Set.range fun j => (frameUnit x e φ b a i k j)⁻¹) =
        Algebra.adjoin o ((chartRing o (fibreSqVec x e φ a) (i, k) : Set Φ) ∪
          {(algebraMap Ω Φ f)⁻¹} ∪ Set.range (frameUnit x e φ b a i k))
def BaseLineStatement (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) : Prop :=
  IsScalarTower o Ω Φ → ∀ (a : Fin 2 → Φ), AlgebraicIndependent Ω a → ∀ (N : ι → AddSubgroup Ω) i k, x i ≠ 0 →
    (∀ j, φ (k j) ≠ 0) → pullThrough (o := o) x e φ a N 0 i k = pullThrough x e φ a N 1 i k
def threeFrames (b : Fin 2 → E) : Fin 3 → Fin 2 → E :=
  ![b, ![b 1, b 0], ![b 0, b 0 + b 1]]
def FrameCoverStatement (B : ChartBundle o x 2 E) : Prop :=
  (∀ i f (b : Fin 2 → E), IsFrameOn B i f b → ∀ c, IsFrameOn B i f (threeFrames b c)) ∧
  ∀ (K : Type u) [Field K] (p : Fin 2 → Fin 2 → K), (∀ j, p j ≠ 0) → ∃ c : Fin 3, ∀ j,
    p j 0 * (![![0, 1], ![1, 0], ![1, 1]] c : Fin 2 → K) 1 -
      p j 1 * (![![0, 1], ![1, 0], ![1, 1]] c : Fin 2 → K) 0 ≠ 0
end Statements
def diagIdeal (A : Type*) [CommRing A] : Ideal (MvPolynomial (Fin 2) A) :=
  RingHom.ker (aeval fun _ => Polynomial.X : MvPolynomial (Fin 2) A →ₐ[A] Polynomial A)
def DiagDivisorStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A],
    Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) A)} = diagIdeal A ∧ (diagIdeal A).IsPrime ∧
    ∀ [(diagIdeal A).IsPrime], Module.length (Localization.AtPrime (diagIdeal A))
      (Localization.AtPrime (diagIdeal A) ⧸
        Ideal.span {algebraMap (MvPolynomial (Fin 2) A) (Localization.AtPrime (diagIdeal A)) (X 0 - X 1)}) = 1
def InhabitStatement : Prop :=
  ∃ (B : ChartBundle ℤ (fun _ : Unit => (1 : ℚ)) 2 (Fin 2 → ℚ))
    (φ : Fin 2 → (Fin 2 → ℚ) →ₗ[ℚ] ℚ) (e : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ)),
    (∀ k, φ k ≠ 0) ∧ B.lat () ≠ ⊤ ∧ IsTwistedDualSec B φ ∧ IsTwistedDualGen B φ ∧
    ∃ a : Fin 2 → FractionRing (MvPolynomial (Fin 2) ℚ), AlgebraicIndependent ℚ a ∧
      chartRing ℤ (projVec (fun _ : Unit => (1 : ℚ)) e φ (a 0)) ((), ![0]) =
        Algebra.adjoin ℤ {a 0}
end ReciprocityTheory.ChartRestriction.G.AI.T


