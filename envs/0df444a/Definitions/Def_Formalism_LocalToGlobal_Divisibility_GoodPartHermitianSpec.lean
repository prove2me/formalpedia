-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
-- name    : Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:01.643737+00:00
-- url     : https://prove2.me/theorems/9796b36e-7200-47b7-9b4c-1c2ee77a257b
-- title:
--   Good Part Hermitian Spec
-- statement:
--   Definitions and structural lemmas for Good Part Hermitian Spec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/GoodPartHermitianSpec.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section GroupAlgebra
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
def IsAbsIrrChar (χ : G → K) : Prop :=
  ∃ (n : ℕ) (ρ : Representation (AlgebraicClosure K) G (Fin n → AlgebraicClosure K)),
    ρ.IsIrreducible ∧ ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t)
def chiIdem (χ : G → K) : MonoidAlgebra K G :=
  ∑ t : G, MonoidAlgebra.single t (χ 1 / (Fintype.card G : K) * χ t⁻¹)
def idemOf (X : Finset (G → K)) : MonoidAlgebra K G := ∑ χ ∈ X, chiIdem χ
open Classical in

def lvlIdem (P : Subgroup G) (ψ : P →* Kˣ) : MonoidAlgebra K G :=
  ∑ h : P, MonoidAlgebra.single (h : G) ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K))
def goodAt (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : MonoidAlgebra K G :=
  idemOf X * lvlIdem P ψ
def gaStar [StarRing K] (a : MonoidAlgebra K G) : MonoidAlgebra K G :=
  ∑ t : G, MonoidAlgebra.single t⁻¹ (star (a.coeff t))
end GroupAlgebra
section Image
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
def subDim (Z : Submodule K (Fin n → K)) : ℕ := finrank K Z
def SubHasRatBasis (Z : Submodule K (Fin n → K)) : Prop :=
  ∃ b : Basis (Fin (subDim Z)) K Z, ∀ j i, (b j : Fin n → K) i ∈ cmMax K
open Classical in

def subBasis (Z : Submodule K (Fin n → K)) : Basis (Fin (subDim Z)) K Z :=
  if h : SubHasRatBasis Z then h.choose else finBasis K Z
def subE (Z : Submodule K (Fin n → K)) : Matrix (Fin n) (Fin (subDim Z)) K :=
  Matrix.of fun i j => (subBasis Z j : Fin n → K) i
abbrev imDim (e : Matrix (Fin n) (Fin n) K) : ℕ := subDim (LinearMap.range e.mulVecLin)
def imE (e : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin (imDim e)) K :=
  subE (LinearMap.range e.mulVecLin)
def orthPr {d : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K) :
    Matrix (Fin d) (Fin n) K :=
  (Eᴴ * H * E)⁻¹ * (Eᴴ * H)
end Image
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
def actMat (t : G) : Matrix (Fin S.dim) (Fin S.dim) K := LinearMap.toMatrix S.basis S.basis (r t)
def gaMat (a : MonoidAlgebra K G) : Matrix (Fin S.dim) (Fin S.dim) K := ∑ t : G, a.coeff t • S.actMat r t
structure ActGood : Prop where
  unitary : ∀ (t : G) (f g : S.Forms),
    S.csum (r t f : S.Cl → S.V) (r t g : S.Cl → S.V) = S.csum (f : S.Cl → S.V) (g : S.Cl → S.V)
  nab_stable : ∀ (t : G) (f : S.Forms), (∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) →
    ∀ c, (r t f : S.Cl → S.V) c ∈ S.Nab c
  del_stable : ∀ (t : G) (f : S.Forms), (∀ c, (f : S.Cl → S.V) c ∈ S.Del c) →
    ∀ c, (r t f : S.Cl → S.V) c ∈ S.Del c
def ActRat : Prop := ∀ (t : G) i j, S.actMat r t i j ∈ cmMax K
abbrev cutDim (a : MonoidAlgebra K G) : ℕ := imDim (S.gaMat r a)
def cutE (a : MonoidAlgebra K G) : Matrix (Fin S.dim) (Fin (S.cutDim r a)) K := imE (S.gaMat r a)
def cutPr (a : MonoidAlgebra K G) : Matrix (Fin (S.cutDim r a)) (Fin S.dim) K :=
  orthPr S.H (S.cutE r a)
def cutH (a : MonoidAlgebra K G) : Matrix (Fin (S.cutDim r a)) (Fin (S.cutDim r a)) K :=
  (S.cutE r a)ᴴ * S.H * S.cutE r a
def cutNab (a : MonoidAlgebra K G) : Submodule (𝓞 K) (Fin (S.cutDim r a) → K) :=
  cutLat (S.cutE r a) S.nabLat
def cutDel (a : MonoidAlgebra K G) : Submodule (𝓞 K) (Fin (S.cutDim r a) → K) :=
  cutLat (S.cutE r a) S.delLat
def lvlPart (P : Subgroup G) (ψ : P →* Kˣ) : Submodule K (Fin S.dim → K) where
  carrier := {x | ∀ h : P, (S.actMat r (h : G)).mulVec x = ((ψ h : Kˣ) : K) • x}
  add_mem' := by
    intro x y hx hy h
    rw [Matrix.mulVec_add, hx h, hy h, smul_add]
  zero_mem' := by
    intro h
    rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' := by
    intro a x hx h
    rw [Matrix.mulVec_smul, hx h, smul_comm]
variable (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
abbrev lvlDim : ℕ := S.cutDim r (lvlIdem P ψ)
def lvlE : Matrix (Fin S.dim) (Fin (S.lvlDim r P ψ)) K := S.cutE r (lvlIdem P ψ)
def lvlPr : Matrix (Fin (S.lvlDim r P ψ)) (Fin S.dim) K := S.cutPr r (lvlIdem P ψ)
def lvlH : Matrix (Fin (S.lvlDim r P ψ)) (Fin (S.lvlDim r P ψ)) K :=
  (Nat.card P : K)⁻¹ • S.cutH r (lvlIdem P ψ)
def lvlNab : Submodule (𝓞 K) (Fin (S.lvlDim r P ψ) → K) := S.cutNab r (lvlIdem P ψ)
def lvlDel : Submodule (𝓞 K) (Fin (S.lvlDim r P ψ) → K) := S.cutDel r (lvlIdem P ψ)
def lvlI : (Fin (S.lvlDim r P ψ) → K) →ₗ[K] (S.Cl → S.V) := S.I ∘ₗ (S.lvlE r P ψ).mulVecLin
def lvlOp (a : MonoidAlgebra K G) : Matrix (Fin (S.lvlDim r P ψ)) (Fin (S.lvlDim r P ψ)) K :=
  S.lvlPr r P ψ * S.gaMat r a * S.lvlE r P ψ
abbrev BaseDimension : ℕ := S.cutDim r (goodAt X P ψ)
def V0E : Matrix (Fin S.dim) (Fin (S.BaseDimension r X P ψ)) K := S.cutE r (goodAt X P ψ)
def goodPartProjection : Matrix (Fin (S.BaseDimension r X P ψ)) (Fin S.dim) K := S.cutPr r (goodAt X P ψ)
def goodPartHermitianForm : Matrix (Fin (S.BaseDimension r X P ψ)) (Fin (S.BaseDimension r X P ψ)) K :=
  (Nat.card P : K)⁻¹ • S.cutH r (goodAt X P ψ)
def Mt : Submodule (𝓞 K) (Fin (S.BaseDimension r X P ψ) → K) := S.cutNab r (goodAt X P ψ)
def MtDel : Submodule (𝓞 K) (Fin (S.BaseDimension r X P ψ) → K) := S.cutDel r (goodAt X P ψ)
end CSD
section Statements
structure IsProjElt {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    (a : MonoidAlgebra K G) (N : ℕ) : Prop where
  idem : a * a = a
  selfAdj : gaStar a = a
  rat : ∀ t, a.coeff t ∈ cmMax K
  integral : ∀ t, ∃ b : 𝓞 K, (b : K) = (N : K) * a.coeff t
def IdemOfSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) →
      IsProjElt (idemOf X) (Fintype.card G) ∧ ∀ b : MonoidAlgebra K G, b * idemOf X = idemOf X * b
def IdemOfCentral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)),
    (∀ χ ∈ X, IsAbsIrrChar χ) →
      idemOf X * idemOf X = idemOf X ∧ ∀ b : MonoidAlgebra K G, b * idemOf X = idemOf X * b
def IdemOfOrth : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X Y : Finset (G → K)),
    (∀ χ ∈ X, IsAbsIrrChar χ) → (∀ χ ∈ Y, IsAbsIrrChar χ) → Disjoint X Y → idemOf X * idemOf Y = 0
def LvlIdemSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (G : Type) [Group G] [Fintype G] (P : Subgroup G) (ψ : P →* Kˣ),
      IsProjElt (lvlIdem P ψ) (Nat.card P) ∧
      ∀ h : P, MonoidAlgebra.single (h : G) (1 : K) * lvlIdem P ψ = ((ψ h : Kˣ) : K) • lvlIdem P ψ
def LvlIdemBot : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [Group G] [Fintype G] (ψ : (⊥ : Subgroup G) →* Kˣ),
    lvlIdem (⊥ : Subgroup G) ψ = 1
def GoodAtSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ), IsProjElt (goodAt X P ψ) (Fintype.card G * Nat.card P)
def SubESpec : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : ℕ) (Z : Submodule K (Fin n → K)),
    Function.Injective (subE Z).mulVec ∧ LinearMap.range (subE Z).mulVecLin = Z
def ImESpec : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : ℕ) (e : Matrix (Fin n) (Fin n) K),
    Function.Injective (imE e).mulVec ∧
      LinearMap.range (imE e).mulVecLin = LinearMap.range e.mulVecLin
def ImERat : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : ℕ) (e : Matrix (Fin n) (Fin n) K),
    (∀ i j, e i j ∈ cmMax K) → ∀ i j, imE e i j ∈ cmMax K
def ActMatSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G]
    (r : Representation K G S.Forms) (t : G) (x : Fin S.dim → K),
    S.I ((S.actMat r t).mulVec x) = (r t (S.basis.equivFun.symm x) : S.Cl → S.V)
def GaMatHom : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G]
    (r : Representation K G S.Forms),
    S.gaMat r 1 = 1 ∧ ∀ a b : MonoidAlgebra K G, S.gaMat r (a * b) = S.gaMat r a * S.gaMat r b
def GaMatAdj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G]
    (r : Representation K G S.Forms), S.ActGood r →
    ∀ a : MonoidAlgebra K G, (S.gaMat r a)ᴴ * S.H = S.H * S.gaMat r (gaStar a)
def ActLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G]
    (r : Representation K G S.Forms), S.ActGood r → ∀ t : G,
    (∀ x ∈ S.nabLat, (S.actMat r t).mulVec x ∈ S.nabLat) ∧
      ∀ x ∈ S.delLat, (S.actMat r t).mulVec x ∈ S.delLat
def CutOrthProj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (S : CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ a : MonoidAlgebra K G, a * a = a → gaStar a = a →
      IsOrthProj S.H (S.cutE r a) (S.cutPr r a) ∧ S.cutE r a * S.cutPr r a = S.gaMat r a
def LvlPartSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G]
    (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ),
    LinearMap.range (S.gaMat r (lvlIdem P ψ)).mulVecLin = S.lvlPart r P ψ
def LvlClassSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G]
    (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ),
    Function.Injective (S.lvlI r P ψ) ∧
      IsClassSum (S.lvlH r P ψ) (S.lvlI r P ψ) S.pair (fun c => Nat.card P * S.wt c) ∧
      S.lvlNab r P ψ = valLatF (S.lvlI r P ψ) S.Nab ∧ S.lvlDel r P ψ = valLatF (S.lvlI r P ψ) S.Del
def LvlOpSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (S : CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), a * lvlIdem P ψ = lvlIdem P ψ * a →
      S.lvlE r P ψ * S.lvlOp r P ψ a = S.gaMat r a * S.lvlE r P ψ ∧
      ∀ b : MonoidAlgebra K G, S.lvlOp r P ψ (b * a) = S.lvlOp r P ψ b * S.lvlOp r P ψ a
def LvlOpIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (S : CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P : Subgroup G) (ψ : P →* Kˣ),
      (∀ x ∈ S.lvlNab r P ψ,
        (Fintype.card G : 𝓞 K) • (S.lvlOp r P ψ (idemOf X)).mulVec x ∈ S.lvlNab r P ψ) ∧
      ∀ x ∈ S.lvlDel r P ψ,
        (Fintype.card G : 𝓞 K) • (S.lvlOp r P ψ (idemOf X)).mulVec x ∈ S.lvlDel r P ψ
def LvlDualLe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (S : CSD K) (s : ℕ), S.Good s → (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ),
      ∀ y ∈ Formalism.HermitianLatticesTheory.dual (hform (S.lvlH r P ψ)) (S.lvlNab r P ψ), (s : 𝓞 K) • y ∈ S.lvlDel r P ψ
def GoodPartSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G]
    (r : Representation K G S.Forms) (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ),
    LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (idemOf X)).mulVecLin ⊓ S.lvlPart r P ψ
def GoodPartHermitianSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (S : CSD K), (∀ i j, S.H i j ∈ cmMax K) → (∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActRat r →
    ∀ (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P : Subgroup G) (ψ : P →* Kˣ),
      (∀ i j, S.V0E r X P ψ i j ∈ cmMax K) ∧ (∀ i j, S.goodPartHermitianForm r X P ψ i j ∈ cmMax K) ∧
        ∀ v : InfinitePlace K, ((S.goodPartHermitianForm r X P ψ).map v.embedding).PosDef
def BoundsIHyps : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (S : CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P : Subgroup G) (ψ : P →* Kˣ),
      IsOrthProj S.H (S.V0E r X P ψ) (S.goodPartProjection r X P ψ) ∧
      S.V0E r X P ψ * S.goodPartProjection r X P ψ = ∑ t : G, (goodAt X P ψ).coeff t • S.actMat r t ∧
      (∀ t : G, ∃ a : 𝓞 K, (a : K) = ((Fintype.card G * Nat.card P : ℕ) : K) * (goodAt X P ψ).coeff t) ∧
      ∀ t : G, ∀ x ∈ valLatF S.I S.Del, (S.actMat r t).mulVec x ∈ valLatF S.I S.Del
def BoundsIAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (S : CSD K) (s : ℕ), S.Good s → (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P : Subgroup G) (ψ : P →* Kˣ),
      Submodule.IsLattice K S.nabLat ∧ Submodule.IsLattice K (S.Mt r X P ψ) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (S.goodPartHermitianForm r X P ψ)) (S.Mt r X P ψ),
        ((Fintype.card G * s : ℕ) : 𝓞 K) • x ∈ S.Mt r X P ψ
end Statements
end Formalism.L2.DIV


