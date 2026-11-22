-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_HLatOps
-- name    : Formalism_LocalToGlobal_GlobalTheory_HLatOps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:13.072286+00:00
-- url     : https://prove2.me/theorems/55df7b97-700c-4f25-8dc1-98aefeee9b6c
-- title:
--   HLat Ops
-- statement:
--   Definitions and structural lemmas for HLat Ops, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/HLatOps.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField ComplexOrder
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.HLatOps
open Formalism.BasicNotions
section Defs
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def FrameOK (A : HLat K) : Prop := ∀ v, IsUnit (A.X v).det
structure Iso (A B : HLat K) where

  e : A.V ≃ₗ[K] B.V

  map_L : A.L.map (e.toLinearMap.restrictScalars (𝓞 K)) = B.L

  norm : ∀ v x, Formalism.HermitianLatticesTheory.normAt B.b B.X v (e x) = Formalism.HermitianLatticesTheory.normAt A.b A.X v x
@[reducible] def withL (A : HLat K) (L' : Submodule (𝓞 K) A.V) : HLat K := { A with L := L' }
@[reducible] def dual (A : HLat K) : HLat K where
  V := Module.Dual K A.V
  ι := A.ι
  b := A.dualB
  X := A.dualX
  L := A.dualL
def IsSesq {V : Type} [AddCommGroup V] [Module K V] (H : InfinitePlace K → V → V → ℂ) : Prop :=
  ∀ v, (∀ x x' y, H v (x + x') y = H v x y + H v x' y) ∧
    (∀ x y y', H v x (y + y') = H v x y + H v x y') ∧
    (∀ (a : K) x y, H v (a • x) y = starRingEnd ℂ (v.embedding a) * H v x y) ∧
    (∀ (a : K) x y, H v x (a • y) = v.embedding a * H v x y)
def gramOf {V ι : Type} [AddCommGroup V] [Module K V] (b : Basis ι K V) (H : V → V → ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j => H (b i) (b j)
def PosAt {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V)
    (H : InfinitePlace K → V → V → ℂ) : Prop :=
  ∀ v, (gramOf b (H v)).PosDef
open Classical in

def frameOf {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if h : ∃ B : Matrix ι ι ℂ, IsUnit B.det ∧ B.conjTranspose * B = G then (Classical.choose h)⁻¹
  else 1
@[reducible] def ofFormB {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (L : Submodule (𝓞 K) V)
    (H : InfinitePlace K → V → V → ℂ) : HLat K where
  V := V
  ι := ι
  b := b
  X := fun v => frameOf (gramOf b (H v))
  L := L
@[reducible] def ofForm {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Module.Finite K V] (L : Submodule (𝓞 K) V) (H : InfinitePlace K → V → V → ℂ) : HLat K :=
  ofFormB (Module.finBasis K V) L H
@[reducible] def pull (B : HLat K) {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] [Fintype κ] [DecidableEq κ] (c : Basis κ K W) (f : W →ₗ[K] B.V) :
    HLat K :=
  ofFormB c (B.L.comap (f.restrictScalars (𝓞 K)))
    (fun v x y => Formalism.HermitianLatticesTheory.majAt B.b B.X v (f x) (f y))
@[reducible] def sub (B : HLat K) (U : Submodule K B.V) : HLat K :=
  haveI : Module.Finite K B.V := Module.Finite.of_basis B.b
  pull B (Module.finBasis K U) U.subtype
end Defs
def IsoInv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A B : HLat K), Iso A B →
    A.rank = B.rank ∧ (FrameOK A ↔ FrameOK B) ∧ (A.L.FG ↔ B.L.FG) ∧ (A.Good ↔ B.Good) ∧
    (FrameOK A → A.L.FG →
      A.mu = B.mu ∧ A.muMax = B.muMax ∧ A.muMin = B.muMin ∧ A.lcv = B.lcv)
def IsoGroupoid : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A B C : HLat K),
    (∃ I : Iso A A, ∀ x, I.e x = x) ∧
    (∀ I : Iso A B, ∃ J : Iso B A, ∀ x, J.e (I.e x) = x) ∧
    (∀ (I : Iso A B) (J : Iso B C), ∃ M : Iso A C, ∀ x, M.e x = J.e (I.e x))
def IsoWithL : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A B : HLat K) (I : Iso A B)
    (L' : Submodule (𝓞 K) A.V),
    ∃ J : Iso (withL A L') (withL B (L'.map (I.e.toLinearMap.restrictScalars (𝓞 K)))),
      ∀ x : A.V, (J.e x : B.V) = I.e x
def FrameFree : Prop :=
  ∀ (K V ι κ : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K V)
    (X' : InfinitePlace K → Matrix κ κ ℂ), (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    (∀ v x, Formalism.HermitianLatticesTheory.normAt b X v x = Formalism.HermitianLatticesTheory.normAt b' X' v x) →
    ∀ L : Submodule (𝓞 K) V, L.FG →
      Formalism.HN.ht b X L = Formalism.HN.ht b' X' L ∧ Formalism.HN.muDef b X L = Formalism.HN.muDef b' X' L ∧
      Formalism.HN.muMaxDef b X L = Formalism.HN.muMaxDef b' X' L ∧
      Formalism.HN.muMinDef b X L = Formalism.HN.muMinDef b' X' L
def IsoMaj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A B : HLat K)
    (I : Iso A B) (v : InfinitePlace K) (x y : A.V),
    Formalism.HermitianLatticesTheory.majAt B.b B.X v (I.e x) (I.e y) = Formalism.HermitianLatticesTheory.majAt A.b A.X v x y
def DualNumbers : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A : HLat K),
    A.Good → 0 < A.rank →
    A.muDual = -A.mu ∧ A.muMaxDual = -A.muMin ∧ A.muMinDual = -A.muMax
def IsoInvDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A B : HLat K),
    Iso A B → A.Good →
    A.muDual = B.muDual ∧ A.muMaxDual = B.muMaxDual ∧ A.muMinDual = B.muMinDual
def IsoDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A B : HLat K)
    (I : Iso A B), FrameOK A →
    ∃ J : Iso (dual A) (dual B), ∀ (f : Module.Dual K A.V) (x : A.V),
      (J.e f : Module.Dual K B.V) (I.e x) = f x
def OfFormSpec : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (L : Submodule (𝓞 K) V) (H : InfinitePlace K → V → V → ℂ), IsSesq H → PosAt b H →
    FrameOK (ofFormB b L H) ∧
    (∀ v (x y : V), Formalism.HermitianLatticesTheory.majAt (ofFormB b L H).b (ofFormB b L H).X v x y = H v x y) ∧
    (∀ v (x : V), Formalism.HermitianLatticesTheory.normAt (ofFormB b L H).b (ofFormB b L H).X v x =
      Real.sqrt (H v x x).re)
def OfFormIndep : Prop :=
  ∀ (K V ι κ : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (b : Basis ι K V) (b' : Basis κ K V) (L : Submodule (𝓞 K) V)
    (H : InfinitePlace K → V → V → ℂ), IsSesq H → PosAt b H →
    PosAt b' H ∧ ∃ I : Iso (ofFormB b L H) (ofFormB b' L H), ∀ x : V, (I.e x : V) = x
def OfFormSelf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K), FrameOK A →
    IsSesq (fun v => Formalism.HermitianLatticesTheory.majAt A.b A.X v) ∧ PosAt A.b (fun v => Formalism.HermitianLatticesTheory.majAt A.b A.X v) ∧
    ∃ I : Iso A (ofFormB A.b A.L (fun v => Formalism.HermitianLatticesTheory.majAt A.b A.X v)), ∀ x : A.V, (I.e x : A.V) = x
def PullSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (B : HLat K) (W κ : Type) [AddCommGroup W]
    [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] [Fintype κ] [DecidableEq κ]
    (c : Basis κ K W) (f : W →ₗ[K] B.V), FrameOK B → Function.Injective f →
    FrameOK (pull B c f) ∧
    (∀ v (x y : W), Formalism.HermitianLatticesTheory.majAt (pull B c f).b (pull B c f).X v x y =
      Formalism.HermitianLatticesTheory.majAt B.b B.X v (f x) (f y)) ∧
    (∀ v (x : W), Formalism.HermitianLatticesTheory.normAt (pull B c f).b (pull B c f).X v x =
      Formalism.HermitianLatticesTheory.normAt B.b B.X v (f x)) ∧
    (B.L.FG → (pull B c f).L.FG ∧
      (pull B c f).rank = (withL B (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))).rank ∧
      (pull B c f).mu = (withL B (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))).mu ∧
      (pull B c f).muMax = (withL B (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))).muMax ∧
      (pull B c f).muMin = (withL B (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))).muMin) ∧
    (B.Good → (pull B c f).Good)
def EmbIso : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A B : HLat K) (ψ : A.V →ₗ[K] B.V)
    (U : Submodule K B.V), FrameOK B → Function.Injective ψ → LinearMap.range ψ = U →
    (∀ v x, Formalism.HermitianLatticesTheory.normAt A.b A.X v x = Formalism.HermitianLatticesTheory.normAt B.b B.X v (ψ x)) →
    ∃ I : Iso (withL A (B.L.comap (ψ.restrictScalars (𝓞 K)))) (sub B U),
      ∀ x : A.V, U.subtype (I.e x) = ψ x
def WithLIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A : HLat K)
    (L' : Submodule (𝓞 K) A.V), FrameOK A → A.L.FG → L' ≤ A.L → L' ≠ ⊥ →
    (withL A L').muMax ≤ A.muMax ∧
    ((withL A L').rank = A.rank →
      (withL A L').mu = A.mu - 2 * Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) /
        ((Module.finrank ℚ K : ℝ) * (A.rank : ℝ)))
def IsoSub : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A B : HLat K) (I : Iso A B)
    (U : Submodule K A.V), FrameOK A →
    ∃ J : Iso (sub A U) (sub B (U.map I.e.toLinearMap)),
      ∀ x : U, (U.map I.e.toLinearMap).subtype (J.e x) = I.e (x : A.V)
def HtMapInv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A A' B B' : HLat K)
    (I : Iso A A') (J : Iso B B') (φ : A.V →ₗ[K] B.V), FrameOK A → FrameOK B →
    (∀ v, Formalism.HN.opNormAt A'.b A'.X B'.b B'.X v
        (J.e.toLinearMap ∘ₗ φ ∘ₗ I.e.symm.toLinearMap) = Formalism.HN.opNormAt A.b A.X B.b B.X v φ) ∧
    Formalism.HN.htMap A'.b A'.X B'.b B'.X (J.e.toLinearMap ∘ₗ φ ∘ₗ I.e.symm.toLinearMap) =
      Formalism.HN.htMap A.b A.X B.b B.X φ
def EmbNumbers : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A B : HLat K) (ψ : A.V →ₗ[K] B.V),
    FrameOK B → Function.Injective ψ →
    (∀ v x, Formalism.HermitianLatticesTheory.normAt A.b A.X v x = Formalism.HermitianLatticesTheory.normAt B.b B.X v (ψ x)) →
    FrameOK A ∧ ∀ N : Submodule (𝓞 K) A.V,
      (withL A N).rank = (withL B (N.map (ψ.restrictScalars (𝓞 K)))).rank ∧
      (N.FG →
        (withL A N).mu = (withL B (N.map (ψ.restrictScalars (𝓞 K)))).mu ∧
        (withL A N).muMax = (withL B (N.map (ψ.restrictScalars (𝓞 K)))).muMax ∧
        (withL A N).muMin = (withL B (N.map (ψ.restrictScalars (𝓞 K)))).muMin ∧
        (withL A N).lcv = (withL B (N.map (ψ.restrictScalars (𝓞 K)))).lcv)
section Ext
open TensorProduct
variable (K' : Type) {K : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K']
  [StarRing K'] [Algebra K K']
open Classical in

def extFrame {ι : Type} (X : InfinitePlace K → Matrix ι ι ℂ) (v' : InfinitePlace K') :
    Matrix ι ι ℂ :=
  if v'.embedding.comp (algebraMap K K') = (v'.comap (algebraMap K K')).embedding then
    X (v'.comap (algebraMap K K'))
  else (X (v'.comap (algebraMap K K'))).map (starRingEnd ℂ)
@[reducible] def baseChange (A : HLat K) : HLat K' :=
  letI mO : Module (𝓞 K') (K' ⊗[K] A.V) := Module.compHom _ (algebraMap (𝓞 K') K')
  { V := K' ⊗[K] A.V
    modOV := mO
    towV := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ι := A.ι
    b := A.b.baseChange K'
    X := extFrame K' A.X
    L := Submodule.span (𝓞 K') ((fun x => (1 : K') ⊗ₜ[K] x) '' (A.L : Set A.V)) }
end Ext
def ExtBasic : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
    [Algebra K K'] (A : HLat K),
    (FrameOK A → FrameOK (baseChange K' A)) ∧ (A.L.FG → (baseChange K' A).L.FG) ∧
    (baseChange K' A).rank = A.rank ∧ (A.Good → (baseChange K' A).Good) ∧
    ∀ (v' : InfinitePlace K') (x : A.V),
      Formalism.HermitianLatticesTheory.normAt (baseChange K' A).b (baseChange K' A).X v'
                (((1 : K') ⊗ₜ[K] x : TensorProduct K K' A.V) : (baseChange K' A).V) =
        Formalism.HermitianLatticesTheory.normAt A.b A.X (v'.comap (algebraMap K K')) x
def ExtSelf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K),
    ∃ I : Iso (baseChange K A) A, ∀ x : A.V,
      I.e (((1 : K) ⊗ₜ[K] x : TensorProduct K K A.V) : (baseChange K A).V) = x
def ExtInv : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [Field K']
    [NumberField K'] [StarRing K'] [IsTotallyComplex K'] [Algebra K K'] (A : HLat K),
    FrameOK A → A.L.FG → 0 < A.rank →
    (baseChange K' A).mu = A.mu ∧ (baseChange K' A).muMax = A.muMax ∧
    (baseChange K' A).muMin = A.muMin
end Formalism.L2.GlobalTheoryTheory.HLatOps


