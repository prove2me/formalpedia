-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
-- name    : Formalism_LocalToGlobal_Divisibility_Frames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:26.899801+00:00
-- url     : https://prove2.me/theorems/f53075d8-a583-4e08-b921-dde7500ed119
-- title:
--   Frames
-- statement:
--   Definitions and structural lemmas for Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/Frames.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section OnePlace
variable {n d : ℕ}
def metOf (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (Y⁻¹)ᴴ * Y⁻¹
def frameOf (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (CFC.sqrt A)⁻¹
def quotMetC (P : Matrix (Fin d) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (P * A⁻¹ * Pᴴ)⁻¹
def restrMetC (C : Matrix (Fin n) (Fin d) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Cᴴ * A * C
end OnePlace
section AllPlaces
variable {K : Type} [Field K] [NumberField K] {n d D : ℕ}
def stdFrame (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => frameOf (H.map v.embedding)
def quotFrame (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K) :
    InfinitePlace K → Matrix (Fin D) (Fin D) ℂ :=
  fun v => frameOf (quotMetC (P.map v.embedding) (H.map v.embedding))
def restrFrame (E : Matrix (Fin n) (Fin d) K) (H : Matrix (Fin n) (Fin n) K) :
    InfinitePlace K → Matrix (Fin d) (Fin d) ℂ :=
  fun v => frameOf (restrMetC (E.map v.embedding) (H.map v.embedding))
def weightMet {Ix : Type} [Fintype Ix] (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, ((t p v : ℝ) : ℂ) • restrMetC ((pr p).map v.embedding) (metOf (X v))
def weightFrame {Ix : Type} [Fintype Ix] (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => frameOf (weightMet pr t X v)
def pushFrame (φ : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => φ.map v.embedding * X v
open Classical in

def spliceFrame (v0 : InfinitePlace K) (Y : Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  Function.update X v0 Y
def rowFrame {Ix : Type} [Fintype Ix] (v0 : InfinitePlace K) (Y : Matrix (Fin n) (Fin n) ℂ)
    (φ : Matrix (Fin n) (Fin n) K) (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  spliceFrame v0 Y (pushFrame φ (weightFrame pr t X))
def toHLat [StarRing K] (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (L : Submodule (𝓞 K) (Fin d → K)) : Formalism.BasicNotions.HLat K where
  V := Fin d → K
  ι := Fin d
  b := Pi.basisFun K (Fin d)
  X := X
  L := L
end AllPlaces
def FrameOfSpec : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    IsUnit (frameOf A).det ∧ metOf (frameOf A) = A
def FrameOfEqZeroOfNotPosDef : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), ¬ A.PosDef → frameOf A = 0
def MetOfSpec : Prop :=
  ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), IsUnit Y.det →
    (metOf Y).PosDef ∧ (metOf Y)⁻¹ = Y * Yᴴ ∧ metOf (frameOf (metOf Y)) = metOf Y
def QuotRestrPosDef : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    (∀ P : Matrix (Fin d) (Fin n) ℂ, Function.Surjective P.mulVec → (quotMetC P A).PosDef) ∧
    (∀ C : Matrix (Fin n) (Fin d) ℂ, Function.Injective C.mulVec → (restrMetC C A).PosDef)
def QuotEqRestrC : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    ∀ (C : Matrix (Fin n) (Fin d) ℂ) (P : Matrix (Fin d) (Fin n) ℂ), P * C = 1 →
      Cᴴ * A * (1 - C * P) = 0 → quotMetC P A = restrMetC C A
def StdFrameRatHerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K) (n : ℕ)
    (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) → IsRatHerm K0 H (stdFrame H)
def StdFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v0 : InfinitePlace K) (n : ℕ)
    (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) → IsHermAt v0 H (stdFrame H)
def QuotFrameIsQuot : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D : ℕ) (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (quotFrame P H)
def RestrFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
    ∀ v : InfinitePlace K, IsUnit (restrFrame E H v).det ∧
      metOf (restrFrame E H v) = restrMetC (E.map v.embedding) (H.map v.embedding) ∧
      ∀ x y : Fin d → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) (restrFrame E H) v x y =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (stdFrame H) v (E.mulVec x) (E.mulVec y)
def RestrFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
      IsHermAt v0 (Eᴴ * H * E) (restrFrame E H)
def RestrFrameRatHerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    (∀ a ∈ K0, star a ∈ K0) →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec → (∀ i a, E i a ∈ K0) →
      IsRatHerm K0 (Eᴴ * H * E) (restrFrame E H) ∧ restrFrame E H = stdFrame (Eᴴ * H * E)
def QuotEqRestrAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (H.map v0.embedding).PosDef →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      quotFrame Pr H v0 = restrFrame E H v0
def QuotEqRestrRat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), (∀ i a, E i a ∈ K0) →
      IsOrthProj H E Pr → quotFrame Pr H = restrFrame E H
def QuotFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      IsHermAt v0 (Eᴴ * H * E) (quotFrame Pr H)
def RestrFormGram : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (E : Matrix (Fin n) (Fin d) K), Eᴴ * H * E = gramMat H (fun a i => E i a)
def WeightFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Ix : Type) [Fintype Ix]
    (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
    (∀ p v, 0 < t p v) → ∑ p, pr p = 1 →
    ∀ v : InfinitePlace K, IsUnit (weightFrame pr t X v).det ∧
      metOf (weightFrame pr t X v) = weightMet pr t X v ∧
      ∀ x y : Fin n → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (weightFrame pr t X) v x y =
        ∑ p, ((t p v : ℝ) : ℂ) *
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v ((pr p).mulVec x) ((pr p).mulVec y)
def WeightFramePart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Ix : Type) [Fintype Ix]
    (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
    (∀ p v, 0 < t p v) → ∑ p, pr p = 1 → (∀ p q, p ≠ q → pr p * pr q = 0) →
    ∀ v : InfinitePlace K,
    (∀ p q, p ≠ q → ∀ x y : Fin n → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v ((pr p).mulVec x) ((pr q).mulVec y) = 0) →
    ∀ (p : Ix) (x y : Fin n → K), (pr p).mulVec x = x →
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (weightFrame pr t X) v x y =
        ((t p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y
def PushFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (φ : Matrix (Fin n) (Fin n) K),
    IsUnit φ.det → ∀ X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ v : InfinitePlace K, IsUnit (pushFrame φ X v).det ∧
      (∀ x y : Fin n → K,
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (pushFrame φ X) v (φ.mulVec x) (φ.mulVec y) =
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y) ∧
      detRatio X (pushFrame φ X) φ v = 1
def SpliceFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v0 : InfinitePlace K)
    (Y : Matrix (Fin n) (Fin n) ℂ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    spliceFrame v0 Y X v0 = Y ∧ ∀ v, v ≠ v0 → spliceFrame v0 Y X v = X v
def RowFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Ix : Type) [Fintype Ix]
    (v0 : InfinitePlace K) (Y : Matrix (Fin n) (Fin n) ℂ), IsUnit Y.det →
    ∀ φ : Matrix (Fin n) (Fin n) K, IsUnit φ.det →
    ∀ (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
    (∀ p v, 0 < t p v) → ∑ p, pr p = 1 → (∀ p q, p ≠ q → pr p * pr q = 0) →
    (∀ v, IsUnit (rowFrame v0 Y φ pr t X v).det) ∧ rowFrame v0 Y φ pr t X v0 = Y ∧
    ∀ v : InfinitePlace K, v ≠ v0 →
    (∀ p q, p ≠ q → ∀ x y : Fin n → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v ((pr p).mulVec x) ((pr q).mulVec y) = 0) →
    ∀ (p : Ix) (x y : Fin n → K), (pr p).mulVec x = x →
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (rowFrame v0 Y φ pr t X) v (φ.mulVec x) (φ.mulVec y) =
        ((t p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y
def DualFrameMet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ v, metOf (Formalism.HN.dualFrame X v) = ((metOf (X v))⁻¹)ᵀ
def FrameIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (X X2 : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    (∀ v, IsUnit (X2 v).det) → (∀ v, metOf (X v) = metOf (X2 v)) →
    (∀ v (x y : Fin d → K), Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X2 v x y) ∧
    ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG →
      lcv X L = lcv X2 L ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X L = Formalism.HN.muDef (Pi.basisFun K (Fin d)) X2 L ∧
      Formalism.HN.muMaxDef (Pi.basisFun K (Fin d)) X L = Formalism.HN.muMaxDef (Pi.basisFun K (Fin d)) X2 L ∧
      Formalism.HN.muMinDef (Pi.basisFun K (Fin d)) X L = Formalism.HN.muMinDef (Pi.basisFun K (Fin d)) X2 L
def ToHLatSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (L : Submodule (𝓞 K) (Fin d → K)),
    (toHLat X L).lcv = lcv X L ∧
    (toHLat X L).mu = Formalism.HN.muDef (Pi.basisFun K (Fin d)) X L ∧
    (toHLat X L).muMax = Formalism.HN.muMaxDef (Pi.basisFun K (Fin d)) X L ∧
    (toHLat X L).muMin = Formalism.HN.muMinDef (Pi.basisFun K (Fin d)) X L ∧
    (toHLat X L).dualL = Formalism.HN.dualLat L ∧
    (toHLat X L).dualX = Formalism.HN.dualFrame X ∧
    ((toHLat X L).Good ↔ (∀ v, IsUnit (X v).det) ∧ Submodule.IsLattice K L)
end Formalism.L2.DIV


