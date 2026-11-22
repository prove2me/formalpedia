-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
-- name    : Formalism_LocalToGlobal_IndefiniteForms_IndefSide
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:34.792809+00:00
-- url     : https://prove2.me/theorems/a4b524ab-99eb-4bd6-8c9b-4a691044f00a
-- title:
--   Indef Side
-- statement:
--   Definitions and structural lemmas for Indef Side, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
structure DefBase (K : Type) [Field K] [NumberField K] [StarRing K] where

  K0 : Subfield K

  v0 : InfinitePlace K

  Tup : Type

  μ0 : Tup

  Ix : Type

  fIx : Fintype Ix

  J : Type

  fJ : Fintype J
attribute [instance] DefBase.fIx DefBase.fJ
variable {K : Type} [Field K] [NumberField K] [StarRing K]
structure DefSide (Bs : DefBase K) where

  nV : Bs.Tup → ℕ

  HV : ∀ t, Matrix (Fin (nV t)) (Fin (nV t)) K

  Mt : ∀ t, Submodule (𝓞 K) (Fin (nV t) → K)

  dQ : Bs.Tup → ℕ

  Pq : ∀ t, Matrix (Fin (dQ t)) (Fin (nV t)) K

  XQ : ∀ t, InfinitePlace K → Matrix (Fin (dQ t)) (Fin (dQ t)) ℂ

  Qp : ∀ t, Bs.Ix → Submodule K (Fin (dQ t) → K)

  dZ : Bs.J → Bs.Tup → ℕ

  HT : ∀ j t, Matrix (Fin (dZ j t)) (Fin (dZ j t)) K

  XT : ∀ j t, InfinitePlace K → Matrix (Fin (dZ j t)) (Fin (dZ j t)) ℂ

  Tl : ∀ j t, Submodule (𝓞 K) (Fin (dZ j t) → K)

  Zp : ∀ j t, Bs.Ix → Submodule K (Fin (dZ j t) → K)
namespace DefSide
variable {Bs : DefBase K} (Df : DefSide Bs)
def abelian₂ (t : Bs.Tup) : Submodule (𝓞 K) (Fin (Df.dQ t) → K) := matLat (Df.Pq t) (Df.Mt t)
def U (t : Bs.Tup) : Submodule K (Fin (Df.nV t) → K) := LinearMap.ker (Df.Pq t).mulVecLin
def Gm (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df.dQ t) → Fin (Df.dQ t) → K) (t : Bs.Tup)
    (w : HeightOneSpectrum (𝓞 K)) : K :=
  gramR (quotGram (Df.Pq t) (Df.HV t)) (eb t w)
structure WF : Prop where

  cm : IsCMSub Bs.K0

  conj : IsConjAt Bs.v0

  HV_rat : ∀ t i j, Df.HV t i j ∈ Bs.K0

  HV_pos : ∀ t (v : InfinitePlace K), ((Df.HV t).map v.embedding).PosDef

  Mt_lat : ∀ t, Submodule.IsLattice K (Df.Mt t)

  Pq_surj : ∀ t, Function.Surjective (Df.Pq t).mulVec

  XQ_quot : ∀ t, IsQuotMetric (Df.Pq t) (Df.HV t) (Df.XQ t)

  Lam_lat : ∀ t, Submodule.IsLattice K (Df.abelian₂ t)

  Qp_indep : iSupIndep (Df.Qp Bs.μ0)

  Qp_top : (⨆ p, Df.Qp Bs.μ0 p) = ⊤

  XT_herm : ∀ j t, IsHermAt Bs.v0 (Df.HT j t) (Df.XT j t)

  Tl_lat : ∀ j t, Submodule.IsLattice K (Df.Tl j t)

  Zp_indep : ∀ j, iSupIndep (Df.Zp j Bs.μ0)
def Pos : Prop := 0 < Df.dQ Bs.μ0
def Proviso : Prop := ∀ j, IsRatHerm Bs.K0 (Df.HT j Bs.μ0) (Df.XT j Bs.μ0)
def Types : Prop := ∀ j, (⨆ p, Df.Zp j Bs.μ0 p) = ⊤
end DefSide
structure DefCols {Bs : DefBase K} (Df : DefSide Bs) where

  Mem : Type

  a : Mem → ℕ

  Xc : ∀ u, InfinitePlace K → Matrix (Fin (a u)) (Fin (a u)) ℂ

  Pt : ∀ u t, (Fin (a u) → K) →ₗ[K] Module.Dual K (Fin (Df.nV t) → K)
structure DefAmb (Bs : DefBase K) where

  FR : Bs.Tup → Type

  aR : ∀ t, AddCommGroup (FR t)

  mR : ∀ t, Module K (FR t)

  OpR : Bs.Tup → Type

  opR : ∀ t, OpR t → Module.End K (FR t)

  ZHR : ∀ t, Submodule K (FR t)

  FL : Bs.J → Bs.Tup → Type

  aL : ∀ j t, AddCommGroup (FL j t)

  mL : ∀ j t, Module K (FL j t)

  OpL : Bs.J → Bs.Tup → Type

  opL : ∀ j t, OpL j t → Module.End K (FL j t)

  ZHL : ∀ j t, Submodule K (FL j t)
attribute [instance] DefAmb.aR DefAmb.mR DefAmb.aL DefAmb.mL
structure DefSub {Bs : DefBase K} (A : DefAmb Bs) where

  Z : ∀ t, Submodule K (A.FR t)

  Zl : ∀ j t, Submodule K (A.FL j t)
namespace DefSub
variable {Bs : DefBase K} {A : DefAmb Bs} (Zs : DefSub A)
def Stable : Prop :=
  (∀ t i, (Zs.Z t).map (A.opR t i) ≤ Zs.Z t) ∧ ∀ j t i, (Zs.Zl j t).map (A.opL j t i) ≤ Zs.Zl j t
def InBlock : Prop :=
  (∀ t, Zs.Z t ≤ A.ZHR t) ∧ ∀ j t, Zs.Zl j t ≤ A.ZHL j t
end DefSub
structure SPer {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) where

  HH : Type

  nHH : NormedAddCommGroup HH

  iHH : InnerProductSpace ℂ HH

  Pu : ∀ u, (Fin (Dc.a u) → ℂ) →ₗ[ℂ] HH

  Rw : Submodule ℂ HH
attribute [instance] SPer.nHH SPer.iHH
@[ext] structure IndefNum (Bs : DefBase K) where

  F0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  J0 : Bs.Tup → HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  E1 : Bs.J → ℝ

  l3 : Bs.J → ℝ

  l6 : Bs.J → ℝ

  hh : ℝ

  la : ℝ

  de : ℝ
structure IndefScale (Bs : DefBase K) where

  F0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  J0 : Bs.Tup → HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  E1u : ℝ

  l3m : Bs.J → ℝ

  l3u : ℝ

  l6m : Bs.J → ℝ

  l6u : ℝ

  x : ℝ

  b : ℝ

  la : ℝ

  de : ℝ
def IndefScale.num {Bs : DefBase K} (Z : IndefScale Bs) (C CH : ℝ) : IndefNum Bs where
  F0 := Z.F0
  J0 := Z.J0
  E1 := fun _ => C * Z.E1u
  l3 := fun j => Z.l3m j + C * Z.l3u
  l6 := fun j => Z.l6m j - C * Z.l6u
  hh := Z.x ^ CH * Z.b
  la := Z.la
  de := Z.de
def IsScalarOn {d d' : ℕ} (XS : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (XT : InfinitePlace K → Matrix (Fin d') (Fin d') ℂ) (v : InfinitePlace K)
    (φ : Matrix (Fin d') (Fin d) K) (A : Submodule K (Fin d → K)) (s : ℝ) : Prop :=
  ∀ x ∈ A, ∀ y : Fin d → K,
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d')) XT v (φ.mulVec x) (φ.mulVec y) =
      (s : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XS v x y
structure IndefData {Bs : DefBase K} (Df : DefSide Bs) where

  μ : HeightOneSpectrum (𝓞 K) → Bs.Tup

  Tw : Finset (HeightOneSpectrum (𝓞 K))

  D : ℕ

  XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ

  Ep : Bs.Ix → Submodule K (Fin D → K)

  ι : ∀ t, Matrix (Fin D) (Fin (Df.dQ t)) K

  dW : Bs.J → ℕ

  XW : ∀ j, InfinitePlace K → Matrix (Fin (dW j)) (Fin (dW j)) ℂ

  Wp : ∀ j, Bs.Ix → Submodule K (Fin (dW j) → K)

  M : ∀ j, Submodule (𝓞 K) (Fin (dW j) → K)

  θ : ∀ j t, Matrix (Fin (dW j)) (Fin (Df.dZ j t)) K

  κ : InfinitePlace K → ℝ

  lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ

  err0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ
namespace IndefData
variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df)
def Iw (j : Bs.J) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) : ℤ :=
  idx w (S.M j) (matLat (S.θ j t) (Df.Tl j t))
def Aw (j : Bs.J) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (conjPl w) : ℝ) + (jw (Df.HT j (S.μ w)) w (Df.Tl j (S.μ w)) : ℝ)
def RR : Submodule (𝓞 K) (Fin S.D → K) :=
  glueLat fun w => matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))
def muCC : ℝ :=
  Formalism.HN.muDef (Pi.basisFun K (Fin S.D)).dualBasis (Formalism.HN.dualFrame S.XE) (Formalism.HN.dualLat S.RR)
def muMaxRR : ℝ := Formalism.HN.muMaxDef (Pi.basisFun K (Fin S.D)) S.XE S.RR
def Qpart (t : Bs.Tup) (p : Bs.Ix) : Submodule K (Fin (Df.dQ t) → K) := (S.Ep p).comap (S.ι t).mulVecLin
def Zpart (j : Bs.J) (t : Bs.Tup) (p : Bs.Ix) : Submodule K (Fin (Df.dZ j t) → K) :=
  (S.Wp j p).comap (S.θ j t).mulVecLin
def H0 : Prop :=
  (∀ w, S.μ (conjPl w) = S.μ w) ∧ ∀ w, w ∈ S.Tw ↔ S.μ w ≠ Bs.μ0
def Frames : Prop :=
  (∀ v, IsUnit (S.XE v).det) ∧ (∀ j v, IsUnit (S.XW j v).det) ∧ ∀ j, Submodule.IsLattice K (S.M j)
def BaseTypeSubspacesMapOntoBothSides : Prop :=
  (∀ p, (Df.Qp Bs.μ0 p).map (S.ι Bs.μ0).mulVecLin = S.Ep p) ∧
    ∀ j p, (Df.Zp j Bs.μ0 p).map (S.θ j Bs.μ0).mulVecLin = S.Wp j p
def RowLatticeBoundForBasis : Prop :=
  (∀ t, Function.Bijective (S.ι t).mulVec) ∧ (∀ j t, Function.Bijective (S.θ j t).mulVec) ∧
  (∀ v, 0 < S.κ v) ∧ (∀ j t p v, 0 < S.lam j t p v) ∧
  (∀ t v, (t = Bs.μ0 ∨ v = Bs.v0) → ∀ p,
    IsScalarOn (Df.XQ t) S.XE v (S.ι t) (S.Qpart t p) (S.κ v * ∏ j, S.lam j t p v)) ∧
  ∀ j t v, (t = Bs.μ0 ∨ v = Bs.v0) → ∀ p,
    IsScalarOn (Df.XT j t) (S.XW j) v (S.θ j t) (S.Zpart j t p) (S.lam j t p v)
def DimensionsOfPartsAgree : Prop :=
  ∀ j p, finrank K (S.Wp j p) = finrank K (S.Ep p)
def L3 (N : IndefNum Bs) : Prop :=
  ∀ j, lcv (S.XW j) (S.M j) / (S.D : ℝ) ≤ N.l3 j
def ON (N : IndefNum Bs) : Prop :=
  (∀ w ∈ S.Tw, ∑ j, ((S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (conjPl w) : ℝ)) ≤
    (∑ j, (2 * ((ramw w : ℝ) * N.F0 w j) + (ramw w : ℝ) * S.err0 w j) +
      (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) * (S.D : ℝ)) ∧
  (∀ w ∈ S.Tw, ∀ j, 0 ≤ S.err0 w j) ∧
  ∀ j, ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * S.err0 w j + (ramw w : ℝ) * N.J0 (S.μ w) w j) ≤ N.E1 j
def L6 (N : IndefNum Bs) : Prop :=
  ∀ j p v, N.l6 j ≤ Real.log (S.lam j Bs.μ0 p v)
def Untwisted (N : IndefNum Bs) : Prop :=
  ∀ w, w ∉ S.Tw → ∀ j, S.Aw j w = 0 ∧ N.F0 w j = 0
def FUN (N : IndefNum Bs) : Prop :=
  S.muMaxRR ≤ N.hh - meanLog S.κ
end IndefData
def LevelLink {Bs : DefBase K} {Df Df' : DefSide Bs} (S : IndefData Df) (S' : IndefData Df') : Prop :=
  S.μ = S'.μ ∧ S.κ = S'.κ ∧ S.lam = S'.lam
def Passage {Bs : DefBase K} {Df Df' : DefSide Bs} (N : IndefNum Bs) (S : IndefData Df) (S' : IndefData Df') :
    Prop :=
  0 ≤ N.de → N.de ≤ 1 / 3 → ∀ HH0 : ℝ, S.muMaxRR ≤ HH0 →
    S'.muMaxRR ≤ HH0 + 14 * N.la ∧
      S'.muCC ≤ S.muCC + 3 * N.de * (S.muCC + HH0 + 28 * N.la) + 28 * N.la
structure IndefRows {Bs : DefBase K} (Df : DefSide Bs) extends IndefData Df where

  pos : Df.Pos

  proviso : Df.Proviso

  types : Df.Types

  h0 : toIndefData.H0

  frames : toIndefData.Frames

  l1a : toIndefData.BaseTypeSubspacesMapOntoBothSides

  l1c : toIndefData.RowLatticeBoundForBasis

  l1d : toIndefData.DimensionsOfPartsAgree
structure IndefSide {Bs : DefBase K} (Df : DefSide Bs) (N : IndefNum Bs) extends IndefRows Df where

  l3 : toIndefData.L3 N

  on : toIndefData.ON N
structure ColData {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (Sp : SPer Dc) (S : IndefData Df) where

  B : ∀ u, (Fin (Dc.a u) → K) →ₗ[K] Module.Dual K (Fin S.D → K)

  ζ : Dc.Mem → Bs.Tup → K

  sE : (Fin S.D → ℂ) →ₗ⋆[ℂ] Sp.HH
namespace ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)
def bes (u : Dc.Mem) (x : Fin (Dc.a u) → ℂ) (y : Fin S.D → ℂ) : ℂ := ⟪C.sE y, Sp.Pu u x⟫_ℂ
def PairingFactorsThroughPeriods : Prop :=
  (∀ u t (φ : Fin (Dc.a u) → K) (F : Fin (Df.nV t) → K),
    Dc.Pt u t φ F = C.ζ u t * C.B u φ ((S.ι t).mulVec ((Df.Pq t).mulVec F))) ∧
  (∀ u, C.ζ u Bs.μ0 = 1) ∧ (∀ u t, C.ζ u t ≠ 0) ∧ ∀ u w, vw w (C.ζ u (S.μ w)) = 0
def L1e : Prop :=
  (∀ y, ‖C.sE y‖ = fnorm (S.XE Bs.v0) y) ∧ (∀ y, C.sE y ∈ Sp.Rw) ∧ Module.finrank ℂ Sp.Rw = S.D ∧
  ∃ V : Matrix (Fin S.D) (Fin S.D) ℂ, (∀ y, fnorm (S.XE Bs.v0) (V.mulVec y) = fnorm (S.XE Bs.v0) y) ∧
    ∀ u, ∃ a : ℂ, a ≠ 0 ∧ ∃ U : Matrix (Fin (Dc.a u)) (Fin (Dc.a u)) ℂ,
      (∀ x, fnorm (Dc.Xc u Bs.v0) (U.mulVec x) = fnorm (Dc.Xc u Bs.v0) x) ∧
      ∀ (x : Fin (Dc.a u) → ℂ) (y : Fin S.D → ℂ),
        pairC Bs.v0 (C.B u) x y = a * C.bes u (U.mulVec x) (V.mulVec y)
end ColData
structure IndefCols {Bs : DefBase K} (Df : DefSide Bs) (Dc : DefCols Df) (Sp : SPer Dc) (N : IndefNum Bs)
    extends IndefRows Df where

  l6 : toIndefData.L6 N

  col : ColData Dc Sp toIndefData

  l1b : col.PairingFactorsThroughPeriods

  l1e : col.L1e
structure IndefExtra {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
    (S0 : IndefSide Df0 N) (S1 : IndefCols Df1 Dc Sp N) : Prop where

  untw : S0.toIndefData.Untwisted N

  level : LevelLink S0.toIndefData S1.toIndefData

  passage : Passage N S0.toIndefData S1.toIndefData

  fun0 : S0.toIndefData.FUN N
structure IndefCore {Bs : DefBase K} (Df0 Df1 : DefSide Bs) (Dc : DefCols Df1) (Sp : SPer Dc) (N : IndefNum Bs) where

  base : IndefSide Df0 N

  cols : IndefCols Df1 Dc Sp N

  extra : IndefExtra base cols
structure DefFace (Bs : DefBase K) where

  Df0 : DefSide Bs

  Df1 : DefSide Bs

  Dc : DefCols Df1

  Sp : SPer Dc

  Z : IndefScale Bs
structure IndefPkg {Bs : DefBase K} (A : DefAmb Bs) (fc : DefSub A → DefFace Bs) (C CH : ℝ) where

  Zs : DefSub A

  stable : Zs.Stable

  inBlock : Zs.InBlock

  core : IndefCore (fc Zs).Df0 (fc Zs).Df1 (fc Zs).Dc (fc Zs).Sp ((fc Zs).Z.num C CH)
structure IndefFace where

  K : Type

  [fK : Field K]

  [nK : NumberField K]

  [sK : StarRing K]

  [tK : IsTotallyComplex K]

  Bs : DefBase K

  A : DefAmb Bs

  fc : DefSub A → DefFace Bs
attribute [instance] IndefFace.fK IndefFace.nK IndefFace.sK IndefFace.tK
def IndefLink (Ix : ℝ → Type) (F : ∀ x, Ix x → IndefFace) (CH : ℝ)
    (Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Ix x, ∃ P : IndefPkg (F x i).A (F x i).fc C CH, Q x i C P.Zs P.core.base.μ
end Formalism.L2.Indef


