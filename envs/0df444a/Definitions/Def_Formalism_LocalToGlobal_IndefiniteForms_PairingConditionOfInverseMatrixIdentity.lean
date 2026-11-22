-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
-- name    : Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:17.694199+00:00
-- url     : https://prove2.me/theorems/57b57d1e-952f-4756-9ea8-a7f0dea8b733
-- title:
--   Pairing Condition Of Inverse Matrix Identity
-- statement:
--   Definitions and structural lemmas for Pairing Condition Of Inverse Matrix Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)
def invZ : ColData Dc Sp S where
  B := C.B
  ζ := fun u t => (C.ζ u t)⁻¹
  sE := C.sE
def MatrixIdentityOffBase : Prop :=
  (∀ u t (φ : Fin (Dc.a u) → K) (F : Fin (Df.nV t) → K),
    C.ζ u t * Dc.Pt u t φ F = C.B u φ ((S.ι t).mulVec ((Df.Pq t).mulVec F))) ∧
  (∀ u, C.ζ u Bs.μ0 = 1) ∧ (∀ u t, C.ζ u t ≠ 0) ∧
  ∀ u w, vw w (C.ζ u (S.μ w)) = 0 ∧ vw (conjPl w) (C.ζ u (S.μ w)) = 0
end ColData
structure ConvFace (Bs : DefBase K) where

  primes : Prop

  symLevel : Prop

  sg0 : K →+* ℂ

  Hk : Type

  ev : Bs.Ix → Hk → K

  ev_inj : Function.Injective ev
structure IndefConv (Bs : DefBase K) (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup) (cf : ConvFace Bs) : Prop where

  c1 : cf.primes

  c2 : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, μ w = t

  c3 : cf.symLevel

  c4 : Bs.v0.embedding = cf.sg0
structure HeckeRows {Bs : DefBase K} (cf : ConvFace Bs) {Df : DefSide Bs} (S : IndefData Df) where

  hE : cf.Hk → Module.End K (Fin S.D → K)

  eigE : ∀ c, S.Ep c = ⨅ T, LinearMap.ker (hE T - cf.ev c T • LinearMap.id)
structure HeckeAll {Bs : DefBase K} (cf : ConvFace Bs) {Df : DefSide Bs} (S : IndefData Df) extends HeckeRows cf S where

  hW : ∀ j, cf.Hk → Module.End K (Fin (S.dW j) → K)

  eigW : ∀ j c, S.Wp j c = ⨅ T, LinearMap.ker (hW j T - cf.ev c T • LinearMap.id)
structure IndefPkg2 {Bs : DefBase K} (A : DefAmb Bs) (fc : DefSub A → DefFace Bs) (cf : ConvFace Bs) (C CH : ℝ)
    extends IndefPkg A fc C CH where

  conv : IndefConv Bs toIndefPkg.core.base.μ cf

  heckeB : HeckeAll cf toIndefPkg.core.base.toIndefData

  heckeC : HeckeAll cf toIndefPkg.core.cols.toIndefData
abbrev IndefPkg2.forget {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (P : IndefPkg2 A fc cf C CH) : IndefPkg A fc C CH :=
  P.toIndefPkg
structure IndefFace2 extends IndefFace where

  cf : ConvFace Bs
def IndefLink2 (Ix : ℝ → Type) (F : ∀ x, Ix x → IndefFace2) (CH : ℝ)
    (Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Ix x, ∃ P : IndefPkg2 (F x i).A (F x i).fc (F x i).cf C CH, Q x i C P.Zs P.core.base.μ
namespace IndefPkg2
variable {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
  (P : IndefPkg2 A fc cf C CH)
end IndefPkg2
namespace IndefData
variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df)
def FramesR : Prop := ∀ v, IsUnit (S.XE v).det
def BaseTypeSubspacesMapOnto : Prop := ∀ p, (Df.Qp Bs.μ0 p).map (S.ι Bs.μ0).mulVecLin = S.Ep p
def BijectivityAndPositivity : Prop :=
  (∀ t, Function.Bijective (S.ι t).mulVec) ∧ (∀ v, 0 < S.κ v) ∧ (∀ j t p v, 0 < S.lam j t p v) ∧
  ∀ t v, (t = Bs.μ0 ∨ v = Bs.v0) → ∀ p,
    IsScalarOn (Df.XQ t) S.XE v (S.ι t) (S.Qpart t p) (S.κ v * ∏ j, S.lam j t p v)
end IndefData
structure IndefColsR {Bs : DefBase K} (Df : DefSide Bs) (Dc : DefCols Df) (Sp : SPer Dc) (N : IndefNum Bs)
    extends IndefData Df where

  pos : Df.Pos

  h0 : toIndefData.H0

  frames : toIndefData.FramesR

  l1a : toIndefData.BaseTypeSubspacesMapOnto

  l1c : toIndefData.BijectivityAndPositivity

  l6 : toIndefData.L6 N

  col : ColData Dc Sp toIndefData

  l1b : col.PairingFactorsThroughPeriods

  l1e : col.L1e
structure IndefExtraR {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
    (S0 : IndefSide Df0 N) (S1 : IndefColsR Df1 Dc Sp N) : Prop where

  untw : S0.toIndefData.Untwisted N

  level : LevelLink S0.toIndefData S1.toIndefData

  passage : Passage N S0.toIndefData S1.toIndefData

  fun0 : S0.toIndefData.FUN N
structure IndefCoreR {Bs : DefBase K} (Df0 Df1 : DefSide Bs) (Dc : DefCols Df1) (Sp : SPer Dc) (N : IndefNum Bs) where

  base : IndefSide Df0 N

  cols : IndefColsR Df1 Dc Sp N

  extra : IndefExtraR base cols
structure IndefPkgR {Bs : DefBase K} (A : DefAmb Bs) (fc : DefSub A → DefFace Bs) (cf : ConvFace Bs) (C CH : ℝ) where

  Zs : DefSub A

  stable : Zs.Stable

  inBlock : Zs.InBlock

  core : IndefCoreR (fc Zs).Df0 (fc Zs).Df1 (fc Zs).Dc (fc Zs).Sp ((fc Zs).Z.num C CH)

  conv : IndefConv Bs core.base.μ cf

  heckeB : HeckeAll cf core.base.toIndefData

  heckeC : HeckeRows cf core.cols.toIndefData
def IndefCols.toR {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    (S : IndefCols Df Dc Sp N) : IndefColsR Df Dc Sp N where
  toIndefData := S.toIndefData
  pos := S.pos
  h0 := S.h0
  frames := S.frames.1
  l1a := S.l1a.1
  l1c := ⟨S.l1c.1, S.l1c.2.2.1, S.l1c.2.2.2.1, S.l1c.2.2.2.2.1⟩
  l6 := S.l6
  col := S.col
  l1b := S.l1b
  l1e := S.l1e
def IndefCore.toR {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
    (P : IndefCore Df0 Df1 Dc Sp N) : IndefCoreR Df0 Df1 Dc Sp N where
  base := P.base
  cols := P.cols.toR
  extra := ⟨P.extra.untw, P.extra.level, P.extra.passage, P.extra.fun0⟩
def IndefPkg2.toR {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (P : IndefPkg2 A fc cf C CH) : IndefPkgR A fc cf C CH where
  Zs := P.Zs
  stable := P.stable
  inBlock := P.inBlock
  core := P.core.toR
  conv := P.conv
  heckeB := P.heckeB
  heckeC := P.heckeC.toHeckeRows
def IndefLinkR (Ix : ℝ → Type) (F : ∀ x, Ix x → IndefFace2) (CH : ℝ)
    (Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Ix x, ∃ P : IndefPkgR (F x i).A (F x i).fc (F x i).cf C CH, Q x i C P.Zs P.core.base.μ
namespace IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)
end IndefColsR
namespace IndefCoreR
variable {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
  (P : IndefCoreR Df0 Df1 Dc Sp N)
include P
end IndefCoreR
end Formalism.L2.Indef


