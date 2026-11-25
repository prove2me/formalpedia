-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RestNonneg
-- name    : Formalism_LocalToGlobal_CharacterGerms_RestNonneg
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:30.182619+00:00
-- url     : https://prove2.me/theorems/7a147232-ed70-4ba4-b5c0-bc13958755c9
-- title:
--   Rest Nonneg
-- statement:
--   Definitions and structural lemmas for Rest Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RestNonneg.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
def i0 (k l : ℕ) : ℕ := sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}
structure Par : Type 1 where
  Pl : Type
  [fPl : Fintype Pl]
  k : ℕ
  m : ℕ
  r : ℕ
  f : ℕ
  d : ℕ
  [nz : NeZero d]
  pos : Pl → ℕ → Pl
  w : Pl → ℝ
  SE : ℝ
attribute [instance] Par.fPl Par.nz
def IsReps (P : Par) (Z : Finset P.Pl) : Prop :=
  ∀ z' : P.Pl, ∃! p : P.Pl × ZMod P.d, p.1 ∈ Z ∧ P.pos p.1 p.2.val = z'
def alongOrb {X : Type} (P : Par) (z : P.Pl) (W : P.Pl → X) : ZMod P.d → X :=
  fun s => W (P.pos z s.val)
structure DegHyp2 (P : Par) (W : P.Pl → ℕ) (T θ0 rest C1 : ℝ) : Prop where
  T_one : 1 ≤ T
  w_pos : ∀ z, 0 < P.w z
  TW_lo : ∀ z, (1 - θ0) * P.w z ≤ T * W z
  TW_hi : ∀ z, T * W z ≤ P.w z + C1 * P.SE
  th_rng : 0 ≤ θ0 ∧ θ0 ≤ 1
  th_m : ((P.k : ℝ) - 1) * θ0 ≤ 5 * P.m
  rest_nonneg : 0 ≤ rest
  rest_le : T * rest ≤ C1 * (P.f * P.k * P.SE)
structure RowFam (P : Par) (l d : ℕ) [NeZero d] : Type 1 where
  C : Type
  [fC : Field C]
  V : VF C
  hVl : V.l = l
  I : P.Pl → Fin 2 → Type
  J : P.Pl → Fin 2 → Type
  [fI : ∀ o g, Fintype (I o g)]
  [fJ : ∀ o g, Fintype (J o g)]
  X : ∀ z, RowData C V d (I z) (J z)
  F : ∀ z, Flag (X z)
  hn : ∀ z, (X z).n = P.k - 1 ∧ (X z).m = P.m
attribute [instance] RowFam.fC RowFam.fI RowFam.fJ
structure PkgInert (P : Par) (l : ℕ) (C1 : ℝ) : Type 1 where
  R : RowFam P l P.d
  Z : Finset P.Pl
  hZ : IsReps P Z
  alt : ∀ z ∈ Z, (R.X z).Alt
  ga : P.Pl → Fin 2 → ZMod P.d → ℕ → ℕ
  W : P.Pl → ℕ
  nW : ℕ
  T : ℝ
  θ0 : ℝ
  rest : ℝ
  ν : ℝ
  wt : WtHyp P.k P.r Z bg (fun z => (R.X z).rkF) ga (fun z => alongOrb P z W) (fun _ _ => 0) rest
  what₂ : P.f * (i0 P.k l * (P.k - 1)) + 2 * P.r * P.f ≤ nW
  deg : DegHyp2 P W T θ0 rest C1
  val : @ValBlocks R.C R.fC R.V P.d _ P.Pl _ R.I R.J R.fI R.fJ R.X R.F Z nW ga ν
structure PkgPhiC (P : Par) (l : ℕ) (C1 : ℝ) : Type 1 where
  R : RowFam P l 2
  alt : ∀ z, (R.X z).Alt
  gaC : P.Pl → ZMod 2 → ℕ → ℕ
  W : P.Pl → ℕ
  nW : ℕ
  T : ℝ
  θ0 : ℝ
  rest : ℝ
  ν : ℝ
  supp : ∀ z s k, gaC z s k ≠ 0 → 1 ≤ k ∧ k ≤ (R.X z).rkF 0 s
  main : ∀ z, gaC z 0 (P.k - 1) = W z
  rest_eq : rest = ∑ z, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 P.r,
    (if s = 0 ∧ k = P.k - 1 then (0 : ℝ) else (k : ℝ) * gaC z s k)
  what₂ : 8 * P.r * P.f ≤ nW
  deg : DegHyp2 P W T θ0 rest C1
  val : @ValBlocksC R.C R.fC R.V P.Pl _ R.I R.J R.fI R.fJ R.X R.F nW gaC ν
structure PkgSplit (P : Par) (l : ℕ) (C1 : ℝ) : Type 1 where
  R : RowFam P l P.d
  Z : Finset P.Pl
  hZ : IsReps P Z
  allBig : ∀ z ∈ Z, ∀ a, (R.X z).big 0 a
  ga : P.Pl → Fin 2 → ZMod P.d → ℕ → ℕ
  W : P.Pl → ℕ
  nW : ℕ
  T : ℝ
  θ0 : ℝ
  rest : ℝ
  ν : ℝ
  wt : WtHyp P.k P.r Z (fun _ => 0) (fun z => (R.X z).rkF) ga (fun z => alongOrb P z W)
    (fun _ _ => 0) rest
  what₂ : 4 * P.r * P.f ≤ nW
  deg : DegHyp2 P W T θ0 rest C1
  val : @ValBlocks R.C R.fC R.V P.d _ P.Pl _ R.I R.J R.fI R.fJ R.X R.F Z nW ga ν
structure PkgZero (P : Par) (l : ℕ) : Type 1 where
  R : RowFam P l P.d
  Z : Finset P.Pl
  hZ : IsReps P Z
  ga : P.Pl → Fin 2 → ZMod P.d → ℕ → ℕ
  K : ℕ
  s : ℕ
  nW : ℕ
  T : ℝ
  ν : ℝ
  T_one : 1 ≤ T
  w_nonneg : ∀ z, 0 ≤ P.w z
  supp : ∀ z ∈ Z, ∀ g a k, ga z g a k ≠ 0 → 1 ≤ k ∧ k ≤ (R.X z).rkF g a ∧ k ≤ K
  first : ∀ z ∈ Z, ∀ g a, ∑ k ∈ Finset.Icc 1 K, ga z g a k ≤ s * (l - 1)
  what₂ : 2 * K * s * Z.card ≤ nW
  val : @ValBlocks R.C R.fC R.V P.d _ P.Pl _ R.I R.J R.fI R.fJ R.X R.F Z nW ga ν
structure PkgZeroC (P : Par) (l : ℕ) : Type 1 where
  R : RowFam P l 2
  gaC : P.Pl → ZMod 2 → ℕ → ℕ
  K : ℕ
  s : ℕ
  nW : ℕ
  T : ℝ
  ν : ℝ
  T_one : 1 ≤ T
  w_nonneg : ∀ z, 0 ≤ P.w z
  supp : ∀ z σ k, gaC z σ k ≠ 0 → 1 ≤ k ∧ k ≤ (R.X z).rkF 0 σ ∧ k ≤ K
  first : ∀ z σ, ∑ k ∈ Finset.Icc 1 K, gaC z σ k ≤ s * (l - 1)
  what₂ : 4 * K * s * Fintype.card P.Pl ≤ nW
  val : @ValBlocksC R.C R.fC R.V P.Pl _ R.I R.J R.fI R.fJ R.X R.F nW gaC ν
end Formalism.L2.FormalSeriesBounds.RF


