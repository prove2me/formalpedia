-- Prove2me | Definitions.Def_Yukon_1d12cd42de48e1c5386cddc7
-- name    : Yukon_1d12cd42de48e1c5386cddc7
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:36.380974+00:00
-- url     : https://prove2.me/theorems/df91ce62-3694-4fe1-bdbd-ce90ed8b790f
-- title:
--   YukonModule.CompPoly.Univariate.NTT.KoalaBear.part0
-- statement:
--   Source module CompPoly.Univariate.NTT.KoalaBear.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Univariate/NTT/KoalaBear.lean
--
--   yukon-proof-operation:b9123b4ba0905f77a4675920436d3e40ef94a1c4dec811961b3f4a3283ccb6bc
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YjkxMjNiNGJhMDkwNWY3N2E0Njc1OTIwNDM2ZDNlNDBlZjk0YTFjNGRlYzgxMTk2MWIzZjRhMzI4M2NjYjZiYyIsImhhc2giOiI1NDkwMDU2YjJiOTBkMzQwZTZiOTRjOWM1ZDVlODkwN2RkZjI2ZjczODI5MjYyNzkwYmI4MTAxNjVhNDE2NTUxIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8xZDEyY2Q0MmRlNDhlMWM1Mzg2Y2RkYzciLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import Definitions.Def_Yukon_9e16b2bd8a44fd5b9c05fbe2

public import Definitions.Def_Yukon_cdb86a7d352f997352680dd3



public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.Nat.Log
public import Init.Data.Vector.OfFn
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Cases
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.GroupWithZero.Nat
public import Init
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.ReduceModChar
public import Definitions.Def_Yukon_db9e62887577419e408bc32c
meta import Definitions.Def_Yukon_db9e62887577419e408bc32c
meta import Definitions.Def_Yukon_9e16b2bd8a44fd5b9c05fbe2
meta import Definitions.Def_Yukon_cdb86a7d352f997352680dd3
set_option backward.isDefEq.respectTransparency.types false
/-!
# KoalaBear NTT Domains

Concrete radix-2 NTT domains over the KoalaBear field.
-/

@[expose] public section

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace KoalaBear

/-- Build a finite index into the KoalaBear two-adic generator table. -/
def bitsOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Fin (KoalaBear.twoAdicity + 1) :=
  ⟨logN, Nat.lt_succ_of_le hlogN⟩

/-- KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def domainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Domain KoalaBear.Field where
  logN := logN
  omega := KoalaBear.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    simpa [bitsOfLogN] using
      KoalaBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)

/-- KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def bestDomainForLength? (requiredLen : Nat) :
    Option (FittingDomain KoalaBear.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? KoalaBear.twoAdicity
    domainOfLogN (by intro _ _; rfl) requiredLen

/-- Fast KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def fastDomainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Domain KoalaBear.Fast.Field where
  logN := logN
  omega := KoalaBear.Fast.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    have h := (KoalaBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)).map_of_injective
      KoalaBear.Fast.ringEquiv.symm.injective
    simpa [KoalaBear.Fast.twoAdicGenerators_eq_map, bitsOfLogN, KoalaBear.Fast.ringEquiv,
      KoalaBear.Fast.ofField] using h

/-- Fast KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def fastBestDomainForLength? (requiredLen : Nat) :
    Option (FittingDomain KoalaBear.Fast.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? KoalaBear.twoAdicity
    fastDomainOfLogN (by intro _ _; rfl) requiredLen

end KoalaBear
end NTT
end CPolynomial
end CompPoly


