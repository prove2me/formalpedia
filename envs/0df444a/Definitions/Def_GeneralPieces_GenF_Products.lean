-- Prove2me | Definitions.Def_GeneralPieces_GenF_Products
-- name    : GeneralPieces_GenF_Products
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:26:59.569734+00:00
-- url     : https://prove2.me/theorems/656c9e77-0400-46e1-a54e-93d7b6baedd4
-- title:
--   Products
-- statement:
--   Definitions and structural lemmas for Products, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Products.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Hahn
import Definitions.Def_GeneralPieces_GenF_Coeff
set_option autoImplicit false
section
section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
noncomputable def JmT (n : ℕ) : Derivation ℚ Tv Tv := hder ((JmU n).restrictScalars ℚ)
noncomputable def DD (rd : Bool) : X → Derivation ℚ Tv Tv := sel rd JmT 0
noncomputable def Phi (rd : Bool) : W →+* W := expD (X := X) (A := Tv) (DD rd)
noncomputable def plusSide (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) : PS := braW σ (expW (Ap rd E) * Phi rd (expW (Bp rd) * ket rd σ'))
noncomputable def normal (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) : PS := braW σ (expW (Ap rd E) * (expW (Bp rd) * Phi rd (ket rd σ')))
noncomputable def aL (ι : ℕ → X) (a : List ℕ) : X →₀ ℕ := (a.map fun n => Finsupp.single (ι n) 1).sum
def StTwoOrders : Prop := ∀ (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ), plusSide rd E σ σ' = expW (kap rd) * normal rd E σ σ'
def StN1 : Prop := ∀ (E : ℕ) (σ σ' : Multiset ℕ) (γ : X →₀ ℕ), σ.sum ≤ E →
  ∃ n : L, MvPowerSeries.coeff γ (normal false E σ σ') = toP n ∧ MvPowerSeries.coeff γ (normal true E σ σ') = toM n
def StN2 : Prop := ∀ (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ), MvPowerSeries.constantCoeff (normal rd E σ σ') = if σ = σ' then 1 else 0
def StN3 : Prop := ∀ (rd : Bool) (E : ℕ), normal rd E 0 0 = 1
def StY : Prop := ∀ (rd : Bool) (E : ℕ) (a b : List ℕ) (σ σ' : Multiset ℕ), Pos a → Pos b → 0 ∉ σ → 0 ∉ σ' → σ.sum = σ'.sum → σ.sum ≤ E →
  fac (aL (xi rd) a + aL (xo rd) b) • MvPowerSeries.coeff (aL (xi rd) a + aL (xo rd) b) (plusSide rd E σ σ') = fP a b σ σ'
end GeneralPieces.GenF


