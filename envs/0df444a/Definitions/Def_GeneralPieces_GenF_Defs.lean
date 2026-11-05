-- Prove2me | Definitions.Def_GeneralPieces_GenF_Defs
-- name    : GeneralPieces_GenF_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:25:46.792067+00:00
-- url     : https://prove2.me/theorems/a6acf8ad-464a-4bf2-8e5b-04028c213407
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_Deriv
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Data.Finsupp.Multiset
set_option autoImplicit false
section
section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
abbrev Lu : Type := LaurentPolynomial ℚ
abbrev Vu : Type := MvPolynomial ℕ Lu
abbrev Tv : Type := HahnSeries ℤ Vu
abbrev X : Type := ℕ ⊕ ℕ
abbrev W : Type := MvPowerSeries X Tv
abbrev PS : Type := MvPowerSeries X S
noncomputable def emb : S →+* Tv where
  toFun f := f.map (MvPolynomial.C : Lu →+* Vu)
  map_one' := HahnSeries.map_one (MvPolynomial.C : Lu →+* Vu).toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (MvPolynomial.C : Lu →+* Vu).toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero (MvPolynomial.C : Lu →+* Vu).toZeroHom
  map_add' _ _ := HahnSeries.map_add (MvPolynomial.C : Lu →+* Vu).toAddMonoidHom
noncomputable def embW : PS →+* W := MvPowerSeries.map emb
noncomputable def tT (k : ℕ) : Tv := HahnSeries.C (MvPolynomial.X k)
noncomputable def bra (σ : Multiset ℕ) (f : Tv) : S := f.map (MvPolynomial.coeffAddMonoidHom (Multiset.toFinsupp σ) : Vu →+ Lu)
noncomputable def braW (σ : Multiset ℕ) (w : W) : PS := fun α => bra σ (MvPowerSeries.coeff α w)
def xi (rd : Bool) (n : ℕ) : X := if rd then Sum.inr n else Sum.inl n
def xo (rd : Bool) (n : ℕ) : X := if rd then Sum.inl n else Sum.inr n
def z0 {R : Type} [Zero R] (f : ℕ → R) : ℕ → R := fun n => if n = 0 then 0 else f n
def sel {R : Type} [Zero R] (rd : Bool) (f g : ℕ → R) : X → R := if rd then Sum.elim (z0 g) (z0 f) else Sum.elim (z0 f) (z0 g)
noncomputable def bil {R : Type} [Semiring R] (q : X → X → R) : MvPowerSeries X R :=
  fun α => if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, q i i' else 0
theorem JpV_bddBelow (n : ℕ) :
    BddBelow (Function.support fun y : ℤ => if 0 ≤ y then (MvPolynomial.C (C (bet n (y + n) : ℚ)) * MvPolynomial.X (y + n).toNat : Vu) else 0) :=
  ⟨0, fun y hy => by
    by_contra h
    exact hy (if_neg h)⟩
noncomputable def JpV (n : ℕ) : Tv :=
  HahnSeries.ofSuppBddBelow (fun y : ℤ => if 0 ≤ y then MvPolynomial.C (C (bet n (y + n) : ℚ)) * MvPolynomial.X (y + n).toNat else 0) (JpV_bddBelow n)
noncomputable def JpU (E n : ℕ) : Vu := ∑ l ∈ Finset.Icc 1 E, MvPolynomial.C (C (bet n l : ℚ) * T (l - n)) * MvPolynomial.X l
noncomputable def JmU (n : ℕ) : Derivation Lu Vu Vu :=
  MvPolynomial.mkDerivation Lu fun k => MvPolynomial.C (C ((k : ℚ) * (bet n (-(k : ℤ)) : ℚ)) * T (-(k : ℤ) - n))
noncomputable def sfB' (rd : Bool) (k : ℕ) : PS := lin (sel rd 0 (fun n => (bet n (-(k : ℤ)) : ℚ) • mo 0 (-(k : ℤ) - n)))
noncomputable def Bp (rd : Bool) : W := lin (sel rd 0 JpV)
noncomputable def Ap (rd : Bool) (E : ℕ) : W := lin (sel rd (fun n => HahnSeries.C (JpU E n)) 0)
noncomputable def ket (rd : Bool) (σ' : Multiset ℕ) : W := (σ'.map fun k => MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)).prod
noncomputable def kapS (p q : ℕ) : S := sumP p q fun k => (k : ℚ) * (Ring.choose (-k - 1) (p - 1) : ℤ) * (Ring.choose (k - 1) (q - 1) : ℤ)
noncomputable def kap (rd : Bool) : PS := bil fun i i' => sel rd (fun p => sel rd 0 (fun q => kapS p q) i') 0 i
end GeneralPieces.GenF


