-- Prove2me | Definitions.Def_GeneralPieces_GenF_YY
-- name    : GeneralPieces_GenF_YY
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:28:03.784371+00:00
-- url     : https://prove2.me/theorems/dbb33ab4-8f31-4bc8-b83a-e9b0b6c1763b
-- title:
--   YY
-- statement:
--   Definitions and structural lemmas for YY, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
@[expose] def StY1 : Prop := ∀ (rd : Bool) (b : List ℕ), Pos b → ∀ τ σ' : Multiset ℕ,
  bra τ (fac (aL (xo rd) b) • MvPowerSeries.coeff (aL (xo rd) b) (expW (Bp rd) * ket rd σ')) =
    ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) • mo 0 ((τ.sum : ℤ) - σ'.sum - b.sum)
@[expose] def StY1' : Prop := ∀ (rd : Bool) (n : ℕ) (σ' : Multiset ℕ), MvPowerSeries.pderiv Tv (xi rd n) (expW (Bp rd) * ket rd σ') = 0
@[expose] def StOp0 : Prop := ∀ (b : List ℕ) (r : ℤ) (τ σ : Multiset ℕ), 0 ∈ τ → 0 ∉ σ → op b r τ σ = 0
@[expose] def StY2 : Prop := ∀ (rd : Bool) (E : ℕ) (a : List ℕ) (σ : Multiset ℕ), Pos a → σ.sum ≤ E → ∃ ℓ : Vu →ₗ[Lu] Lu,
  (∀ τ : Multiset ℕ, ℓ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) = C ((op a ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * T ((σ.sum : ℤ) - τ.sum - a.sum)) ∧
    ∀ w : W, (∀ n, MvPowerSeries.pderiv Tv (xi rd n) w = 0) →
      MvPowerSeries.constantCoeff (pdL (a.map (xi rd)) (braW σ (expW (Ap rd E) * Phi rd w))) = (MvPowerSeries.constantCoeff w).map ℓ
@[expose] def StXo : Prop := ∀ (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (b : List ℕ) (w : W),
  pdL (b.map (xo rd)) (braW σ (expW (Ap rd E) * Phi rd w)) = braW σ (expW (Ap rd E) * Phi rd (pdL (b.map (xo rd)) w))
end GeneralPieces.GenF


