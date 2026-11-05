-- Prove2me | Definitions.Def_GeneralPieces_GenF_Bra
-- name    : GeneralPieces_GenF_Bra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:27:00.03722+00:00
-- url     : https://prove2.me/theorems/0f65cf4e-ed22-4391-a5a4-1d90b8049fa7
-- title:
--   Bra
-- statement:
--   Definitions and structural lemmas for Bra, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
section Sel
variable {R : Type} [Zero R]
end Sel
section Lin
variable {Y A : Type} [CommRing A]
end Lin
section Bil
variable {R : Type}
end Bil
theorem coeff_bra (σ : Multiset ℕ) (f : Tv) (y : ℤ) : (bra σ f).coeff y = MvPolynomial.coeff (Multiset.toFinsupp σ) (f.coeff y) := rfl
theorem bra_zero (σ : Multiset ℕ) : bra σ 0 = 0 := by
  ext y : 2
  rw [coeff_bra, HahnSeries.coeff_zero, HahnSeries.coeff_zero, MvPolynomial.coeff_zero]
theorem bra_add (σ : Multiset ℕ) (f g : Tv) : bra σ (f + g) = bra σ f + bra σ g := by
  ext y : 2
  rw [HahnSeries.coeff_add, coeff_bra, coeff_bra, coeff_bra, HahnSeries.coeff_add, MvPolynomial.coeff_add]
@[expose] noncomputable def braH (σ : Multiset ℕ) : Tv →+ S where
  toFun := bra σ
  map_zero' := bra_zero σ
  map_add' := bra_add σ
@[expose] def Lin1 (g : Tv) : Prop := ∀ (y : ℤ) (m : ℕ →₀ ℕ), MvPolynomial.coeff m (g.coeff y) ≠ 0 → m.degree = 1
theorem coeff_braW (σ : Multiset ℕ) (w : W) (α : X →₀ ℕ) : MvPowerSeries.coeff α (braW σ w) = bra σ (MvPowerSeries.coeff α w) := rfl
theorem braW_zero (σ : Multiset ℕ) : braW σ 0 = 0 := by
  ext α : 1
  rw [coeff_braW, map_zero, map_zero, bra_zero]
theorem braW_add (σ : Multiset ℕ) (w w' : W) : braW σ (w + w') = braW σ w + braW σ w' := by
  ext α : 1
  rw [coeff_braW, map_add, map_add, bra_add, coeff_braW, coeff_braW]
@[expose] noncomputable def braWH (σ : Multiset ℕ) : W →+ PS where
  toFun := braW σ
  map_zero' := braW_zero σ
  map_add' := braW_add σ
end GeneralPieces.GenF


