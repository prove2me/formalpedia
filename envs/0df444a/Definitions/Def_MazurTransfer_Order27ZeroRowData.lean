-- Prove2me | Definitions.Def_MazurTransfer_Order27ZeroRowData
-- name    : MazurTransfer_Order27ZeroRowData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T16:58:33.469145+00:00
-- url     : https://prove2.me/theorems/625f7ff2-ccde-42b6-b6b3-d830d6abdd95
-- title:
--   Order-27 zero certificate: row and column data
-- statement:
--   For $f,\xi\in\mathbb Q$, let $r_i(f,\xi,b)$, with $0\leq i<17$ and $0\leq b<24$, denote the entries of the original sparse row table. Define the column sum by
--   \[C(f,\xi,b)=\sum_{i=0}^{16} r_i(f,\xi,b).\]
--   The row entries are the exact original rational expressions. These are data definitions only. The named downstream consumers are the row reordering equality and the twenty-four column-vanishing certificates.
-- source:
--   Exact pure definitions from user MazurTheorem WIP, commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Zero. Apache-2.0 header retained. Only the resolved private modifier token is removed; every type and value byte is retained.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

noncomputable section
namespace MazurTorsion.Kubert

@[irreducible]  def tlRowCell0 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 =>
      ((tlNCbP0c0 f ξ + tlNCbP1c0 f ξ) +
                  (tlNCbP2c0 f ξ + (tlNCbP3c0 f ξ + tlNCbP4c0 f ξ)))
  | 1 =>
      ((tlNCbP0c1 f ξ + tlNCbP1c1 f ξ) +
                  (tlNCbP2c1 f ξ + (tlNCbP3c1 f ξ + tlNCbP4c1 f ξ)))
  | 2 =>
      ((tlNCbP0c2 f ξ + tlNCbP1c2 f ξ) +
                  (tlNCbP2c2 f ξ + (tlNCbP3c2 f ξ + tlNCbP4c2 f ξ)))
  | 3 =>
      ((tlNCbP0c3 f ξ + tlNCbP1c3 f ξ) +
                  (tlNCbP2c3 f ξ + (tlNCbP3c3 f ξ + tlNCbP4c3 f ξ)))
  | 4 =>
      ((tlNCbP0c4 f ξ + tlNCbP1c4 f ξ) +
                  (tlNCbP2c4 f ξ + (tlNCbP3c4 f ξ + tlNCbP4c4 f ξ)))
  | 5 =>
      ((tlNCbP0c5 f ξ + tlNCbP1c5 f ξ) +
                  (tlNCbP2c5 f ξ + (tlNCbP3c5 f ξ + tlNCbP4c5 f ξ)))
  | 6 =>
      ((tlNCbP0c6 f ξ + tlNCbP1c6 f ξ) +
                  (tlNCbP2c6 f ξ + (tlNCbP3c6 f ξ + tlNCbP4c6 f ξ)))
  | 7 =>
      ((tlNCbP0c7 f ξ + tlNCbP1c7 f ξ) +
                  (tlNCbP2c7 f ξ + (tlNCbP3c7 f ξ + tlNCbP4c7 f ξ)))
  | 8 =>
      ((tlNCbP0c8 f ξ + tlNCbP1c8 f ξ) +
                  (tlNCbP2c8 f ξ + (tlNCbP3c8 f ξ + tlNCbP4c8 f ξ)))
  | 9 => ((tlNCbP0c9 f ξ + tlNCbP1c9 f ξ) + (tlNCbP2c9 f ξ + tlNCbP3c9 f ξ))
  | 10 =>
      ((tlNCbP0c10 f ξ + tlNCbP1c10 f ξ) +
                  (tlNCbP2c10 f ξ + tlNCbP3c10 f ξ))
  | 11 => (tlNCbP1c11 f ξ + (tlNCbP2c11 f ξ + tlNCbP3c11 f ξ))
  | 12 => (tlNCbP1c12 f ξ + (tlNCbP2c12 f ξ + tlNCbP3c12 f ξ))
  | 13 => (tlNCbP2c13 f ξ + tlNCbP3c13 f ξ)
  | 14 => (tlNCbP2c14 f ξ + tlNCbP3c14 f ξ)
  | 15 => tlNCbP3c15 f ξ
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell1 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => (tlNCbP5c0 f ξ + tlNCbP8c0 f ξ)
  | 1 => (tlNCbP5c1 f ξ + tlNCbP6c0 f ξ)
  | 2 => (tlNCbP5c2 f ξ + (tlNCbP6c1 f ξ + tlNCbP7c0 f ξ))
  | 3 => (tlNCbP5c3 f ξ + (tlNCbP6c2 f ξ + tlNCbP7c1 f ξ))
  | 4 => (tlNCbP5c4 f ξ + (tlNCbP6c3 f ξ + tlNCbP7c2 f ξ))
  | 5 => (tlNCbP5c5 f ξ + (tlNCbP6c4 f ξ + tlNCbP7c3 f ξ))
  | 6 => (tlNCbP5c6 f ξ + (tlNCbP6c5 f ξ + tlNCbP7c4 f ξ))
  | 7 => (tlNCbP5c7 f ξ + (tlNCbP6c6 f ξ + tlNCbP7c5 f ξ))
  | 8 => (tlNCbP5c8 f ξ + (tlNCbP6c7 f ξ + tlNCbP7c6 f ξ))
  | 9 => ((tlNCbP4c9 f ξ + tlNCbP5c9 f ξ) + (tlNCbP6c8 f ξ + tlNCbP7c7 f ξ))
  | 10 => ((tlNCbP4c10 f ξ + tlNCbP5c10 f ξ) + (tlNCbP6c9 f ξ + tlNCbP7c8 f ξ))
  | 11 => ((tlNCbP4c11 f ξ + tlNCbP5c11 f ξ) + (tlNCbP6c10 f ξ + tlNCbP7c9 f ξ))
  | 12 =>
      ((tlNCbP4c12 f ξ + tlNCbP5c12 f ξ) +
                  (tlNCbP6c11 f ξ + tlNCbP7c10 f ξ))
  | 13 =>
      ((tlNCbP4c13 f ξ + tlNCbP5c13 f ξ) +
                  (tlNCbP6c12 f ξ + tlNCbP7c11 f ξ))
  | 14 =>
      ((tlNCbP4c14 f ξ + tlNCbP5c14 f ξ) +
                  (tlNCbP6c13 f ξ + tlNCbP7c12 f ξ))
  | 15 =>
      ((tlNCbP4c15 f ξ + tlNCbP5c15 f ξ) +
                  (tlNCbP6c14 f ξ + tlNCbP7c13 f ξ))
  | 16 =>
      ((tlNCbP4c16 f ξ + tlNCbP5c16 f ξ) +
                  (tlNCbP6c15 f ξ + tlNCbP7c14 f ξ))
  | 17 => (tlNCbP5c17 f ξ + (tlNCbP6c16 f ξ + tlNCbP7c15 f ξ))
  | 18 => (tlNCbP6c17 f ξ + tlNCbP7c16 f ξ)
  | 19 => tlNCbP7c17 f ξ
  | 20 => tlNCbP7c18 f ξ
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell2 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => ((tlNCbP9c0 f ξ + tlNCbP10c0 f ξ) + (tlNCbP11c0 f ξ + tlNCbP12c0 f ξ))
  | 1 =>
      ((tlNCbP8c1 f ξ + tlNCbP9c1 f ξ) +
                  (tlNCbP10c1 f ξ + (tlNCbP11c1 f ξ + tlNCbP12c1 f ξ)))
  | 2 =>
      ((tlNCbP8c2 f ξ + tlNCbP9c2 f ξ) +
                  (tlNCbP10c2 f ξ + (tlNCbP11c2 f ξ + tlNCbP12c2 f ξ)))
  | 3 =>
      ((tlNCbP8c3 f ξ + tlNCbP9c3 f ξ) +
                  (tlNCbP10c3 f ξ + (tlNCbP11c3 f ξ + tlNCbP12c3 f ξ)))
  | 4 =>
      ((tlNCbP8c4 f ξ + tlNCbP9c4 f ξ) +
                  (tlNCbP10c4 f ξ + (tlNCbP11c4 f ξ + tlNCbP12c4 f ξ)))
  | 5 =>
      ((tlNCbP8c5 f ξ + tlNCbP9c5 f ξ) +
                  (tlNCbP10c5 f ξ + (tlNCbP11c5 f ξ + tlNCbP12c5 f ξ)))
  | 6 =>
      ((tlNCbP8c6 f ξ + tlNCbP9c6 f ξ) +
                  (tlNCbP10c6 f ξ + (tlNCbP11c6 f ξ + tlNCbP12c6 f ξ)))
  | 7 =>
      ((tlNCbP8c7 f ξ + tlNCbP9c7 f ξ) +
                  (tlNCbP10c7 f ξ + (tlNCbP11c7 f ξ + tlNCbP12c7 f ξ)))
  | 8 =>
      ((tlNCbP8c8 f ξ + tlNCbP9c8 f ξ) +
                  (tlNCbP10c8 f ξ + (tlNCbP11c8 f ξ + tlNCbP12c8 f ξ)))
  | 9 =>
      ((tlNCbP8c9 f ξ + tlNCbP9c9 f ξ) +
                  (tlNCbP10c9 f ξ + (tlNCbP11c9 f ξ + tlNCbP12c9 f ξ)))
  | 10 =>
      ((tlNCbP8c10 f ξ + tlNCbP9c10 f ξ) +
                  (tlNCbP10c10 f ξ + (tlNCbP11c10 f ξ + tlNCbP12c10 f ξ)))
  | 11 =>
      ((tlNCbP9c11 f ξ + tlNCbP10c11 f ξ) +
                  (tlNCbP11c11 f ξ + tlNCbP12c11 f ξ))
  | 12 => (tlNCbP9c12 f ξ + (tlNCbP10c12 f ξ + tlNCbP11c12 f ξ))
  | 13 => (tlNCbP10c13 f ξ + tlNCbP11c13 f ξ)
  | 14 => tlNCbP11c14 f ξ
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell3 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => tlNCbP13c0 f ξ
  | 1 => (tlNCbP13c1 f ξ + (tlNCbP14c0 f ξ + tlNCbP15c0 f))
  | 2 =>
      ((tlNCbP13c2 f ξ + tlNCbP14c1 f ξ) +
                  (tlNCbP15c1 f ξ + tlNCbP16c0 f ξ))
  | 3 =>
      ((tlNCbP13c3 f ξ + tlNCbP14c2 f ξ) +
                  (tlNCbP15c2 f ξ + tlNCbP16c1 f ξ))
  | 4 =>
      ((tlNCbP13c4 f ξ + tlNCbP14c3 f ξ) +
                  (tlNCbP15c3 f ξ + tlNCbP16c2 f ξ))
  | 5 =>
      ((tlNCbP13c5 f ξ + tlNCbP14c4 f ξ) +
                  (tlNCbP15c4 f ξ + tlNCbP16c3 f ξ))
  | 6 =>
      ((tlNCbP13c6 f ξ + tlNCbP14c5 f ξ) +
                  (tlNCbP15c5 f ξ + tlNCbP16c4 f ξ))
  | 7 => (tlNCbP13c7 f ξ + (tlNCbP14c6 f ξ + tlNCbP15c6 f ξ))
  | 8 => (tlNCbP13c8 f ξ + (tlNCbP14c7 f ξ + tlNCbP15c7 f ξ))
  | 9 => (tlNCbP13c9 f ξ + (tlNCbP14c8 f ξ + tlNCbP15c8 f ξ))
  | 10 => (tlNCbP13c10 f ξ + (tlNCbP14c9 f ξ + tlNCbP15c9 f ξ))
  | 11 => (tlNCbP13c11 f ξ + (tlNCbP14c10 f ξ + tlNCbP15c10 f ξ))
  | 12 =>
      ((tlNCbP12c12 f ξ + tlNCbP13c12 f ξ) +
                  (tlNCbP14c11 f ξ + tlNCbP15c11 f ξ))
  | 13 =>
      ((tlNCbP12c13 f ξ + tlNCbP13c13 f ξ) +
                  (tlNCbP14c12 f ξ + tlNCbP15c12 f ξ))
  | 14 =>
      ((tlNCbP12c14 f ξ + tlNCbP13c14 f ξ) +
                  (tlNCbP14c13 f ξ + tlNCbP15c13 f ξ))
  | 15 =>
      ((tlNCbP12c15 f ξ + tlNCbP13c15 f ξ) +
                  (tlNCbP14c14 f ξ + tlNCbP15c14 f ξ))
  | 16 => (tlNCbP13c16 f ξ + (tlNCbP14c15 f ξ + tlNCbP15c15 f ξ))
  | 17 => (tlNCbP13c17 f ξ + (tlNCbP14c16 f ξ + tlNCbP15c16 f ξ))
  | 18 => (tlNCbP14c17 f ξ + tlNCbP15c17 f ξ)
  | 19 => tlNCbP15c18 f ξ
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell4 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => (tlNCbP18c0 f ξ + (tlNCbP19c0 f ξ + tlNCbP20c0 f ξ))
  | 1 => (tlNCbP18c1 f ξ + (tlNCbP19c1 f ξ + tlNCbP20c1 f ξ))
  | 2 => (tlNCbP18c2 f ξ + (tlNCbP19c2 f ξ + tlNCbP20c2 f ξ))
  | 3 =>
      ((tlNCbP17c0 f ξ + tlNCbP18c3 f ξ) +
                  (tlNCbP19c3 f ξ + tlNCbP20c3 f ξ))
  | 4 =>
      ((tlNCbP17c1 f ξ + tlNCbP18c4 f ξ) +
                  (tlNCbP19c4 f ξ + tlNCbP20c4 f ξ))
  | 5 =>
      ((tlNCbP17c2 f ξ + tlNCbP18c5 f ξ) +
                  (tlNCbP19c5 f ξ + tlNCbP20c5 f ξ))
  | 6 =>
      ((tlNCbP17c3 f ξ + tlNCbP18c6 f ξ) +
                  (tlNCbP19c6 f ξ + tlNCbP20c6 f ξ))
  | 7 =>
      ((tlNCbP16c5 f ξ + tlNCbP17c4 f ξ) +
                  (tlNCbP18c7 f ξ + tlNCbP19c7 f ξ))
  | 8 =>
      ((tlNCbP16c6 f ξ + tlNCbP17c5 f ξ) +
                  (tlNCbP18c8 f ξ + tlNCbP19c8 f ξ))
  | 9 =>
      ((tlNCbP16c7 f ξ + tlNCbP17c6 f ξ) +
                  (tlNCbP18c9 f ξ + tlNCbP19c9 f ξ))
  | 10 =>
      ((tlNCbP16c8 f ξ + tlNCbP17c7 f ξ) +
                  (tlNCbP18c10 f ξ + tlNCbP19c10 f ξ))
  | 11 => (tlNCbP16c9 f ξ + (tlNCbP17c8 f ξ + tlNCbP19c11 f ξ))
  | 12 => (tlNCbP16c10 f ξ + (tlNCbP17c9 f ξ + tlNCbP19c12 f ξ))
  | 13 => (tlNCbP16c11 f ξ + tlNCbP17c10 f ξ)
  | 14 => (tlNCbP16c12 f ξ + tlNCbP17c11 f ξ)
  | 15 => (tlNCbP16c13 f ξ + tlNCbP17c12 f ξ)
  | 16 => (tlNCbP16c14 f ξ + tlNCbP17c13 f ξ)
  | 17 => (tlNCbP16c15 f ξ + tlNCbP17c14 f ξ)
  | 18 => (tlNCbP16c16 f ξ + tlNCbP17c15 f ξ)
  | 19 => (tlNCbP16c17 f ξ + tlNCbP17c16 f ξ)
  | 20 => (tlNCbP16c18 f ξ + tlNCbP17c17 f ξ)
  | 21 => tlNCbP17c18 f ξ
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell5 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => (tlNCbP21c0 f ξ + (tlNCbP22c0 f ξ + tlNCbP23c0 f ξ))
  | 1 =>
      ((tlNCbP21c1 f ξ + tlNCbP22c1 f ξ) +
                  (tlNCbP23c1 f ξ + tlNCbP24c0 f ξ))
  | 2 =>
      ((tlNCbP21c2 f ξ + tlNCbP22c2 f ξ) +
                  (tlNCbP23c2 f ξ + tlNCbP24c1 f ξ))
  | 3 =>
      ((tlNCbP21c3 f ξ + tlNCbP22c3 f ξ) +
                  (tlNCbP23c3 f ξ + tlNCbP24c2 f ξ))
  | 4 =>
      ((tlNCbP21c4 f ξ + tlNCbP22c4 f ξ) +
                  (tlNCbP23c4 f ξ + tlNCbP24c3 f ξ))
  | 5 =>
      ((tlNCbP21c5 f ξ + tlNCbP22c5 f ξ) +
                  (tlNCbP23c5 f ξ + tlNCbP24c4 f ξ))
  | 6 =>
      ((tlNCbP21c6 f ξ + tlNCbP22c6 f ξ) +
                  (tlNCbP23c6 f ξ + tlNCbP24c5 f ξ))
  | 7 =>
      ((tlNCbP20c7 f ξ + tlNCbP21c7 f ξ) +
                  (tlNCbP22c7 f ξ + (tlNCbP23c7 f ξ + tlNCbP24c6 f ξ)))
  | 8 =>
      ((tlNCbP20c8 f ξ + tlNCbP21c8 f ξ) +
                  (tlNCbP22c8 f ξ + (tlNCbP23c8 f ξ + tlNCbP24c7 f ξ)))
  | 9 =>
      ((tlNCbP20c9 f ξ + tlNCbP21c9 f ξ) +
                  (tlNCbP22c9 f ξ + (tlNCbP23c9 f ξ + tlNCbP24c8 f ξ)))
  | 10 =>
      ((tlNCbP20c10 f ξ + tlNCbP21c10 f ξ) +
                  (tlNCbP22c10 f ξ + tlNCbP23c10 f ξ))
  | 11 =>
      ((tlNCbP20c11 f ξ + tlNCbP21c11 f ξ) +
                  (tlNCbP22c11 f ξ + tlNCbP23c11 f ξ))
  | 12 =>
      ((tlNCbP20c12 f ξ + tlNCbP21c12 f ξ) +
                  (tlNCbP22c12 f ξ + tlNCbP23c12 f ξ))
  | 13 =>
      ((tlNCbP20c13 f ξ + tlNCbP21c13 f ξ) +
                  (tlNCbP22c13 f ξ + tlNCbP23c13 f ξ))
  | 14 => (tlNCbP21c14 f ξ + (tlNCbP22c14 f ξ + tlNCbP23c14 f ξ))
  | 15 => (tlNCbP22c15 f ξ + tlNCbP23c15 f ξ)
  | 16 => tlNCbP23c16 f ξ
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell6 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => 0
  | 1 => tlNCbP25c0 f
  | 2 => (tlNCbP25c1 f ξ + tlNCbP26c0 f ξ)
  | 3 => (tlNCbP25c2 f ξ + (tlNCbP26c1 f ξ + tlNCbP27c0 f ξ))
  | 4 => (tlNCbP25c3 f ξ + (tlNCbP26c2 f ξ + tlNCbP27c1 f ξ))
  | 5 => (tlNCbP25c4 f ξ + (tlNCbP26c3 f ξ + tlNCbP27c2 f ξ))
  | 6 => (tlNCbP25c5 f ξ + (tlNCbP26c4 f ξ + tlNCbP27c3 f ξ))
  | 7 => (tlNCbP25c6 f ξ + (tlNCbP26c5 f ξ + tlNCbP27c4 f ξ))
  | 8 => (tlNCbP25c7 f ξ + (tlNCbP26c6 f ξ + tlNCbP27c5 f ξ))
  | 9 => (tlNCbP25c8 f ξ + (tlNCbP26c7 f ξ + tlNCbP27c6 f ξ))
  | 10 =>
      ((tlNCbP24c9 f ξ + tlNCbP25c9 f ξ) +
                  (tlNCbP26c8 f ξ + tlNCbP27c7 f ξ))
  | 11 =>
      ((tlNCbP24c10 f ξ + tlNCbP25c10 f ξ) +
                  (tlNCbP26c9 f ξ + tlNCbP27c8 f ξ))
  | 12 =>
      ((tlNCbP24c11 f ξ + tlNCbP25c11 f ξ) +
                  (tlNCbP26c10 f ξ + tlNCbP27c9 f ξ))
  | 13 =>
      ((tlNCbP24c12 f ξ + tlNCbP25c12 f ξ) +
                  (tlNCbP26c11 f ξ + tlNCbP27c10 f ξ))
  | 14 =>
      ((tlNCbP24c13 f ξ + tlNCbP25c13 f ξ) +
                  (tlNCbP26c12 f ξ + tlNCbP27c11 f ξ))
  | 15 =>
      ((tlNCbP24c14 f ξ + tlNCbP25c14 f ξ) +
                  (tlNCbP26c13 f ξ + tlNCbP27c12 f ξ))
  | 16 =>
      ((tlNCbP24c15 f ξ + tlNCbP25c15 f ξ) +
                  (tlNCbP26c14 f ξ + tlNCbP27c13 f ξ))
  | 17 =>
      ((tlNCbP24c16 f ξ + tlNCbP25c16 f ξ) +
                  (tlNCbP26c15 f ξ + tlNCbP27c14 f ξ))
  | 18 =>
      ((tlNCbP24c17 f ξ + tlNCbP25c17 f ξ) +
                  (tlNCbP26c16 f ξ + tlNCbP27c15 f ξ))
  | 19 => (tlNCbP25c18 f ξ + (tlNCbP26c17 f ξ + tlNCbP27c16 f ξ))
  | 20 => tlNCbP26c18 f ξ
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell7 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 =>
      ((tlNCbP29c0 f ξ + tlNCbP30c0 f ξ) +
                  (tlNCbP31c0 f ξ + tlNCbP32c0 f ξ))
  | 1 =>
      ((tlNCbP29c1 f ξ + tlNCbP30c1 f ξ) +
                  (tlNCbP31c1 f ξ + tlNCbP32c1 f ξ))
  | 2 =>
      ((tlNCbP29c2 f ξ + tlNCbP30c2 f ξ) +
                  (tlNCbP31c2 f ξ + tlNCbP32c2 f ξ))
  | 3 =>
      ((tlNCbP29c3 f ξ + tlNCbP30c3 f ξ) +
                  (tlNCbP31c3 f ξ + tlNCbP32c3 f ξ))
  | 4 =>
      ((tlNCbP28c0 f ξ + tlNCbP29c4 f ξ) +
                  (tlNCbP30c4 f ξ + (tlNCbP31c4 f ξ + tlNCbP32c4 f ξ)))
  | 5 =>
      ((tlNCbP28c1 f ξ + tlNCbP29c5 f ξ) +
                  (tlNCbP30c5 f ξ + tlNCbP31c5 f ξ))
  | 6 =>
      ((tlNCbP28c2 f ξ + tlNCbP29c6 f ξ) +
                  (tlNCbP30c6 f ξ + tlNCbP31c6 f ξ))
  | 7 =>
      ((tlNCbP28c3 f ξ + tlNCbP29c7 f ξ) +
                  (tlNCbP30c7 f ξ + tlNCbP31c7 f ξ))
  | 8 =>
      ((tlNCbP28c4 f ξ + tlNCbP29c8 f ξ) +
                  (tlNCbP30c8 f ξ + tlNCbP31c8 f ξ))
  | 9 =>
      ((tlNCbP28c5 f ξ + tlNCbP29c9 f ξ) +
                  (tlNCbP30c9 f ξ + tlNCbP31c9 f ξ))
  | 10 =>
      ((tlNCbP28c6 f ξ + tlNCbP29c10 f ξ) +
                  (tlNCbP30c10 f ξ + tlNCbP31c10 f ξ))
  | 11 => (tlNCbP28c7 f ξ + (tlNCbP30c11 f ξ + tlNCbP31c11 f ξ))
  | 12 => (tlNCbP28c8 f ξ + (tlNCbP30c12 f ξ + tlNCbP31c12 f ξ))
  | 13 => (tlNCbP28c9 f ξ + tlNCbP31c13 f ξ)
  | 14 => tlNCbP28c10 f ξ
  | 15 => tlNCbP28c11 f ξ
  | 16 => tlNCbP28c12 f ξ
  | 17 => tlNCbP28c13 f ξ
  | 18 => tlNCbP28c14 f ξ
  | 19 => tlNCbP28c15 f ξ
  | 20 => (tlNCbP27c17 f ξ + tlNCbP28c16 f ξ)
  | 21 => (tlNCbP27c18 f ξ + tlNCbP28c17 f ξ)
  | 22 => tlNCbP28c18 f ξ
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell8 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => (tlNCbP33c0 f ξ + tlNCbP34c0 f ξ)
  | 1 => (tlNCbP33c1 f ξ + (tlNCbP34c1 f ξ + tlNCbP35c0 f ξ))
  | 2 => (tlNCbP33c2 f ξ + (tlNCbP34c2 f ξ + tlNCbP35c1 f ξ))
  | 3 => (tlNCbP33c3 f ξ + (tlNCbP34c3 f ξ + tlNCbP35c2 f ξ))
  | 4 => (tlNCbP33c4 f ξ + (tlNCbP34c4 f ξ + tlNCbP35c3 f ξ))
  | 5 =>
      ((tlNCbP32c5 f ξ + tlNCbP33c5 f ξ) +
                  (tlNCbP34c5 f ξ + tlNCbP35c4 f ξ))
  | 6 =>
      ((tlNCbP32c6 f ξ + tlNCbP33c6 f ξ) +
                  (tlNCbP34c6 f ξ + tlNCbP35c5 f ξ))
  | 7 =>
      ((tlNCbP32c7 f ξ + tlNCbP33c7 f ξ) +
                  (tlNCbP34c7 f ξ + tlNCbP35c6 f ξ))
  | 8 =>
      ((tlNCbP32c8 f ξ + tlNCbP33c8 f ξ) +
                  (tlNCbP34c8 f ξ + tlNCbP35c7 f ξ))
  | 9 =>
      ((tlNCbP32c9 f ξ + tlNCbP33c9 f ξ) +
                  (tlNCbP34c9 f ξ + tlNCbP35c8 f ξ))
  | 10 =>
      ((tlNCbP32c10 f ξ + tlNCbP33c10 f ξ) +
                  (tlNCbP34c10 f ξ + tlNCbP35c9 f ξ))
  | 11 =>
      ((tlNCbP32c11 f ξ + tlNCbP33c11 f ξ) +
                  (tlNCbP34c11 f ξ + tlNCbP35c10 f ξ))
  | 12 =>
      ((tlNCbP32c12 f ξ + tlNCbP33c12 f ξ) +
                  (tlNCbP34c12 f ξ + tlNCbP35c11 f ξ))
  | 13 =>
      ((tlNCbP32c13 f ξ + tlNCbP33c13 f ξ) +
                  (tlNCbP34c13 f ξ + tlNCbP35c12 f ξ))
  | 14 =>
      ((tlNCbP32c14 f ξ + tlNCbP33c14 f ξ) +
                  (tlNCbP34c14 f ξ + tlNCbP35c13 f ξ))
  | 15 =>
      ((tlNCbP32c15 f ξ + tlNCbP33c15 f ξ) +
                  (tlNCbP34c15 f ξ + tlNCbP35c14 f ξ))
  | 16 => (tlNCbP33c16 f ξ + (tlNCbP34c16 f ξ + tlNCbP35c15 f ξ))
  | 17 => (tlNCbP34c17 f ξ + tlNCbP35c16 f ξ)
  | 18 => tlNCbP35c17 f ξ
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell9 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => 0
  | 1 => tlNCbP36c0 f
  | 2 => (tlNCbP36c1 f ξ + tlNCbP37c0 f)
  | 3 => (tlNCbP36c2 f ξ + (tlNCbP37c1 f ξ + tlNCbP38c0 f))
  | 4 => ((tlNCbP36c3 f ξ + tlNCbP37c2 f ξ) + (tlNCbP38c1 f ξ + tlNCbP39c0 f))
  | 5 =>
      ((tlNCbP36c4 f ξ + tlNCbP37c3 f ξ) +
                  (tlNCbP38c2 f ξ + tlNCbP39c1 f ξ))
  | 6 =>
      ((tlNCbP36c5 f ξ + tlNCbP37c4 f ξ) +
                  (tlNCbP38c3 f ξ + tlNCbP39c2 f ξ))
  | 7 =>
      ((tlNCbP36c6 f ξ + tlNCbP37c5 f ξ) +
                  (tlNCbP38c4 f ξ + tlNCbP39c3 f ξ))
  | 8 =>
      ((tlNCbP36c7 f ξ + tlNCbP37c6 f ξ) +
                  (tlNCbP38c5 f ξ + tlNCbP39c4 f ξ))
  | 9 =>
      ((tlNCbP36c8 f ξ + tlNCbP37c7 f ξ) +
                  (tlNCbP38c6 f ξ + tlNCbP39c5 f ξ))
  | 10 =>
      ((tlNCbP36c9 f ξ + tlNCbP37c8 f ξ) +
                  (tlNCbP38c7 f ξ + tlNCbP39c6 f ξ))
  | 11 => (tlNCbP36c10 f ξ + (tlNCbP37c9 f ξ + tlNCbP38c8 f ξ))
  | 12 => (tlNCbP36c11 f ξ + (tlNCbP37c10 f ξ + tlNCbP38c9 f ξ))
  | 13 => (tlNCbP36c12 f ξ + (tlNCbP37c11 f ξ + tlNCbP38c10 f ξ))
  | 14 => (tlNCbP36c13 f ξ + (tlNCbP37c12 f ξ + tlNCbP38c11 f ξ))
  | 15 => (tlNCbP36c14 f ξ + (tlNCbP37c13 f ξ + tlNCbP38c12 f ξ))
  | 16 => (tlNCbP36c15 f ξ + (tlNCbP37c14 f ξ + tlNCbP38c13 f ξ))
  | 17 => (tlNCbP36c16 f ξ + (tlNCbP37c15 f ξ + tlNCbP38c14 f ξ))
  | 18 => (tlNCbP36c17 f ξ + (tlNCbP37c16 f ξ + tlNCbP38c15 f ξ))
  | 19 => (tlNCbP36c18 f ξ + (tlNCbP37c17 f ξ + tlNCbP38c16 f ξ))
  | 20 => (tlNCbP37c18 f ξ + tlNCbP38c17 f ξ)
  | 21 => tlNCbP38c18 f ξ
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell10 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => tlNCbP40c0 f
  | 6 => tlNCbP40c1 f ξ
  | 7 => tlNCbP40c2 f ξ
  | 8 => tlNCbP40c3 f ξ
  | 9 => tlNCbP40c4 f ξ
  | 10 => tlNCbP40c5 f ξ
  | 11 => (tlNCbP39c7 f ξ + tlNCbP40c6 f ξ)
  | 12 => (tlNCbP39c8 f ξ + tlNCbP40c7 f ξ)
  | 13 => (tlNCbP39c9 f ξ + tlNCbP40c8 f ξ)
  | 14 => (tlNCbP39c10 f ξ + tlNCbP40c9 f ξ)
  | 15 => (tlNCbP39c11 f ξ + tlNCbP40c10 f ξ)
  | 16 => (tlNCbP39c12 f ξ + tlNCbP40c11 f ξ)
  | 17 => (tlNCbP39c13 f ξ + tlNCbP40c12 f ξ)
  | 18 => (tlNCbP39c14 f ξ + tlNCbP40c13 f ξ)
  | 19 => (tlNCbP39c15 f ξ + tlNCbP40c14 f ξ)
  | 20 => (tlNCbP39c16 f ξ + tlNCbP40c15 f ξ)
  | 21 => (tlNCbP39c17 f ξ + tlNCbP40c16 f ξ)
  | 22 => (tlNCbP39c18 f ξ + tlNCbP40c17 f ξ)
  | 23 => tlNCbP40c18 f ξ
  | _ => 0

@[irreducible]  def tlRowCell11 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => (tlWTwoXP0c0 f ξ + (tlWTwoXP1c0 f ξ + tlWTwoXP2c0 f ξ))
  | 1 => (tlWTwoXP0c1 f ξ + (tlWTwoXP1c1 f ξ + tlWTwoXP2c1 f ξ))
  | 2 => (tlWTwoXP0c2 f ξ + (tlWTwoXP1c2 f ξ + tlWTwoXP2c2 f ξ))
  | 3 => (tlWTwoXP0c3 f ξ + (tlWTwoXP1c3 f ξ + tlWTwoXP2c3 f ξ))
  | 4 => (tlWTwoXP0c4 f ξ + (tlWTwoXP1c4 f ξ + tlWTwoXP2c4 f ξ))
  | 5 => (tlWTwoXP0c5 f ξ + (tlWTwoXP1c5 f ξ + tlWTwoXP2c5 f ξ))
  | 6 => (tlWTwoXP0c6 f ξ + (tlWTwoXP1c6 f ξ + tlWTwoXP2c6 f ξ))
  | 7 => (tlWTwoXP0c7 f ξ + (tlWTwoXP1c7 f ξ + tlWTwoXP2c7 f ξ))
  | 8 => (tlWTwoXP0c8 f ξ + (tlWTwoXP1c8 f ξ + tlWTwoXP2c8 f ξ))
  | 9 => (tlWTwoXP0c9 f ξ + (tlWTwoXP1c9 f ξ + tlWTwoXP2c9 f ξ))
  | 10 => (tlWTwoXP0c10 f ξ + (tlWTwoXP1c10 f ξ + tlWTwoXP2c10 f ξ))
  | 11 => (tlWTwoXP0c11 f ξ + (tlWTwoXP1c11 f ξ + tlWTwoXP2c11 f ξ))
  | 12 => (tlWTwoXP0c12 f ξ + (tlWTwoXP1c12 f ξ + tlWTwoXP2c12 f ξ))
  | 13 => (tlWTwoXP0c13 f ξ + (tlWTwoXP1c13 f ξ + tlWTwoXP2c13 f ξ))
  | 14 => (tlWTwoXP0c14 f ξ + (tlWTwoXP1c14 f ξ + tlWTwoXP2c14 f ξ))
  | 15 => (tlWTwoXP0c15 f ξ + (tlWTwoXP1c15 f ξ + tlWTwoXP2c15 f ξ))
  | 16 => (tlWTwoXP0c16 f ξ + (tlWTwoXP1c16 f ξ + tlWTwoXP2c16 f ξ))
  | 17 => (tlWTwoXP0c17 f ξ + (tlWTwoXP1c17 f ξ + tlWTwoXP2c17 f ξ))
  | 18 => (tlWTwoXP0c18 f ξ + (tlWTwoXP1c18 f ξ + tlWTwoXP2c18 f ξ))
  | 19 => (tlWTwoXP0c19 f ξ + (tlWTwoXP1c19 f ξ + tlWTwoXP2c19 f ξ))
  | 20 => (tlWTwoXP0c20 f ξ + (tlWTwoXP1c20 f ξ + tlWTwoXP2c20 f ξ))
  | 21 => tlWTwoXP1c21 f ξ
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell12 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => tlWTwoXP3c0 f ξ
  | 1 => tlWTwoXP3c1 f ξ
  | 2 => tlWTwoXP3c2 f ξ
  | 3 => tlWTwoXP3c3 f ξ
  | 4 => tlWTwoXP3c4 f ξ
  | 5 => tlWTwoXP3c5 f ξ
  | 6 => tlWTwoXP3c6 f ξ
  | 7 => tlWTwoXP3c7 f ξ
  | 8 => tlWTwoXP3c8 f ξ
  | 9 => tlWTwoXP3c9 f ξ
  | 10 => tlWTwoXP3c10 f ξ
  | 11 => tlWTwoXP3c11 f ξ
  | 12 => tlWTwoXP3c12 f ξ
  | 13 => tlWTwoXP3c13 f ξ
  | 14 => tlWTwoXP3c14 f ξ
  | 15 => tlWTwoXP3c15 f ξ
  | 16 => tlWTwoXP3c16 f ξ
  | 17 => (tlWTwoXP3c17 f ξ + tlWTwoXP4c0 f ξ)
  | 18 => (tlWTwoXP3c18 f ξ + tlWTwoXP4c1 f ξ)
  | 19 => (tlWTwoXP3c19 f ξ + tlWTwoXP4c2 f ξ)
  | 20 => (tlWTwoXP3c20 f ξ + tlWTwoXP4c3 f ξ)
  | 21 => (tlWTwoXP2c21 f ξ + (tlWTwoXP3c21 f ξ + tlWTwoXP4c4 f ξ))
  | 22 => (tlWTwoXP2c22 f ξ + tlWTwoXP4c5 f ξ)
  | 23 => tlWTwoXP4c6 f ξ
  | _ => 0

@[irreducible]  def tlRowCell13 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => (tlWOneXP0c0 f ξ + (tlWOneXP1c0 f ξ + tlWOneXP2c0 f ξ))
  | 1 =>
      ((tlWOneXP0c1 f ξ + tlWOneXP1c1 f ξ) +
                  (tlWOneXP2c1 f ξ + tlWOneXP3c0 f ξ))
  | 2 =>
      ((tlWOneXP0c2 f ξ + tlWOneXP1c2 f ξ) +
                  (tlWOneXP2c2 f ξ + tlWOneXP3c1 f ξ))
  | 3 =>
      ((tlWOneXP0c3 f ξ + tlWOneXP1c3 f ξ) +
                  (tlWOneXP2c3 f ξ + tlWOneXP3c2 f ξ))
  | 4 =>
      ((tlWOneXP0c4 f ξ + tlWOneXP1c4 f ξ) +
                  (tlWOneXP2c4 f ξ + tlWOneXP3c3 f ξ))
  | 5 =>
      ((tlWOneXP0c5 f ξ + tlWOneXP1c5 f ξ) +
                  (tlWOneXP2c5 f ξ + tlWOneXP3c4 f ξ))
  | 6 =>
      ((tlWOneXP0c6 f ξ + tlWOneXP1c6 f ξ) +
                  (tlWOneXP2c6 f ξ + tlWOneXP3c5 f ξ))
  | 7 =>
      ((tlWOneXP0c7 f ξ + tlWOneXP1c7 f ξ) +
                  (tlWOneXP2c7 f ξ + tlWOneXP3c6 f ξ))
  | 8 =>
      ((tlWOneXP0c8 f ξ + tlWOneXP1c8 f ξ) +
                  (tlWOneXP2c8 f ξ + tlWOneXP3c7 f ξ))
  | 9 =>
      ((tlWOneXP0c9 f ξ + tlWOneXP1c9 f ξ) +
                  (tlWOneXP2c9 f ξ + tlWOneXP3c8 f ξ))
  | 10 =>
      ((tlWOneXP0c10 f ξ + tlWOneXP1c10 f ξ) +
                  (tlWOneXP2c10 f ξ + tlWOneXP3c9 f ξ))
  | 11 =>
      ((tlWOneXP0c11 f ξ + tlWOneXP1c11 f ξ) +
                  (tlWOneXP2c11 f ξ + tlWOneXP3c10 f ξ))
  | 12 =>
      ((tlWOneXP0c12 f ξ + tlWOneXP1c12 f ξ) +
                  (tlWOneXP2c12 f ξ + tlWOneXP3c11 f ξ))
  | 13 =>
      ((tlWOneXP0c13 f ξ + tlWOneXP1c13 f ξ) +
                  (tlWOneXP2c13 f ξ + tlWOneXP3c12 f ξ))
  | 14 => (tlWOneXP0c14 f ξ + (tlWOneXP1c14 f ξ + tlWOneXP2c14 f ξ))
  | 15 => (tlWOneXP1c15 f ξ + tlWOneXP2c15 f ξ)
  | 16 => (tlWOneXP1c16 f ξ + tlWOneXP2c16 f ξ)
  | 17 => tlWOneXP2c17 f ξ
  | 18 => tlWOneXP2c18 f ξ
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell14 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => 0
  | 1 => tlWOneXP4c0 f
  | 2 => tlWOneXP4c1 f ξ
  | 3 => (tlWOneXP4c2 f ξ + tlWOneXP5c0 f ξ)
  | 4 => (tlWOneXP4c3 f ξ + tlWOneXP5c1 f ξ)
  | 5 => (tlWOneXP4c4 f ξ + tlWOneXP5c2 f ξ)
  | 6 => (tlWOneXP4c5 f ξ + tlWOneXP5c3 f ξ)
  | 7 => (tlWOneXP4c6 f ξ + tlWOneXP5c4 f ξ)
  | 8 => (tlWOneXP4c7 f ξ + tlWOneXP5c5 f ξ)
  | 9 => (tlWOneXP4c8 f ξ + tlWOneXP5c6 f ξ)
  | 10 => (tlWOneXP4c9 f ξ + tlWOneXP5c7 f ξ)
  | 11 => (tlWOneXP4c10 f ξ + tlWOneXP5c8 f ξ)
  | 12 => (tlWOneXP4c11 f ξ + tlWOneXP5c9 f ξ)
  | 13 => (tlWOneXP4c12 f ξ + tlWOneXP5c10 f ξ)
  | 14 => (tlWOneXP3c13 f ξ + (tlWOneXP4c13 f ξ + tlWOneXP5c11 f ξ))
  | 15 => (tlWOneXP3c14 f ξ + (tlWOneXP4c14 f ξ + tlWOneXP5c12 f ξ))
  | 16 => (tlWOneXP3c15 f ξ + (tlWOneXP4c15 f ξ + tlWOneXP5c13 f ξ))
  | 17 => (tlWOneXP3c16 f ξ + (tlWOneXP4c16 f ξ + tlWOneXP5c14 f ξ))
  | 18 => (tlWOneXP3c17 f ξ + (tlWOneXP4c17 f ξ + tlWOneXP5c15 f ξ))
  | 19 => (tlWOneXP3c18 f ξ + (tlWOneXP4c18 f ξ + tlWOneXP5c16 f ξ))
  | 20 => (tlWOneXP3c19 f ξ + (tlWOneXP4c19 f ξ + tlWOneXP5c17 f ξ))
  | 21 => (tlWOneXP4c20 f ξ + tlWOneXP5c18 f ξ)
  | 22 => tlWOneXP5c19 f ξ
  | 23 => tlWOneXP5c20 f ξ
  | _ => 0

@[irreducible]  def tlRowCell15 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => tlWZeroXP0c0 f ξ
  | 1 => (tlWZeroXP0c1 f ξ + tlWZeroXP1c0 f ξ)
  | 2 => (tlWZeroXP0c2 f ξ + tlWZeroXP1c1 f ξ)
  | 3 => (tlWZeroXP0c3 f ξ + (tlWZeroXP1c2 f ξ + tlWZeroXP2c0 f ξ))
  | 4 => (tlWZeroXP0c4 f ξ + (tlWZeroXP1c3 f ξ + tlWZeroXP2c1 f ξ))
  | 5 => (tlWZeroXP0c5 f ξ + (tlWZeroXP1c4 f ξ + tlWZeroXP2c2 f ξ))
  | 6 => (tlWZeroXP0c6 f ξ + (tlWZeroXP1c5 f ξ + tlWZeroXP2c3 f ξ))
  | 7 => (tlWZeroXP0c7 f ξ + (tlWZeroXP1c6 f ξ + tlWZeroXP2c4 f ξ))
  | 8 =>
      ((tlWZeroXP0c8 f ξ + tlWZeroXP1c7 f ξ) +
                  (tlWZeroXP2c5 f ξ + tlWZeroXP3c0 f ξ))
  | 9 =>
      ((tlWZeroXP0c9 f ξ + tlWZeroXP1c8 f ξ) +
                  (tlWZeroXP2c6 f ξ + tlWZeroXP3c1 f ξ))
  | 10 =>
      ((tlWZeroXP0c10 f ξ + tlWZeroXP1c9 f ξ) +
                  (tlWZeroXP2c7 f ξ + tlWZeroXP3c2 f ξ))
  | 11 =>
      ((tlWZeroXP0c11 f ξ + tlWZeroXP1c10 f ξ) +
                  (tlWZeroXP2c8 f ξ + tlWZeroXP3c3 f ξ))
  | 12 =>
      ((tlWZeroXP0c12 f ξ + tlWZeroXP1c11 f ξ) +
                  (tlWZeroXP2c9 f ξ + tlWZeroXP3c4 f ξ))
  | 13 =>
      ((tlWZeroXP0c13 f ξ + tlWZeroXP1c12 f ξ) +
                  (tlWZeroXP2c10 f ξ + tlWZeroXP3c5 f ξ))
  | 14 =>
      ((tlWZeroXP0c14 f ξ + tlWZeroXP1c13 f ξ) +
                  (tlWZeroXP2c11 f ξ + tlWZeroXP3c6 f ξ))
  | 15 =>
      ((tlWZeroXP0c15 f ξ + tlWZeroXP1c14 f ξ) +
                  (tlWZeroXP2c12 f ξ + tlWZeroXP3c7 f ξ))
  | 16 => (tlWZeroXP0c16 f ξ + (tlWZeroXP1c15 f ξ + tlWZeroXP2c13 f ξ))
  | 17 => (tlWZeroXP1c16 f ξ + tlWZeroXP2c14 f ξ)
  | 18 => (tlWZeroXP1c17 f ξ + tlWZeroXP2c15 f ξ)
  | 19 => (tlWZeroXP1c18 f ξ + tlWZeroXP2c16 f ξ)
  | 20 => tlWZeroXP2c17 f ξ
  | 21 => tlWZeroXP2c18 f ξ
  | 22 => tlWZeroXP2c19 f ξ
  | 23 => 0
  | _ => 0

@[irreducible]  def tlRowCell16 (f ξ : ℚ) (band : Fin 24) : ℚ :=
  match band.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => tlWZeroXP3c8 f ξ
  | 17 => tlWZeroXP3c9 f ξ
  | 18 => tlWZeroXP3c10 f ξ
  | 19 => tlWZeroXP3c11 f ξ
  | 20 => tlWZeroXP3c12 f ξ
  | 21 => tlWZeroXP3c13 f ξ
  | 22 => tlWZeroXP3c14 f ξ
  | 23 => tlWZeroXP3c15 f ξ
  | _ => 0

 def tlColumn (f ξ : ℚ) (band : Fin 24) : ℚ :=
  (((((((tlRowCell0 f ξ band + tlRowCell1 f ξ band) +
           (tlRowCell2 f ξ band + tlRowCell3 f ξ band)) +
          ((tlRowCell4 f ξ band + tlRowCell5 f ξ band) +
            (tlRowCell6 f ξ band + tlRowCell7 f ξ band))) +
         ((tlRowCell8 f ξ band + tlRowCell9 f ξ band) + tlRowCell10 f ξ band)) +
        (tlRowCell11 f ξ band + tlRowCell12 f ξ band)) +
       (tlRowCell13 f ξ band + tlRowCell14 f ξ band)) +
      (tlRowCell15 f ξ band + tlRowCell16 f ξ band))

end MazurTorsion.Kubert
end


