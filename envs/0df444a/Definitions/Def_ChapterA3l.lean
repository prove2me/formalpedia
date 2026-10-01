-- Prove2me | Definitions.Def_ChapterA3l
-- name    : ChapterA3l
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:23:46.84132+00:00
-- url     : https://prove2.me/theorems/3553bdb5-6fbe-4704-89c1-1205fafc2e39
-- title:
--   Chapter A3l
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3l.lean`): generated def bundle for ChapterA3l. See BookProof/ChapterA3l.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3l.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3k
import Mathlib


/-!
# Chapter A, §A.3 — Note 51 / Lemma 52: the symmetric tensor-square structure

Source: `book.tex` §A.3, Notes 50–51 and Lemma 52 (line ~5560).

`ChapterA3k` formalized the **tensor square** `V ⊗ V` of the Dirac spinor and its
four chirality blocks `V⁺⊗V⁺` (label `(1,0)`), `V⁻⊗V⁻` (`(0,1)`), and the two
mixed blocks `V⁺⊗V⁻`, `V⁻⊗V⁺` (`(½,½)`), showing that the *diagonal* `Spin⁺`
action preserves each block and that *diagonal parity* `γ⁰⊗γ⁰` glues `(1,0)` to
`(0,1)`.

This file takes the **next step**: Note 51 builds the general irreps `V_{(m,n)}`
as *symmetric* tensor powers of the chiral spinors, so we need the **braiding
(swap) operator** `τ : u ⊗ v ↦ v ⊗ u` on `V ⊗ V` and the symmetric /
antisymmetric decomposition it induces.  On the `4×4 ⊗ 4×4` Kronecker model of
§A.3 the swap is the commutation matrix `τ_{(i,j),(k,l)} = [i=l ∧ j=k]`, and we
prove:

* **Braiding relation** `swap_kronecker`: `τ · (A ⊗ B) = (B ⊗ A) · τ` for all
  `A, B`; in particular `τ` is an involution (`swap_sq`) and it *exchanges the
  two per-slot chirality operators* (`swap_chir1`, `swap_chir2`).
* **`τ` commutes with the diagonal Lorentz / parity action** (`swap_spinGenDiag_comm`,
  `swap_parityDiag_comm`), because `A ⊗ 1 + 1 ⊗ A` and `γ⁰ ⊗ γ⁰` are symmetric
  under the exchange of the two slots.
* **`τ` fixes the pure chirality blocks and exchanges the mixed ones**
  (`swap_projLL_comm`, `swap_projRR_comm`, `swap_swaps_LR_RL`): the two `(½,½)`
  blocks `V⁺⊗V⁻ ↔ V⁻⊗V⁺` are braided into each other, exactly as they are glued
  by parity in `ChapterA3k`.
* **Symmetric / antisymmetric projectors** `projSym = ½(1+τ)`, `projAsym = ½(1-τ)`
  (`projSym_idem`, `projAsym_idem`, `projSym_add_projAsym`): the symmetric part is
  the carrier of the **symmetric tensor square** — the Note-51 `V⁺_1 ⊕ V⁻_1 ⊕ …`
  layer.  It is a **full-Lorentz** subrepresentation: it commutes with both the
  diagonal `Spin⁺` action **and** diagonal parity (`projSym_spinGenDiag_comm`,
  `projSym_parityDiag_comm`) — the Lemma-52 payoff that the *real* (symmetric)
  tensor construction is automatically parity-invariant, unlike a single pure
  chirality block.

Everything is a Kronecker-algebra consequence of `ChapterA3j`/`ChapterA3k` and is
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`),
with **no `EXTERNAL` hypothesis** (Note 50 / Weyl complete reducibility and the
extension to arbitrary `N`-fold symmetric powers remain the cited backbone).
-/

open Matrix
open scoped Kronecker

namespace BookProof.ChapterA3l

open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

/-- The braiding (commutation) matrix `τ` on `V ⊗ V`, i.e. the linear operator
`u ⊗ v ↦ v ⊗ u`.  Entrywise `τ_{(i,j),(k,l)} = [i = l ∧ j = k]`. -/
noncomputable def swap : M2 :=
  Matrix.of fun a b => if a.1 = b.2 ∧ a.2 = b.1 then (1 : ℂ) else 0

/-! ## The braiding relation and involutivity -/

/-
**Braiding relation.** `τ · (A ⊗ B) = (B ⊗ A) · τ` for all `A, B`.
-/


/-
The braiding is an involution: `τ² = 1`.
-/


/-! ## The braiding exchanges the two per-slot chirality operators -/





/-! ## The braiding commutes with the diagonal Lorentz / parity action -/





/-! ## The braiding fixes the pure blocks and exchanges the mixed ones -/









/-! ## The symmetric / antisymmetric decomposition -/

/-- The symmetric projector `P_sym = ½(1 + τ)` onto the symmetric tensor square
`V ⊙ V` — the Note-51 symmetric-tensor-power carrier. -/
noncomputable def projSym : M2 := (2 : ℂ)⁻¹ • (1 + swap)

/-- The antisymmetric projector `P_asym = ½(1 - τ)` onto `V ∧ V`. -/
noncomputable def projAsym : M2 := (2 : ℂ)⁻¹ • (1 - swap)









/-! ## The symmetric tensor square is a full-Lorentz subrepresentation -/









/-! ## The pure `(1,0)` block lies in the symmetric part -/



end BookProof.ChapterA3l


