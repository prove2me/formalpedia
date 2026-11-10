-- Prove2me | Definitions.Def_Pr6453RootAddress
-- name    : Pr6453RootAddress
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-09T09:01:04.965846+00:00
-- url     : https://prove2.me/theorems/47eda994-485f-451f-9c80-0ccee5b85ff8
-- title:
--   PR #6453: the root's address structure (sign, mask, field)
-- statement:
--   The address structure of the PR #6453 root, read off ROOT.json: six fields, four full stages, the six-by-four full-site mask table, and the coefficient address as a triple (sign, mask, field). The masks count 16, the addresses 192, and two signs times sixteen masks times thirty-six field-matrix entries is the 1152 independent stage coefficients the certificate prints.
--
--   This is the index set over which the root's polynomial is expanded: module_check.py builds expected[mask][j][j] = 1 for each field j whose mask is `mask`, compares the word against it in both signs, and checks the projector identities, the chronological commutation, the mask expansion, the four-operation normalization, the Gaussian characters and the tensor rule — all finite rational matrix algebra.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/mixed-projector-query-root/ROOT.json (fields, sites, masks, independent_stage_coefficients) and module_check.py.

/-
# PR #6453: the root's address structure

Read off `research/mixed-projector-query-root/ROOT.json`: six fields, seven sites (four full, three
thin) of ranks `2,3,2,2,2,3,2`, four query trees of `7,2,2,7` leaves, six-by-six input and output
bases with 36 nonzeros each, and the six-by-four full-site mask table

```
[[1,1,1,1], [1,1,0,0], [0,0,1,1], [0,0,0,0], [0,0,1,0], [0,1,0,0]].
```

The address of a coefficient is a triple `(sign, mask, j)`: the sign of the character, the subset of
the four full stages that have been passed, and the field. That is `2 · 16 · 6 = 192` diagonal
coordinates, or `2 · 16 · 36 = 1152` if each field carries a full six-by-six matrix — which is the
`independent_stage_coefficients` the certificate prints.
-/
import Mathlib

set_option autoImplicit false

namespace Pr6453Root

/-- The six fields of the root. -/
abbrev Field' := Fin 6

/-- The four full stages, whose passed-or-not bits form the mask. -/
abbrev Stage := Fin 4

/-- The mask of a coefficient: which full stages it has passed. -/
abbrev Mask := Finset Stage

/-- The sign of a character. -/
abbrev Sign := Bool

/-- **The address of a root coefficient**: `(sign, mask, field)`. -/
abbrev Address := Sign × Mask × Field'

theorem mask_count : Fintype.card Mask = 16 := by
  simp [Mask, Fintype.card_finset]

theorem address_count : Fintype.card Address = 192 := by
  simp [Address, Fintype.card_prod, mask_count]

/-- The full-site mask table read off `ROOT.json → masks`, one row per field. -/
def maskTable : Field' → Stage → Bool :=
  ![
    ![true,  true,  true,  true ],
    ![true,  true,  false, false],
    ![false, false, true,  true ],
    ![false, false, false, false],
    ![false, false, true,  false],
    ![false, true,  false, false]
  ]

/-- The mask attached to a field: the full stages its coefficient has passed. -/
def fieldMask (j : Field') : Mask :=
  Finset.univ.filter (fun s => maskTable j s)

/-- The polynomial the root computes: the sum over the passed masks of the diagonal of the field
matrix, with the character's sign. `module_check.py` builds exactly this in `expected`
(`expected[mask][j][j] = 1` for each field `j` whose mask is `mask`) and compares the word against it
in both signs. -/
def expected (sign : Sign) (j : Field') : Mask → Field' → ℚ :=
  fun m j' => if j' = j ∧ m = fieldMask j then (if sign then 1 else -1) else 0

/-- **The count the certificate prints.** Two signs, sixteen masks, thirty-six field-matrix entries:
`1152`. -/
theorem stage_coefficients : 2 * Fintype.card Mask * 36 = 1152 := by
  rw [mask_count]

/-- Every field's mask is a subset of the four full stages, so the address space is the one above. -/
theorem fieldMask_subset (j : Field') : fieldMask j ⊆ Finset.univ :=
  Finset.subset_univ _

end Pr6453Root


