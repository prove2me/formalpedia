-- Prove2me | Definitions.Def_RolesForceSeven_fano
-- name    : RolesForceSeven_fano
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-24T05:41:56.624685+00:00
-- url     : https://prove2.me/theorems/bda4f3e6-5e89-49e4-8862-442d2cbdcdcb
-- title:
--   The Fano plane as a Steiner triple system on $7$ points
-- statement:
--   For $i \in \mathbb{Z}/7\mathbb{Z}$ let $L_i = \{i,\ i+1,\ i+3\}$, with addition modulo $7$. The **Fano plane** is the Steiner triple system on $\{0, \dots, 6\}$ whose lines are the seven sets
--
--   $$
--   \{0,1,3\},\ \{1,2,4\},\ \{2,3,5\},\ \{3,4,6\},\ \{0,4,5\},\ \{1,5,6\},\ \{0,2,6\}.
--   $$
--
--   Every line has three points, and every two distinct points lie on exactly one line.
--
--   **Formalization Note** `fanoLine i` is $L_i$ in `Finset (Fin 7)`, and `fano : STS 7` has lines `Finset.univ.image fanoLine`. The two structure properties are checked by finite computation (`decide`).
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3, Theorem 3.3 and Theorem 3.6 (the Fano plane): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Section 3: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md ; public references: Wikipedia, "Steiner system" (Steiner triple systems, replication number): https://en.wikipedia.org/wiki/Steiner_system ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Octonion" (Fano plane mnemonic for the multiplication of imaginary units): https://en.wikipedia.org/wiki/Octonion

import Mathlib
import Definitions.Def_RolesForceSeven_sts

namespace RolesForceSeven

/-- The Fano plane: lines {i, i+1, i+3} mod 7. -/
def fanoLine (i : Fin 7) : Finset (Fin 7) := {i, i + 1, i + 3}

set_option maxRecDepth 100000 in
def fano : STS 7 where
  lines := Finset.univ.image fanoLine
  card_three := by decide
  pair_unique := by
    have hex : ∀ x y : Fin 7, x ≠ y → ∃ i, x ∈ fanoLine i ∧ y ∈ fanoLine i := by decide
    have huniq : ∀ x y : Fin 7, x ≠ y → ∀ i j, x ∈ fanoLine i → y ∈ fanoLine i →
        x ∈ fanoLine j → y ∈ fanoLine j → fanoLine i = fanoLine j := by decide
    intro x y hxy
    obtain ⟨i, hxi, hyi⟩ := hex x y hxy
    refine ⟨fanoLine i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hxi, hyi⟩, ?_⟩
    rintro l ⟨hl, hxl, hyl⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hl
    exact huniq x y hxy j i hxl hyl hxi hyi

end RolesForceSeven


