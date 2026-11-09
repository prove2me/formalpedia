-- Prove2me | Definitions.Def_LinfContractionFP_unitCube
-- name    : LinfContractionFP_unitCube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:55.188059+00:00
-- url     : https://prove2.me/theorems/b8b73f0a-5042-4742-bffc-891e4a057b4c
-- title:
--   The unit cube $[0,1]^\iota$
-- statement:
--   For a finite coordinate set $\iota$, the **unit cube** is
--   $$[0,1]^\iota=\{x\in\mathbb R^\iota : 0\le x_i\le 1\ \text{for all } i\in\iota\}.$$
--   The paper's $[0,1]^d$ is $\iota=\{1,\dots,d\}$.
--
--   **Formalization Note** A general finite index type is used so that the restricted maps of Section 5, defined on the coordinates of a subset $N\subseteq[d]$, live in the same framework. On $\mathbb R^\iota$ Mathlib's norm is the sup norm, i.e. $\|\cdot\|_\infty$.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 1, p.1

import Mathlib

namespace LinfContractionFP

/-- The unit cube `[0,1]^ι` of a finite coordinate set `ι`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Section 1, p.1: "Let f : [0, 1]^d → [0, 1]^d be an ℓ∞-contraction".

**Formalization Note.** Points are functions `ι → ℝ`; the paper's `[0,1]^d` is `ι = Fin d`.
A general finite index type is used so that the restricted maps of Section 5 (coordinates in a
subset `N ⊆ [d]`) live on `↥N → ℝ` with the same definitions. On `ι → ℝ` (with `[Fintype ι]`)
Mathlib's norm `‖·‖` is the sup norm, i.e. the paper's `‖·‖∞`. -/
def unitCube (ι : Type) : Set (ι → ℝ) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

end LinfContractionFP


