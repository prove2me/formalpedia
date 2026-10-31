-- Prove2me | Definitions.Def_TractableComposite_ip
-- name    : TractableComposite_ip
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:41.678442+00:00
-- url     : https://prove2.me/theorems/3df79e03-e551-47b9-b8fc-2d42381808f9
-- title:
--   The pairing $\langle \alpha, u\rangle$
-- statement:
--   For $\alpha, u \in \mathbb R^{d\times(n+1)}$ the pairing is
--
--   $$\langle\alpha,u\rangle=\sum_{i=1}^{d}\sum_{j=0}^{n}\alpha_{ij}u_{ij}.$$
--
--   It is the inner product in which the paper writes every inequality $\phi\le\langle\alpha,s\rangle+b$.
--
--   **Formalization Note.** Points of $\mathbb R^{d\times(n+1)}$ are functions of a row $i$ and a column $j$ (both 0-based, so the column index is the paper's $j\in\{0,\dots,n\}$). The definition allows the column set to depend on the row, so the same pairing also pairs the $J$-indexed vectors $y_J$ of (7).
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), notation of (15), p.11, and of Theorem 2's proof, p.14

import Mathlib

namespace TractableComposite

/-- **The pairing ⟨α, u⟩.** He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), notation of §2–§3 (e.g. (15), p.11; Theorem 2's proof, p.14).
For `α u : (i : ι) → κ i → ℝ`, `ip α u = ∑ᵢ ∑ⱼ αᵢⱼ uᵢⱼ`.

**Formalization Note.** Points of ℝ^{d×(n+1)} are `Fin d → Fin (n+1) → ℝ` (row `i`, column `j`,
0-based, so `j : Fin (n+1)` is the paper's `j ∈ {0,…,n}`). The pairing is stated for a dependent
family `κ` so that the same definition also pairs the `J`-indexed vectors `y_J` of (7), whose
`i`-th block is indexed by the subtype `J i`. -/
def ip {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (α u : (i : ι) → κ i → ℝ) : ℝ :=
  ∑ i, ∑ j, α i j * u i j

end TractableComposite


