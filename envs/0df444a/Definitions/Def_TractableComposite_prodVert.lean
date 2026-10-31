-- Prove2me | Definitions.Def_TractableComposite_prodVert
-- name    : TractableComposite_prodVert
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:44.947002+00:00
-- url     : https://prove2.me/theorems/448f6fa7-5a25-4fa6-a407-72bbcf73d54a
-- title:
--   The vertex grid of a product of simplices
-- statement:
--   Given vertex lists $\upsilon_{i0},\dots,\upsilon_{in}$ for $i=1,\dots,d$, this is the set of points $(\upsilon_{1j_1},\dots,\upsilon_{dj_d})$ with $(j_1,\dots,j_d)\in\{0,\dots,n\}^d$. These are the extreme points of $\prod_i\operatorname{conv}\{\upsilon_{i0},\dots,\upsilon_{in}\}$ when each list is affinely independent.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), §2.2, p.7 ("The extreme points of S, which are ∏ᵢ{νᵢ₀,…,νᵢₙ}")

import Mathlib

namespace TractableComposite

/-- **The vertex set of a product of simplices**: the points `(υ_{1 j₁}, …, υ_{d j_d})`, one listed
vertex per factor. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), §2.2, p.7 ("The extreme points of S, which are ∏ᵢ{νᵢ₀,…,νᵢₙ}"); vert(R),
Lemma 2, p.10; vert(Q), p.10. -/
def prodVert {d n : ℕ} (υ : Fin d → Fin (n + 1) → (Fin (n + 1) → ℝ)) : Set (Fin d → Fin (n + 1) → ℝ) :=
  {r | ∃ g : Fin d → Fin (n + 1), r = fun i => υ i (g i)}

end TractableComposite


