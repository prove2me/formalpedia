-- Prove2me | Definitions.Def_TractableComposite_Jof
-- name    : TractableComposite_Jof
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:11.736218+00:00
-- url     : https://prove2.me/theorems/5492fe3a-dd7b-4898-9de7-c1b9458b80e6
-- title:
--   The index sets $J_i=\{j\mid\bar u_{ij}=\bar s_{ij}\}$
-- statement:
--   For $\bar u\in P$ with lifting $\bar s$, $J_i=\{j\mid \bar u_{ij}=\bar s_{ij}\}$: the columns at which $\bar u_i$ touches its concave envelope.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 1, p.5; Proposition 2, p.6; Theorem 2's proof, p.14

import Mathlib
import Definitions.Def_TractableComposite_liftS

namespace TractableComposite

/-- **The index sets Jᵢ = {j | ūᵢⱼ = s̄ᵢⱼ}**, Proposition 1, p.5, Proposition 2, p.6, Theorem 2's proof,
p.14. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), pp.5, 6, 14.

**Formalization Note.** `s̄ = liftS a ū`; the filter uses classical decidability of real equality (a
mathematical definition, not a program step; the program `facetGen` computes the same sets by ticked
equality tests). -/
noncomputable def Jof {d n : ℕ} (a u : Fin d → Fin (n + 1) → ℝ) : Fin d → Finset (Fin (n + 1)) := by
  classical
  exact fun i => Finset.univ.filter (fun j => u i j = liftS a u i j)

end TractableComposite


