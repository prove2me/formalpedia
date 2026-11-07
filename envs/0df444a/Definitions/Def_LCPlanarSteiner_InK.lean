-- Prove2me | Definitions.Def_LCPlanarSteiner_InK
-- name    : LCPlanarSteiner_InK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:24.881231+00:00
-- url     : https://prove2.me/theorems/6b78e76d-863f-45e7-b0bf-2ab8f5213fe1
-- title:
--   The surviving vertex set $K_R$ of the separator host
-- statement:
--   Given a region $(C, B, E_R)$, a length horizon $H > 0$ and a cost estimate $\Gamma > 0$, use the mixed weights
--   $$
--   c'_e = c_e + \frac{\Gamma\, \ell_e}{H}.
--   $$
--   A vertex $v$ belongs to $K_R$ when $v \in C$ and some walk of owned arcs from a boundary vertex to $v$ has mixed weight at most $2\Gamma$, i.e. its distance from the contracted boundary is at most $2\Gamma$.
--
--   The separator host of the paper is the contracted graph restricted to the boundary vertex and $K_R$.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §3.1, p.5

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsWalk

namespace LCPlanarSteiner

/-- **The surviving vertex set `K_R` of the separator host.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §3.1, p.5: "For separator topology only, contract B to one vertex. Given a length horizon H
and cost estimate Γ > 0, use mixed weights c′_e = c_e + Γℓ_e/H and let K_R ⊆ C consist of vertices
at contracted distance at most 2Γ."

`InK G C B ER H Γ v`: `v ∈ C` and some walk of owned arcs (in `E_R`) from a boundary vertex `b ∈ B` to
`v` has mixed weight `Σ_e (c_e + Γ ℓ_e / H) ≤ 2Γ`.

**Formalization Note.** With `B` contracted to one vertex `b_R`, a contracted walk from `b_R` is an
owned walk from some `b ∈ B` (owned arcs never enter `B`). -/
def InK (G : Net) (C B ER : Finset ℕ) (H Γ : ℚ) (v : ℕ) : Prop :=
  v ∈ C ∧ ∃ b ∈ B, ∃ q : List ℕ, IsWalk G b v q ∧ (∀ e ∈ q, e ∈ ER) ∧
    (q.map fun e => G.cst e + Γ * G.lng e / H).sum ≤ 2 * Γ

end LCPlanarSteiner


