-- Prove2me | Definitions.Def_PConeEB_Jz
-- name    : PConeEB_Jz
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:36.672639+00:00
-- url     : https://prove2.me/theorems/211ac570-6f75-404b-b133-e2089cd01f43
-- title:
--   The index set $J_z$
-- statement:
--   For $z=(z_0,\bar z)\in\mathbb R^{n+1}$,
--   $$
--   J_z:=\{i\in\{1,\dots,n\}:\bar z_i\ne0\}.
--   $$
--   The size of $J_z$ decides the exponent $\alpha_z$.
--
--   **Formalization Note** The index $i$ in `Fin n` stands for the entry `z i.succ`, so that the 0th entry of $z$ is not counted.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (4.6), p.19

import Mathlib
import Definitions.Def_PConeEB_RR

namespace PConeEB

/-- The index set `J_z := {i | z̄ᵢ ≠ 0} ⊆ {1, …, n}`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (4.6), p.19.

**Formalization Note.** An index `i : Fin n` stands for entry `i.succ`, so the `0`th entry of `z`
is excluded. -/
noncomputable def Jz {n : ℕ} (z : RR n) : Finset (Fin n) :=
  Finset.univ.filter fun i => z i.succ ≠ 0

end PConeEB


