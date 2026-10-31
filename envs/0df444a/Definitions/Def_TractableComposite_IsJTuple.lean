-- Prove2me | Definitions.Def_TractableComposite_IsJTuple
-- name    : TractableComposite_IsJTuple
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:48.249431+00:00
-- url     : https://prove2.me/theorems/2410d84f-863d-4768-9398-c110869281a4
-- title:
--   The $d$-tuples $\mathcal J$ of index sets
-- statement:
--   $$\mathcal J=\{(J_1,\dots,J_d)\mid \{0,n\}\subseteq J_i\subseteq\{0,1,\dots,n\}\ \forall i\}.$$
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (5), p.5

import Mathlib

namespace TractableComposite

/-- **The d-tuples 𝒥**, (5), p.5: `J = (J₁,…,J_d)` with `{0, n} ⊆ Jᵢ ⊆ {0,…,n}` for every `i`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (5), p.5. -/
def IsJTuple {d n : ℕ} (J : Fin d → Finset (Fin (n + 1))) : Prop :=
  ∀ i, 0 ∈ J i ∧ Fin.last n ∈ J i

end TractableComposite


