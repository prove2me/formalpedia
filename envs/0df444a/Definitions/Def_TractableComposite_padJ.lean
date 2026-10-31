-- Prove2me | Definitions.Def_TractableComposite_padJ
-- name    : TractableComposite_padJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:05.352868+00:00
-- url     : https://prove2.me/theorems/b790d1b8-7f05-4071-9e80-dfc51a5bd233
-- title:
--   The vector $(y_J,0)$
-- statement:
--   A $J$-indexed vector $y_J$ is extended to $\mathbb R^{d\times(n+1)}$ by zero on the complementary coordinates $\bar J$. Proposition 2 uses it to write the inequality $\phi\le\langle(\alpha_J,0),(u_J,u_{\bar J})\rangle+b$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 2, p.6

import Mathlib

namespace TractableComposite

/-- **The vector (y_J, 0)**, Proposition 2, p.6 (`(α_J, 0)`): a `J`-indexed vector extended by `0` on the
complement `J̄`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Proposition 2, p.6. -/
def padJ {d n : ℕ} (J : Fin d → Finset (Fin (n + 1))) (y : (i : Fin d) → J i → ℝ) : Fin d → Fin (n + 1) → ℝ :=
  fun i j => if h : j ∈ J i then y i ⟨j, h⟩ else 0

end TractableComposite


