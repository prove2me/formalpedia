-- Prove2me | Definitions.Def_TractableComposite_phiBar
-- name    : TractableComposite_phiBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:43.332204+00:00
-- url     : https://prove2.me/theorems/0ba532b5-3b74-4e91-b2a4-5404b75a4473
-- title:
--   The extension $\bar\phi(s)=\phi(s_{1n},\dots,s_{dn})$
-- statement:
--   Given an outer-function $\phi:\mathbb R^d\to\mathbb R$, its extension $\bar\phi:\mathbb R^{d\times(n+1)}\to\mathbb R$ reads only the last column:
--
--   $$\bar\phi(s)=\phi(s_{1n},\dots,s_{dn}).$$
--
--   The concave envelopes $\operatorname{conc}_P(\bar\phi)$ and $\operatorname{conc}_Q(\bar\phi)$ of this extension are the objects of the mission.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), §2.1, p.3, and Proposition 4, p.10

import Mathlib

namespace TractableComposite

/-- **The extension φ̄ of the outer-function.** He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), §2.1, p.3, and Proposition 4, p.10:
`φ̄(s) = φ(s₁ₙ, …, s_dn)` for `s ∈ ℝ^{d×(n+1)}`.

**Formalization Note.** `Fin.last n` is the paper's column `n`. -/
def phiBar {d n : ℕ} (φ : (Fin d → ℝ) → ℝ) (u : Fin d → Fin (n + 1) → ℝ) : ℝ :=
  φ (fun i => u i (Fin.last n))

end TractableComposite


