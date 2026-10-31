-- Prove2me | Definitions.Def_TractableComposite_phiBarJ
-- name    : TractableComposite_phiBarJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:09.467707+00:00
-- url     : https://prove2.me/theorems/545441d6-f7ee-49a4-888b-99d1acd44a38
-- title:
--   The extension $\bar\phi$ on $Q_J$
-- statement:
--   For $J\in\mathcal J$, $\bar\phi(y_J)=\phi(y_{1n},\dots,y_{dn})$, well defined because $n\in J_i$ for every $i$. Its concave envelope over $Q_J$ appears in Proposition 2 and Lemma 3.
--
--   **Formalization Note.** If $n\notin J_i$ (never the case for $J\in\mathcal J$) the $i$-th argument is $0$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 2, p.6, and Lemma 3, p.14

import Mathlib

namespace TractableComposite

/-- **φ̄ on Q_J**, Proposition 2, p.6 and Lemma 3, p.14: `y_J ↦ φ(y₁ₙ, …, y_dn)`, well defined because
`n ∈ Jᵢ` for `J ∈ 𝒥`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), pp.6, 14.

**Formalization Note.** Reading R7: Proposition 2's printed `conc_{Q_J}(φ)` is the envelope of this
function. If `n ∉ Jᵢ` (never the case for `J ∈ 𝒥`) the `i`-th argument is the junk value `0`. -/
def phiBarJ {d n : ℕ} (φ : (Fin d → ℝ) → ℝ) (J : Fin d → Finset (Fin (n + 1)))
    (y : (i : Fin d) → J i → ℝ) : ℝ :=
  φ (fun i => if h : Fin.last n ∈ J i then y i ⟨Fin.last n, h⟩ else 0)

end TractableComposite


