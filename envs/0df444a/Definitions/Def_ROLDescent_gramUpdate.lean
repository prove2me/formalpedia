-- Prove2me | Definitions.Def_ROLDescent_gramUpdate
-- name    : ROLDescent_gramUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:03.258386+00:00
-- url     : https://prove2.me/theorems/9f2663df-8b7a-4ec7-8fe7-5d319707f96f
-- title:
--   Gram update $F_\lambda(c)$
-- statement:
--   The **Gram update** is
--
--   $$F_\lambda(c) = \frac{(2 - \lambda)\, c}{\lambda (1 - c)} \qquad (0 < \lambda \le 2,\ 0 \le c < 1).$$
--
--   It propagates the largest child Gram bound $c$ to a Gram bound at the parent when the parent's link walk has spectral gap at least $\lambda$. On its domain, $F_\lambda(c) < 1$ exactly when $c < \lambda/2$.
--
--   **Formalization Note** Real division, total on $\mathbb R$; statements read it only on the paper's domain.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.2, p.32 (PDF 32)

import Mathlib

namespace ROLDescent

/-- **Gram update** `F_λ`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.2, p.32 (PDF 32): "Write
F_λ(c) := (2 − λ)c / (λ(1 − c)) (0 < λ ≤ 2, 0 ≤ c < 1)."

**Formalization Note** Real division, total on ℝ; every statement reads it only on the paper's
domain `0 < λ`, `0 ≤ c < 1` (with `λ ≤ 2` where the paper assumes it). -/
noncomputable def gramUpdate (lam c : ℝ) : ℝ := (2 - lam) * c / (lam * (1 - c))

end ROLDescent


