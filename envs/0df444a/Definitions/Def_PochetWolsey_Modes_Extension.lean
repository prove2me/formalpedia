-- Prove2me | Definitions.Def_PochetWolsey_Modes_Extension
-- name    : PochetWolsey_Modes_Extension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:04.981888+00:00
-- url     : https://prove2.me/theorems/2b4be29e-c33b-4b86-b878-e80139133a66
-- title:
--   The printed diagonal extension for arbitrary setup counts
-- statement:
--   For setup, startup and switch-off arrays $(y,z,w)$, introduce a single auxiliary array $\phi_i(t)$ representing only the diagonal coordinate $\phi^{ii}_t$. The extension is the unit-box system
--   $$\sum_j(y_j(t)-z_j(t))=1,\qquad y_i(t+1)-z_i(t+1)=y_i(t)-w_i(t),$$
--   $$y_i(t)-z_i(t)\ge\phi_i(t),\quad y_i(t)-w_i(t)\ge\phi_i(t),\quad\phi_i(t)\ge y_i(t)-z_i(t)-w_i(t),$$
--   $$y_i(t)+\sum_{j\ne i}\phi_j(t)\le1.$$
--   The continuity equation applies to adjacent periods; the other constraints apply to every period. The projected set consists of those $(y,z,w)$ for which such an auxiliary array exists. This records exactly the displayed extension, including its lack of a terminal normalization for $y-w$.
--
--   **Formalization Note** There are $m+1$ labels, including idle label $0$, and $n+1$ periods, numbered $0,\ldots,n$. Thus $m=n=0$ means one idle label and one period, not empty index sets.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 381 (PDF 392), Proposition 12.7

import Mathlib

namespace PochetWolsey.Modes

/-- The displayed system in Proposition 12.7, without an added terminal equation.
The auxiliary grid stores only the diagonal variables φ^{ii}_t. -/
def arbitraryModeExtension {m n : ℕ} (p : ((Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ))) (φ : (Fin (m + 1) → Fin (n + 1) → ℝ)) : Prop :=
  (∀ i, (∀ t, 0 ≤ p.1 i t ∧ p.1 i t ≤ 1)) ∧
  (∀ i, (∀ t, 0 ≤ p.2.1 i t ∧ p.2.1 i t ≤ 1)) ∧
  (∀ i, (∀ t, 0 ≤ p.2.2 i t ∧ p.2.2 i t ≤ 1)) ∧
  (∀ i, (∀ t, 0 ≤ φ i t ∧ φ i t ≤ 1)) ∧
  (∀ t, ∑ j, (p.1 j t - p.2.1 j t) = 1) ∧
  (∀ i (t : Fin n), p.1 i t.succ - p.2.1 i t.succ =
    p.1 i t.castSucc - p.2.2 i t.castSucc) ∧
  (∀ i t, p.1 i t - p.2.1 i t ≥ φ i t) ∧
  (∀ i t, p.1 i t - p.2.2 i t ≥ φ i t) ∧
  (∀ i t, φ i t ≥ p.1 i t - p.2.1 i t - p.2.2 i t) ∧
  (∀ i t, p.1 i t + ∑ j ∈ Finset.univ.erase i, φ j t ≤ 1)

def arbitraryModeProjection (m n : ℕ) : Set (((Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ))) :=
  {p | ∃ φ : (Fin (m + 1) → Fin (n + 1) → ℝ), arbitraryModeExtension p φ}

end PochetWolsey.Modes


