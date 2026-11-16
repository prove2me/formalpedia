-- Prove2me | Definitions.Def_CompDesign_Supplement_kappaGamma
-- name    : CompDesign_Supplement_kappaGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:50:22.256227+00:00
-- url     : https://prove2.me/theorems/d816986d-f157-40a2-8faf-55e5a77ccbc5
-- title:
--   $\kappa_\gamma(\lambda)$ of Theorem B.1
-- statement:
--   For $\gamma>0$ and $0\le\lambda<\gamma$,
--   $$\kappa_\gamma(\lambda)=\max\Big\{\sum_i\frac{x_i}{\gamma-x_i}\ :\ 0\le x_i\le\lambda,\ \sum_ix_i\le1\Big\},$$
--   over all finite families $(x_i)$. For $\gamma=1$ it is the cost concentration term $\kappa(\lambda)$ of (20).
--
--   **Formalization Note** Written exactly as the published `CompDesign.kappa`: a real supremum over all `m` and `x : Fin m → ℝ`, with denominator $\gamma-x_j$. For $0\le\lambda<\gamma$ the set is nonempty and bounded above by $1/(\gamma-\lambda)$, so the supremum is genuine and no division by zero occurs.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem B.1, p.70 (PDF 73)

import Mathlib

namespace CompDesign.Supplement

/-- The term `κ_γ(λ) = max { ∑_i x_i/(γ − x_i) : 0 ≤ x_i ≤ λ, ∑_i x_i ≤ 1 }` of Theorem B.1,
p.70 (PDF 73), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…).

**Formalization Note.** Written exactly as the published `CompDesign.kappa` (an `sSup` over all finite
families `x : Fin m → ℝ`, every `m`), with denominator `γ − x_j`; `κ_1 = CompDesign.kappa`. For
`0 ≤ l < γ` the set is nonempty (`m = 0`) and bounded above by `1/(γ − l)`, and `x_j ≤ l < γ`, so no
division by zero occurs. -/
noncomputable def kappaGamma (γ l : ℝ) : ℝ :=
  sSup {s : ℝ | ∃ (m : ℕ) (x : Fin m → ℝ), (∀ j, 0 ≤ x j ∧ x j ≤ l) ∧ ∑ j, x j ≤ 1 ∧
    s = ∑ j, x j / (γ - x j)}

end CompDesign.Supplement


