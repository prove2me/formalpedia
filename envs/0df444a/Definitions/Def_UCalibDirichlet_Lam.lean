-- Prove2me | Definitions.Def_UCalibDirichlet_Lam
-- name    : UCalibDirichlet_Lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:28.437277+00:00
-- url     : https://prove2.me/theorems/04fdf677-6974-49f1-ad27-f0544ce135c8
-- title:
--   Dirichlet potential $\Lambda_F(a)=\|a\|_1\,\mathbb E_{P\sim\mathrm{Dir}(a)}[F(P)]$
-- statement:
--   For a function $F:\Delta_K\to\mathbb R$ and a count vector $a\in\mathbb R^K_{>0}$, the **Dirichlet potential** is
--   $$\Lambda_F(a)=\|a\|_1\,\mathbb E_{P\sim\mathrm{Dir}(a)}[F(P)],\qquad \|a\|_1=\sum_j a_j .$$
--   By the count-deletion identity (Lemma 1.3), the loss of the be-the-perturbed-leader forecast in a round is the decrease of $\Lambda_F$ when the observed count is added, which drives the regret decomposition of Algorithm 1.
--
--   **Formalization Note** The expectation is a Bochner integral; for convex finite $F$ and positive parameters $F$ is bounded on the simplex and continuous on its relative interior, which carries $\mathrm{Dir}(a)$, so it is the true expectation.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 1.3, display (7), p.4

import Mathlib
import Definitions.Def_UCalibDirichlet_dir

open MeasureTheory

namespace UCalibDirichlet

/-- **The Dirichlet potential `Λ_F`, display (7).** Frongillo, Luo, Mehta & Schneider (manuscript,
STOC 2027 submission), Lemma 1.3, p.4: "`Λ_F` is the Dirichlet potential defined as
`Λ_F(a) = ‖a‖₁ E_{P∼Dir(a)}[F(P)]`. (7)"

`Lam F a = (∑_j a_j) · ∫ F dDir(a)`.

**Formalization Note.** The paper uses `Λ_F(a)` for count vectors `a ∈ ℝ^K_{>0}`, where
`‖a‖₁ = ∑_j a_j`. For a convex `F : Δ_K → ℝ` (finite) and `a > 0`, `F` is bounded on `Δ_K` and
continuous on the relative interior, which carries `Dir(a)`; so the Bochner integral is the true
expectation (no junk value). -/
noncomputable def Lam {K : ℕ} (F : (Fin K → ℝ) → ℝ) (a : Fin K → ℝ) : ℝ :=
  (∑ j, a j) * ∫ p, F p ∂(dir a)

end UCalibDirichlet


