-- Prove2me | Definitions.Def_LPAllocRM_revenue
-- name    : LPAllocRM_revenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:07:25.409156+00:00
-- url     : https://prove2.me/theorems/4ab4820a-c06d-4968-a084-42b0525619e7
-- title:
--   Revenue $R^\pi\equiv f\cdot N^\pi$
-- statement:
--   The revenue collected under policy $\pi$ on an arrival path is
--
--   $$R^\pi\equiv f\cdot N^\pi=\sum_{j=1}^n f_jN^\pi_j,$$
--
--   where $f_j$ is the fare of class $j$. For the LP policy the paper writes $R^{LP}\equiv f\cdot N^{LP}$.
--
--   **Formalization Note** The fares carry no sign restriction; the paper states none.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, §2, p.722 and §3, p.723

import Mathlib
import Definitions.Def_LPAllocRM_accepted

namespace LPAllocRM

/-- The revenue `R^π ≡ f · N^π = ∑_j f_j N^π_j` collected under policy `π` on the arrival path `d`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
§2, p.722 (PDF p.3): "We will also use the notation R^π ≡ f · N^π for the (random) amount of revenue
when π is in use"; for `π^LP`, "R^LP ≡ f · N^LP", p.723 (PDF p.4).

**Formalization Note** The fares `f` carry no sign restriction (the paper states none). -/
noncomputable def revenue {n : ℕ} (f : Fin n → ℝ) (τ : ℝ) (π : Policy n) (d : ℝ → Fin n → ℕ) : ℝ :=
  ∑ j, f j * (accepted τ π d j : ℝ)

end LPAllocRM


