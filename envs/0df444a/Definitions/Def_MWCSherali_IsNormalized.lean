-- Prove2me | Definitions.Def_MWCSherali_IsNormalized
-- name    : MWCSherali_IsNormalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:27.821081+00:00
-- url     : https://prove2.me/theorems/3e0d8066-f681-44b3-a50e-e4748e6536c4
-- title:
--   Normalized weight functions
-- statement:
--   A weight function $w:E_{k,n}\to\mathbb R$ is **normalized** if
--
--   $$\sum_{e\in E_{k,n}}w_e=n.\tag{1}$$
--
--   For a normalized $w$ the CKR relaxation has value at most $1$ (embed every vertex at itself), so the minimum non-opposite cut is a lower bound on the integrality ratio.
--
--   **Formalization Note** Weights are functions on all unordered pairs of points; only their values on $E_{k,n}$ are used. Nonnegativity is a separate hypothesis where the paper has $w:E_{k,n}\to\mathbb R_{\ge0}$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (1), p.4; §2.1, p.14

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_edges

namespace MWCSherali

/-- **Normalized weight functions.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version
of Nov. 3, 2026), (1), p.4, and §2.1, p.14: "We say that our weight function `w` is normalized
if `∑_{e ∈ E_{k,n}} w_e = n`."

**Formalization Note.** Weights are functions `w : Sym2 (Grid k n) → ℝ`; only their values on
`E_{k,n}` are ever used. Nonnegativity on `E_{k,n}` is a separate hypothesis wherever the paper
has `w : E_{k,n} → ℝ_{≥0}`. -/
def IsNormalized {k n : ℕ} (w : Sym2 (Grid k n) → ℝ) : Prop :=
  ∑ e ∈ edges k n, w e = n

end MWCSherali


