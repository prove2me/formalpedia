-- Prove2me | Definitions.Def_MarkdownReadjust_InSetting
-- name    : MarkdownReadjust_InSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:45.8053+00:00
-- url     : https://prove2.me/theorems/b7ecd5df-435e-47fa-b175-50b96f08a964
-- title:
--   The setting of Theorem 4 for one instance
-- statement:
--   A problem instance with inventory $x_0$ and horizon $T$ is **in the setting of Theorem 4** for $N$ and $\alpha$ if $x_0\ge1$ is an integer, $T>0$, $N\ge1$ satisfies the condition of Theorem 4, $\alpha>1/2$, the update times and shifts are (14)–(15), and, as assumed without loss of generality in Appendix B.1,
--
--   $$
--   \rho^d>\eta_0\qquad\text{and}\qquad \lambda T>1 .
--   $$
--
--   The lemmas of Appendix B are stated in this setting.
--
--   **Formalization Note** The k-th problem $(kx_0,kT)$ of the asymptotic setting is such an instance once $k$ is large.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Theorem 4 p.20 and Appendix B.1 p.ec12

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_eta
import Definitions.Def_MarkdownReadjust_NCond

namespace MarkdownReadjust

/-- "The setting of Theorem 4" for one problem instance (Chen–Jasin, SSRN 3740871, Theorem 4,
p.20, and the standing assumptions of Appendix B.1, p.ec12): integer inventory `x₀ ≥ 1`,
horizon `T > 0`, `N ≥ 1` price updates satisfying the condition of Theorem 4, `α > 1/2`, update
times and shifts given by (14)–(15) (built into `tgrid` and `eta`), and "without loss of
generality, we assume that ρd > η0 and λT > 1" (p.ec12).

**Formalization Note.** This is the setting for one instance `(x₀, T) = (x, τ)`; the k-th
problem `(k x₀, k T)` of the asymptotic setting is one such instance whenever it satisfies
these conditions (which hold for all large `k`). -/
def InSetting (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) : Prop :=
  1 ≤ x ∧ 0 < τ ∧ 1 ≤ N ∧ 1 / 2 < α ∧ NCond α N x ∧
    eta M.lam α x τ N 0 < rhoD M x τ ∧ 1 < M.lam * τ

end MarkdownReadjust


