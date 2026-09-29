-- Prove2me | Definitions.Def_eulerMascheroni_padeDecay
-- name    : eulerMascheroni_padeDecay
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T14:54:43.571845+00:00
-- url     : https://prove2.me/theorems/efd5abe2-bfb5-40a3-a91e-7ebafb34b9a9
-- title:
--   Common denominators with the decay rate required by the norm–Padé argument
-- statement:
--   For real $a$, say that Padé-compatible decaying denominators exist if positive integers $D_n$ make every $D_nq_k(a)$ integral over $\mathbb Z$ for $k\le2n$, and
--
--   $$\frac{4^nD_n}{n!}\longrightarrow0.$$
--
--   Here $q_k(a)=(a-\sum_{j<k}(-1)^j j!)/k!$. This growth requirement is weaker than an exponential bound on common denominators and is the estimate sufficient for simultaneous decay of the normalized Padé coefficients.
-- source:
--   Explicit series and norm–Padé growth definitions for this decomposition. Compare Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, §4.1 and §4.3, and Matala-aho–Zudilin, https://arxiv.org/html/1703.02633, Eqs. (10)–(11).

import Definitions.Def_eulerMascheroni_padeTransform

namespace EulerMascheroni.Arithmetic

def PadeDecayDenominators (a : ℝ) : Prop :=
  ∃ D : ℕ → ℕ, (∀ n, 0 < D n) ∧
    Filter.Tendsto (fun n => (D n:ℝ)*4^n/(n.factorial:ℝ)) Filter.atTop (nhds 0) ∧
    ∀ n k : ℕ, k ≤ 2*n → IsIntegral ℤ ((D n:ℝ)*quotientCoeff a k)

end EulerMascheroni.Arithmetic


