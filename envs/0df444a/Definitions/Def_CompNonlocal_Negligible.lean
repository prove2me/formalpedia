-- Prove2me | Definitions.Def_CompNonlocal_Negligible
-- name    : CompNonlocal_Negligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:45.111198+00:00
-- url     : https://prove2.me/theorems/ce19cb4c-4781-4790-a40e-e1606a5660bf
-- title:
--   Negligible functions
-- statement:
--   A function $\mu:\mathbb N\to\mathbb R$ is **negligible** if for every polynomial $p$ with real coefficients
--   $$\lim_{n\to\infty}|\mu(n)|\,p(n)=0.$$
--
--   Throughout the mission, a bound "$\le \mathsf{negl}(\kappa)$" means: there is a negligible $\mu$ with the bound $\le\mu(\kappa)$ for every $\kappa$.
--
--   **Formalization Note** No sign condition is imposed on $\mu$, as in the paper.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4, p.17

import Mathlib

set_option autoImplicit false

namespace CompNonlocal

/-- Negligible functions. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4, p.17: "A function µ : N → R is called negligible if for
every polynomial p : N → R we have lim_{n→∞} |µ(n)| · p(n) = 0."

**Formalization Note** The polynomials range over `Polynomial ℝ`, evaluated at `n`; no sign
condition is imposed on `µ` (the published `QAdvFew.PoQOracle.Negligible` adds `0 ≤ µ`, which the
paper does not state). Throughout the mission, "≤ negl(κ)" is written
`∃ µ, Negligible µ ∧ ∀ κ, … ≤ µ κ`. -/
def Negligible (μ : ℕ → ℝ) : Prop :=
  ∀ p : Polynomial ℝ,
    Filter.Tendsto (fun n : ℕ => |μ n| * p.eval (n : ℝ)) Filter.atTop (nhds 0)

end CompNonlocal


