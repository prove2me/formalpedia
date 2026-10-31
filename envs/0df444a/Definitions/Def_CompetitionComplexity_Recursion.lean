-- Prove2me | Definitions.Def_CompetitionComplexity_Recursion
-- name    : CompetitionComplexity_Recursion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:46.554595+00:00
-- url     : https://prove2.me/theorems/c1b69ccf-dd2a-44d6-a2c5-7238e6015f09
-- title:
--   The recursion (9) for $\rho_{\varepsilon,j}$ and its well-definedness
-- statement:
--   Fix $\varepsilon>0$ and an integer $n\ge2$. The sequence $(\rho_{\varepsilon,j})_{j\ge1}$ is defined by
--   $$
--   \rho_{\varepsilon,1}=1,\qquad (n-1)\rho_{\varepsilon,j-1}^{\,n}-\varepsilon=n\,\rho_{\varepsilon,j}^{\,n-1}\quad(j\ge2), \tag{9}
--   $$
--   where $\rho_{\varepsilon,j}$ is the positive root
--   $$
--   \rho_{\varepsilon,j}=\Bigl(\frac{(n-1)\rho_{\varepsilon,j-1}^{\,n}-\varepsilon}{n}\Bigr)^{1/(n-1)} .
--   $$
--   The paper says $\rho_{\varepsilon,j}$ is **well defined** if $(n-1)\rho_{\varepsilon,j-1}^{\,n}-\varepsilon>0$. Since the sequence is built recursively, this presupposes that $\rho_{\varepsilon,j-1}$ is well defined; so "$\rho_{\varepsilon,j}$ is well defined" means $j\ge1$ and $(n-1)\rho_{\varepsilon,i-1}^{\,n}-\varepsilon>0$ for every $2\le i\le j$.
--
--   By Lemma 4, the value of the program (1)–(4) is $\varepsilon-(n-1)\rho_{\varepsilon,m}^{\,n}$ whenever $\rho_{\varepsilon,m}$ is well defined, so the competition complexity is read off from the last index at which the recursion stays positive.
--
--   **Formalization Note** The value at $j=0$ is a convention ($1$) and never used. Lean's real power of a negative base is a junk value; it can only occur when $\rho_{\varepsilon,j}$ is not well defined, and every statement about $\rho_{\varepsilon,j}$ assumes or concludes well-definedness.
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, §5, display (9) and the definition of well-defined, p.15; the positive root, proof of Proposition 2, p.16

import Mathlib

namespace CompetitionComplexity

/-- **The recursion (9)**: `ρ_{ε,1} = 1` and `(n − 1)ρⁿ_{ε,j−1} − ε = nρ^{n−1}_{ε,j}` for `j ≥ 2`.
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), §5, display (9), p.15.

`rho ε n j` is the paper's `ρ_{ε,j}` (1-based in `j`): `ρ_{ε,j}` is the positive
`(n − 1)`-th root `(((n − 1)ρⁿ_{ε,j−1} − ε)/n)^{1/(n−1)}` (the proof of Proposition 2, p.16,
takes this root and notes it is positive).

**Formalization Note.** The value at `j = 0` is a convention (`1`) and is never used. The real
power `Real.rpow` of a negative base is a junk value; it occurs exactly when `ρ_{ε,j}` is not
well defined in the paper's sense, and every statement about `ρ_{ε,j}` assumes or concludes
`WellDef ε n j`. The recursion is used for integers `n ≥ 2`. -/
noncomputable def rho (ε : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (j + 2) => ((((n : ℝ) - 1) * rho ε n (j + 1) ^ n - ε) / n) ^ (1 / ((n : ℝ) - 1))

/-- **"ρ_{ε,j} is well defined"**, §5, p.15: "For fixed ε and n we say that ρε,j is well defined
if (n − 1)ρⁿ_{ε,j−1} − ε > 0."

**Formalization Note.** The sequence is defined recursively, so `ρ_{ε,j}` being well defined
presupposes that `ρ_{ε,j−1}` is: the predicate is the chain `j ≥ 1` and
`(n − 1)ρⁿ_{ε,i−1} − ε > 0` for every `2 ≤ i ≤ j` (`ρ_{ε,1} = 1` is always well defined). -/
def WellDef (ε : ℝ) (n j : ℕ) : Prop :=
  1 ≤ j ∧ ∀ i : ℕ, 2 ≤ i → i ≤ j → 0 < ((n : ℝ) - 1) * rho ε n (i - 1) ^ n - ε

end CompetitionComplexity


