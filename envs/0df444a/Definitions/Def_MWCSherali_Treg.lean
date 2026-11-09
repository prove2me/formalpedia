-- Prove2me | Definitions.Def_MWCSherali_Treg
-- name    : MWCSherali_Treg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:10.861273+00:00
-- url     : https://prove2.me/theorems/c753048e-5792-45bd-8cc1-4ad30b8e01c1
-- title:
--   The tubes $T_{ab}$
-- statement:
--   For terminals $a\neq b$ with $\{i,j\}=[4]\setminus\{a,b\}$, the **tube**
--
--   $$T_{ab}=\{t\in\Delta_4\mid \max_\ell t_\ell\le\alpha\ \text{and}\ t_i+t_j\le\beta\},$$
--
--   a neighbourhood of the simplex edge between $e_a$ and $e_b$, cut off by the corners. $T_{ab}=T_{ba}$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.31

import Mathlib

namespace MWCSherali

/-- **The tube `T_{ab}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.31: "For every pair of terminals `a, b`, the
tubes `T_{ab} = {t ∈ Δ₄ | max_{ℓ ∈ [4]} t_ℓ ≤ α and t_i + t_j ≤ β, {i, j} = [4] ∖ {a, b}}`."

**Formalization Note.** `t_i + t_j` for `{i, j} = [4] ∖ {a, b}` is the sum of `t` over the
complement of `{a, b}`; so `Treg α β a b = Treg α β b a`. Only `a ≠ b` is used. -/
def Treg (α β : ℝ) (a b : Fin 4) : Set (Fin 4 → ℝ) :=
  {t | t ∈ stdSimplex ℝ (Fin 4) ∧ (∀ l, t l ≤ α) ∧ ∑ l ∈ ({a, b} : Finset (Fin 4))ᶜ, t l ≤ β}

end MWCSherali


