-- Prove2me | Definitions.Def_LeblSCV_Shared_polydisc
-- name    : LeblSCV_Shared_polydisc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:59:03.093443+00:00
-- url     : https://prove2.me/theorems/9d7e19bf-5ed7-409f-8c37-e09149748b62
-- title:
--   Definition 1.1.1 — polydisc $\Delta_\rho(a)$
-- statement:
--   For a center $a = (a_1, \dots, a_n) \in \mathbb{C}^n$ and a polyradius $\rho = (\rho_1, \dots, \rho_n)$ with every $\rho_k > 0$, the **polydisc** with center $a$ and polyradius $\rho$ is the product of open discs
--   $$\Delta_\rho(a) = \{ z \in \mathbb{C}^n : |z_k - a_k| < \rho_k \text{ for } k = 1, 2, \dots, n \}.$$
--   When $\rho > 0$ is a single number, $\Delta_\rho(a)$ denotes the polydisc with all radii equal to $\rho$; the unit polydisc is $\mathbb{D}^n = \Delta_1(0)$.
--
--   Polydiscs are the natural domains of convergence for power series in several variables and the domains on which the Cauchy integral formula takes its simplest form. This one definition serves chunk I (Theorem 1.1.4 and Proposition 1.2.2 on pp. 16 and 22, Theorem 1.2.1 on p. 20), chunk VII (Lemma 4.4.7, the Dolbeault–Grothendieck lemma, p. 143) and chunk IX (the factor $V'$ of the polydisc $V' \times D$ in the Weierstrass preparation theorem, Theorem 6.2.3, p. 170).
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ` and the polyradius is `ρ : Fin n → ℝ`. The positivity $\rho_k > 0$ is not built into the definition; every theorem using the polydisc carries it as an explicit hypothesis. The closed polydisc $\overline{\Delta}$ is written as the topological closure of this set. For $n = 0$ the polydisc is the single point of $\mathbb{C}^0$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 13, Definition 1.1.1

import Mathlib

namespace LeblSCV.Shared

/-- Definition 1.1.1 (Lebl, p. 13). The polydisc `Δ_ρ(a) = {z ∈ ℂⁿ : |z_k - a_k| < ρ_k, k = 1, …, n}`
with center `a` and polyradius `ρ = (ρ_1, …, ρ_n)`. The book requires every `ρ_k > 0`; theorems
using the polydisc carry that as an explicit hypothesis. -/
def polydisc {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ k : Fin n, ‖z k - a k‖ < ρ k}

end LeblSCV.Shared


