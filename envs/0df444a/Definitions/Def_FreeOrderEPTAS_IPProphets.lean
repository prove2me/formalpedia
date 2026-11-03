-- Prove2me | Definitions.Def_FreeOrderEPTAS_IPProphets
-- name    : FreeOrderEPTAS_IPProphets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:15.615287+00:00
-- url     : https://prove2.me/theorems/b2154c6d-d926-409b-8829-e29e508f67de
-- title:
--   The integer program (IPProphets)
-- statement:
--   For guesses $b_i=\mathrm{BaseGuess}(B_i)$ and $\Delta_i=\mathrm{DeltaGuess}(B_i)$ on $m$ machines, (IPProphets) asks for a binary matrix $\xi$ with
--   $$\sum_i\xi_{ij}\le1\ \ \forall j,\qquad\sum_j\xi_{ij}\le1\ \text{ on jump machines},\qquad\sum_j\mathbb E[[X_j-b_i]^+]\,\xi_{ij}\ge\Delta_i\ \ \forall i.$$
--   `excess` is the marginal load $\mathbb E[[X_j-b]^+]=\mathbb E[\max\{X_j,b\}]-b$, `ProphetCard` the two cardinality families, and `IPProphetsFeasible` the feasibility of the program.
--
--   **Formalization Note** Machines are 0-based, so the paper's even $i$ (jump) is an odd index here.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.4, p.19

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Instance
import Definitions.Def_FreeOrderEPTAS_SCInstance

open MeasureTheory

namespace FreeOrderEPTAS

variable {m n : ℕ}

/-- The marginal load `E[[X_j - b]^+]` (arXiv:2007.13121v3, §3.4, p.19). It equals
`E[max{X_j, b}] - b`; the integrand is integrable since `X_j` has a finite mean. -/
noncomputable def excess (I : Instance n) (j : Fin n) (b : ℝ) : ℝ :=
  ∫ x, max (x - b) 0 ∂(I.μ j)

/-- Constraints (2), (3) of (IPProphets) (p.19): each variable is on at most one machine, and each
jump machine has at most one variable. Machines are 0-based, so the paper's even `i` (jump) is an
odd index here. Constraint (1) is the type `Assignment`. -/
def ProphetCard (x : Assignment m n) : Prop :=
  (∀ j, (Finset.univ.filter fun i => x i j = true).card ≤ 1) ∧
    ∀ i : Fin m, i.val % 2 = 1 → (Finset.univ.filter fun j => x i j = true).card ≤ 1

/-- (IPProphets) (p.19), for guesses `b` of BaseGuess and `Δ` of DeltaGuess: constraints (1)–(3) and
(4): `∑_j E[[X_j - b_i]^+] ξ_ij ≥ Δ_i` for each machine. -/
def IPProphetsFeasible (I : Instance n) (b Δ : Fin m → ℝ) : Prop :=
  ∃ ξ : Assignment m n, ProphetCard ξ ∧
    ∀ i, Δ i ≤ ∑ j, excess I j (b i) * bit (ξ i j)

end FreeOrderEPTAS


