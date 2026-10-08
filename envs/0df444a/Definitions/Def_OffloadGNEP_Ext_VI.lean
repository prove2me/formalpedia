-- Prove2me | Definitions.Def_OffloadGNEP_Ext_VI
-- name    : OffloadGNEP_Ext_VI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:01.038632+00:00
-- url     : https://prove2.me/theorems/ce12e21e-ea01-4c69-bd5c-bc0ddbd4caaf
-- title:
--   Variational-inequality solutions and monotonicity
-- statement:
--   For a set $S$ of user profiles and a vector field $G$, a point $\bar x$ solves $\operatorname{VI}(S,G)$ when it belongs to $S$ and
--
--   $$\langle G(\bar x),x-\bar x\rangle\ge0\qquad\text{for every }x\in S.$$
--
--   The field is monotone on $S$ when $\langle G(y)-G(x),y-x\rangle\ge0$ for every $x,y\in S$. The same two notions are also defined for a profile paired with one real price variable.
--
--   These general predicates express both the original game's VI and the extended game's VI without building either game into the definition.
--
--   **Formalization Note** All pairings are explicit finite sums, including the additional scalar product for the price coordinate.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), pp. 11–12, footnotes 2–3; p. 15, VI(F_e,K_e)

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_Types

namespace OffloadGNEP.Ext

/-- A solution of the finite-dimensional variational inequality, footnote 2. -/
def IsVISol {N : ℕ} (S : Set (Fin N → OffloadGNEP.Exist.Tier → ℝ))
    (G : (Fin N → OffloadGNEP.Exist.Tier → ℝ) → (Fin N → OffloadGNEP.Exist.Tier → ℝ))
    (xb : Fin N → OffloadGNEP.Exist.Tier → ℝ) : Prop :=
  xb ∈ S ∧ ∀ x ∈ S, 0 ≤ OffloadGNEP.Exist.pair (G xb) (x - xb)

/-- Monotonicity on a specified set, as in footnote 3. -/
def IsMonotoneOn {N : ℕ} (S : Set (Fin N → OffloadGNEP.Exist.Tier → ℝ))
    (G : (Fin N → OffloadGNEP.Exist.Tier → ℝ) → (Fin N → OffloadGNEP.Exist.Tier → ℝ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, 0 ≤ OffloadGNEP.Exist.pair (G y - G x) (y - x)

/-- Euclidean pairing of a profile and one real price. -/
def pairE {N : ℕ}
    (a b : (Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ) : ℝ :=
  OffloadGNEP.Exist.pair a.1 b.1 + a.2 * b.2

/-- VI solution for the extended profile-price space. -/
def IsVISolE {N : ℕ} (S : Set ((Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ))
    (G : ((Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ) → ((Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ))
    (pb : (Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ) : Prop :=
  pb ∈ S ∧ ∀ p ∈ S, 0 ≤ pairE (G pb) (p - pb)

/-- Monotonicity on a set of profile-price pairs. -/
def IsMonotoneOnE {N : ℕ} (S : Set ((Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ))
    (G : ((Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ) → ((Fin N → OffloadGNEP.Exist.Tier → ℝ) × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, 0 ≤ pairE (G q - G p) (q - p)

end OffloadGNEP.Ext


