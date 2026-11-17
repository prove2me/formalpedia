-- Prove2me | Definitions.Def_PhaseEncodedQGE_Supplement_Readouts
-- name    : PhaseEncodedQGE_Supplement_Readouts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:29:48.686206+00:00
-- url     : https://prove2.me/theorems/a69b1914-82f2-471b-bf07-9c81f5fd94b0
-- title:
--   First-order $m$-defect blocks and Taylor coefficients of a defect layer
-- statement:
--   Fix a preparation, a mixer axis, a number of repetitions, a graph $G$ on $n$ vertices and the angle $\gamma$, and write $p_G(x;\beta)$ for the Born probability of the outcome $x$ and $D(x)$ for its defect set.
--
--   1. The **first-order $m$-defect block** is the multiset $\{\{p_1(x)/p_0(x) : |D(x)|=m\}\}$ of first-order values over the outcomes with $m$ defects, where $p_0=p_G(\cdot;0)$ and $p_1=\partial_\beta p_G(\cdot;\beta)|_{\beta=0}$.
--   2. The **Taylor coefficient** of order $j$ of a function $f$ of $\beta$ at $0$ is $[\beta^j]f=f^{(j)}(0)/j!$.
--   3. The **Taylor coefficients of the $m$-defect layer through order $J$** form the multiset, over the outcomes with $m$ defects, of the vectors $\big([\beta^j]\,p_G(x;\beta)\big)_{0\le j\le J}$.
--
--   These are the quantities compared in the Weisfeiler–Leman placement (Theorem 5.3 and Corollary A.26).
--
--   **Formalization Note** Multiplicities count, and the multisets do not depend on how outcomes are enumerated. The coefficient vectors are unnormalized; the paper divides by the layer weight $\mu_m$, which is common to the layer and nonzero under its hypotheses, so the two forms are equivalent.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §5, pp.10–11 (PDF pp.11–12), Theorem 5.3; App. A.1.7, pp.24–25 (PDF pp.25–26), Corollary A.26

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

open Classical in
/-- The first-order `m`-defect block: the multiset `{{p₁(x)/p₀(x) : |D(x)| = m}}` of first-order
values over the outcomes with `m` defects (Miller, Lee, *Structural Accessibility in Phase-Encoded
Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), Theorem 5.3, p.10; Corollary
A.26(i), p.24).

**Formalization Note** The first-order value is the base `firstOrder` (`λ(x) = p₁(x)/p₀(x)`).
Multiplicities count, and the multiset does not depend on how outcomes are enumerated. -/
noncomputable def firstOrderBlock {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (m : ℕ) : Multiset ℝ :=
  ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
    (firstOrder prep P r G γ)

/-- The Taylor coefficient `[β^j] f = f^{(j)}(0)/j!` of a function of the mixer angle at `β = 0`
(§5, p.10, eq. (15); Corollary A.26(ii), p.24). The Born probability is a trigonometric
polynomial in `β`, so the iterated derivative is the genuine one. -/
noncomputable def taylorCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  iteratedDeriv j f 0 / (j.factorial : ℝ)

open Classical in
/-- The Taylor coefficients of the `m`-defect layer through order `J`: the multiset, over the
outcomes `x` with `m` defects, of the coefficient vectors `([β^j] p_G(x; β))_{0 ≤ j ≤ J}`
(Theorem 5.3(2)–(3), p.11; Corollary A.26(ii)–(iii), pp.24–25).

**Formalization Note** The vector is indexed by `j : Fin (J + 1)`, so the coefficients of one
outcome are kept together ("jointly"). The paper's form (ii) divides by the layer weight
`µ_m = c^{2m} s^{2(n−m)}`, which is common to the whole layer and nonzero under its hypotheses, so
equality of these multisets is equivalent to equality of the normalized ones. -/
noncomputable def taylorLayer {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (m J : ℕ) : Multiset (Fin (J + 1) → ℝ) :=
  ((Finset.univ : Finset (Outcome n)).filter (fun x => (defects x).card = m)).val.map
    (fun x => fun j => taylorCoeff (fun β => born prep P r G γ β x) j)

end PhaseEncodedQGE.Supplement


