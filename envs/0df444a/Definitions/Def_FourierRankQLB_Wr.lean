-- Prove2me | Definitions.Def_FourierRankQLB_Wr
-- name    : FourierRankQLB_Wr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:18.375013+00:00
-- url     : https://prove2.me/theorems/db383db0-d466-4d82-bc29-b35fa93187be
-- title:
--   The space $W_r(Y,K)=V_r^{(n)}\mathbin{\widehat\otimes}L^2(Y,\nu;K)$
-- statement:
--   For a measure space $(Y,\nu)$ and a Hilbert space $K$,
--   $$
--   W_r(Y,K)=V_r^{(n)}\mathbin{\widehat\otimes}L^2(Y,\nu;K)\subseteq L^2(O(n)\times Y,\mu_n\otimes\nu;K),
--   $$
--   the closed span of the functions $(Q,y)\mapsto\chi_\Xi(Q)f(y)$ with $\operatorname{rank}\Xi\le r$ and $f\in L^2(Y,\nu;K)$.
--
--   It adds query labels and workspace registers to the amplitude space.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (20), p.17

import Mathlib
import Definitions.Def_FourierRankQLB_chi
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory

namespace FourierRankQLB

/-- The space `W_r(Y, K) = V_r^{(n)} ⊗̂ L²(Y, ν; K)` of Eq. (20), inside `L²(O(n) × Y, μ_n ⊗ ν; K)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (20), p. 17.

**Formalization Note.** As in `VH`, the completed tensor product is the closed span of the pure
tensors `(Q, y) ↦ χ_Ξ(Q) f(y)`, `rank Ξ ≤ r`, `f ∈ L²(Y, ν; K)`. -/
noncomputable def Wr (n r : ℕ) {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :
    Submodule ℂ (Lp K 2 ((haarO n).prod ν)) :=
  (Submodule.span ℂ {f : Lp K 2 ((haarO n).prod ν) |
    ∃ (Ξ : Matrix (Fin n) (Fin n) ℝ) (g : Lp K 2 ν), Ξ.rank ≤ r ∧
      f =ᵐ[(haarO n).prod ν] fun p => chi Ξ p.1 • g p.2}).topologicalClosure

end FourierRankQLB


