-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_wTree
-- name    : AgnosticTNS_Supplement_wTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:39:39.678575+00:00
-- url     : https://prove2.me/theorems/928532b6-fcfb-4877-aa8a-b4d8664cb278
-- title:
--   TTN edge weights $w_{\hat T}(f)=\prod_{e\in\mathrm{cut}_G(A_f)}w(e)$
-- statement:
--   For a tree-indexed partition $(\hat T,\hat{\mathcal X})$ of $[n]$ and an edge $f$ of $\hat T$, let $A_f\subseteq[n]$ be the union of the bags on one side of $\hat T-f$. The edge weight is
--   $$
--   w_{\hat T}(f) = \prod_{e\in\mathrm{cut}_G(A_f)} w(e),
--   $$
--   with the empty product equal to $1$; it does not depend on the side, since both sides have the same cut.
--
--   **Formalization Note** The side is that of the second endpoint of a fixed representative pair of $f$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.14, Eq. (6.30), p.56

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_treeSide
import Definitions.Def_AgnosticTNS_cut

namespace AgnosticTNS.Supplement

/-- **The TTN edge weights** `w_T̂(f) = ∏_{e ∈ cut_G(A_f)} w(e)`, Eq. (6.30), Theorem 6.14, p.56
(Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)), with `A_f ⊆ [n]` the union of the bags on one side of `T̂ − f`;
the empty product is `1`.

**Formalization Note** The side is the one of the second endpoint of a fixed representative pair of
`f` (`Quot.out`); since `cut_G(A) = cut_G(V ∖ A)` the value does not depend on the side. -/
noncomputable def wTree {n m : ℕ} (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ)
    (That : SimpleGraph (Fin m)) (Xhat : Fin m → Finset (Fin n)) : That.edgeSet → ℕ := fun f =>
  ∏ e ∈ cut G ((treeSide That f.1.out.1 f.1.out.2).biUnion Xhat), w e

end AgnosticTNS.Supplement


