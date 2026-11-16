-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Supplement_MeasureSearch
-- name    : LeeCutCertificates_Certificate_Supplement_MeasureSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:04:03.230372+00:00
-- url     : https://prove2.me/theorems/32c737b9-a5b8-4fdf-8e8d-738af2bee694
-- title:
--   Finite additive mass and exact weak-heavy path coverage
-- statement:
--   A nonnegative additive measure on a finite vertex set is represented by nonnegative vertex masses $w_v$. Its subset oracle returns $\mu(S)=\sum_{v\in S}w_v$. For a rooted tree, known total $D>0$ and endpoints $x,y$, exact weak-heavy coverage means
--
--   $$\mu(\operatorname{subtree}(v))\ge D/2\quad\Longleftrightarrow\quad v\in[\mathrm{root},x]\cup[\mathrm{root},y].$$
--
--   The endpoints may coincide or equal the root. This predicate describes exactly the weakly heavy vertices, including equality at half the total; it does not assert the existence of an oracle search.
--
--   **Formalization Note** The measure representation is a finite sum, with no integrals or measurability assumptions. The theorem chooses its program before the unknown vertex-mass function.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §12.5.1 and Lemma 48, printed p.48 (PDF p.49)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_RootedTrees

set_option autoImplicit false
open scoped BigOperators

namespace LeeCutCertificates.Certificate.Supplement

/-- Finite additive mass, accessed only via the subset oracle in the search theorem. -/
def subsetMass {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ v ∈ S, w v

def WeakHeavyCover {n : ℕ} (T : RootedTree n) (w : Fin n → ℝ) (D : ℝ)
    (ends : Fin n × Fin n) : Prop :=
  ∀ v, D / 2 ≤ subsetMass w (T.subtree v) ↔
    T.Ancestor v ends.1 ∨ T.Ancestor v ends.2

end LeeCutCertificates.Certificate.Supplement


