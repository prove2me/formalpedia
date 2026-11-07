-- Prove2me | Definitions.Def_KServerConj_Psi
-- name    : KServerConj_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:49.249237+00:00
-- url     : https://prove2.me/theorems/18a1960d-e5f7-445a-8023-31790725eb91
-- title:
--   The quadratic matrix $Q=[z^{-d(x,y)}q_xq_y]_{x\le y}$ and the potential $\Psi=\mu(Q)$, equation (17)
-- statement:
--   Let $M$ be finite and let columns $q_x\in K^k$ be given for every $x\in M$. The quadratic matrix $Q$ has rows indexed by the $N=\binom{k+1}2$ monomials $e_ie_j$ and one column for each unordered pair $\{x,y\}$ of points, $x=y$ allowed:
--
--   $$Q=\big[\,z^{-d(x,y)}\,q_xq_y\,\big]_{x\le y},\qquad \Psi=\mu(Q).$$
--
--   The **potential** $\Psi$ is the least valuation of an $N\times N$ minor of $Q$. The paper shows that it pays the extended cost of every request and is bounded in terms of $(k+1)w-\mathrm{cl}$.
--
--   **Formalization Note** Columns are indexed by unordered pairs (`Sym2 M`) instead of the pairs $x\le y$ of a fixed total order; this changes no minor valuation.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §4, equation (17), p.9 (pdf p.10)

import Mathlib
import Definitions.Def_KServerConj_K
import Definitions.Def_KServerConj_symProd
import Definitions.Def_KServerConj_minorVal

namespace KServerConj

/-- **The quadratic matrix `Q`**, equation (17) of Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §4, printed p.9
(PDF p.10): "Fix any total order on the finite point set M. At each time define the
N × (n+1 choose 2) matrix Q, where N = (k+1 choose 2), and the potential Ψ by
Q = [ z^{−d(x,y)} q_x q_y ]_{x≤y}, Ψ = µ(Q)."

Rows are the monomials `e_ie_j` (`Sym2 (Fin k)`), columns the unordered pairs `{x, y}` of points,
diagonal included (`Sym2 M`); column `s(x, y)` is `z^{−d(x,y)}` times the product `q_x q_y`.

**Formalization Note.** The total order on `M` only enumerates the pairs `x ≤ y`; indexing the
columns by `Sym2 M` is order-free and changes no minor valuation. -/
noncomputable def Qmat {k : ℕ} {M : Type*} [PseudoMetricSpace M] (q : M → Fin k → K k M) :
    Matrix (Sym2 (Fin k)) (Sym2 M) (K k M) :=
  fun p c => Sym2.lift ⟨fun x y => zp (-dist x y) * symProd (q x) (q y) p, by
    intro x y
    dsimp only
    rw [dist_comm, symProd_comm]⟩ c

/-- **The potential** `Ψ = µ(Q)`, equation (17) (§4, printed p.9, PDF p.10). -/
noncomputable def Psi {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → K k M) : WithTop ℝ :=
  minorVal (Qmat q)

end KServerConj


