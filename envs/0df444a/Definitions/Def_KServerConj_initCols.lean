-- Prove2me | Definitions.Def_KServerConj_initCols
-- name    : KServerConj_initCols
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:21.360506+00:00
-- url     : https://prove2.me/theorems/49776561-cea3-43fa-9b4a-86109e7b0b86
-- title:
--   Initial columns $(q_x)_i=\gamma_{i,x}z^{d(s_i,x)}$, equation (7)
-- statement:
--   Let the initial configuration be $C_0=\{s_1,\dots,s_k\}$. For every point $x\in M$ the initial column $q_x\in K^k$ is
--
--   $$(q_x)_i=\gamma_{i,x}\,z^{d(s_i,x)},\qquad i\in[k].$$
--
--   Expanding $\det(q_{x_1},\dots,q_{x_k})$ over permutations produces one term per matching from $C_0$ to $X$, with exponent its cost and a distinct coefficient monomial, so the least-cost terms cannot cancel and $\nu(\det)=D(C_0,X)=w_0(X)$ (equation (9)).
--
--   **Formalization Note** The initial configuration is a tuple $s$ (server $i$ starts at $s_i$), since the variables $\gamma_{i,x}$ are indexed by the initial server; statements assume $s$ injective.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §2.2, equation (7), p.6 (pdf p.7)

import Mathlib
import Definitions.Def_KServerConj_K

namespace KServerConj

/-- **The initial columns**, equation (7) of Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §2.2, printed p.6
(PDF p.7): "For every x ∈ M define a column q_x ∈ K^k by (q_x)_i = γ_{i,x} z^{d(s_i,x)}, i ∈ [k]."

**Formalization Note.** The initial configuration `C₀ = {s₁, …, s_k}` is given as a tuple
`s : Fin k → M` (server `i` starts at `s i`), because the variables `γ_{i,x}` are indexed by the
initial server; statements assume `s` injective and use `C₀ = image s`. -/
noncomputable def initCols {k : ℕ} {M : Type*} [PseudoMetricSpace M] (s : Fin k → M) :
    M → Fin k → K k M :=
  fun x i => coef (Sum.inl (i, x)) * zp (dist (s i) x)

end KServerConj


