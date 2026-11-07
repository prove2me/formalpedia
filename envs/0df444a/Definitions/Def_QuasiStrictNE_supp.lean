-- Prove2me | Definitions.Def_QuasiStrictNE_supp
-- name    : QuasiStrictNE_supp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:05:58.873194+00:00
-- url     : https://prove2.me/theorems/e806d224-7dcf-451a-a76f-574c977645ed
-- title:
--   Support $\mathrm{supp}(z)$ of a vector
-- statement:
--   For $z\in\mathbb R^k$, the **support** of $z$ is
--   $$
--   \mathrm{supp}(z)=\{i\in[k] : z_i>0\}.
--   $$
--   For a mixed strategy it is the set of pure strategies played with positive probability.
--
--   **Formalization Note** $[k]$ is `Fin k` $=\{0,\dots,k-1\}$ (0-based); the support is a `Finset`.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §2, p.4

import Mathlib

namespace QuasiStrictNE

/-- **Support of a vector** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, §2, p.4: "we define supp(z) = {i ∈ [k] : zi > 0}").

`supp z` is the set of indices `i` with `0 < z i`.

**Formalization Note** The index set `[k] = {1, …, k}` is `Fin k = {0, …, k − 1}` (0-based), and
`supp z` is a `Finset`. -/
noncomputable def supp {k : ℕ} (z : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => 0 < z i)

end QuasiStrictNE


