-- Prove2me | Definitions.Def_CorrelatedLocalSearch_reflMatrix
-- name    : CorrelatedLocalSearch_reflMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:15.927178+00:00
-- url     : https://prove2.me/theorems/d1194c74-540e-4a70-afc4-43512d7f8131
-- title:
--   The reflected comparison matrix $R^{(m)}$ and $F_T=(R^{(m)})^T\mathbf 1$
-- statement:
--   Let $m\ge2$, $L=m-1$, $a=rk^{-s_*}$ and $b=(k-r)k^{-s_*}$. The **reflected comparison matrix** $R^{(m)}$ acts on vectors $f$ indexed by $\{1,\dots,L\}$, with the convention $f(0)=0$, by
--   $$
--   (R^{(m)}f)(d)=a f(d-1)+b f(d+1)\quad(d<L),\qquad (R^{(m)}f)(L)=a f(L-1)+b f(L).
--   $$
--   For $T\ge0$, $F_T=(R^{(m)})^T\mathbf 1$, read as a function of the potential $d\in\{1,\dots,L\}$ and extended by $F_T(d)=0$ outside that range.
--
--   $F_T(h)$ bounds the cover weight of live paths that stay below the barrier $m$ up to time $T$.
--
--   **Formalization Note** The matrix is indexed by `Fin (m − 1)`, index $i$ standing for the potential $d=i+1$; `reflF k r m T d` is $F_T(d)$.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- The reflected comparison matrix `R^{(m)}` on `{1, …, L}`, `L = m − 1`
(Xu, *Local Search with Correlated Randomness*, arXiv:2607.17469 (sha256 17e00d69…), App. C.1,
proof of Lemma C.1, p.22): `(R f)(d) = a f(d−1) + b f(d+1)` for `d < L` and
`(R f)(L) = a f(L−1) + b f(L)`, with `f(0) = 0`, where `a = r k^{−s∗}` and `b = (k−r) k^{−s∗}`
(p.21).

**Formalization Note** The index `i : Fin (m − 1)` stands for the potential `d = i + 1`. The
convention `f(0) = 0` is built in: row `d = 1` has no entry in column `0`. -/
noncomputable def reflMatrix (k r m : ℕ) : Matrix (Fin (m - 1)) (Fin (m - 1)) ℝ :=
  fun i j =>
    (if (j : ℕ) + 1 = (i : ℕ) then (r : ℝ) * (k : ℝ) ^ (-sStar k r) else 0) +
    (if (j : ℕ) = (i : ℕ) + 1 ∨ ((i : ℕ) + 1 = m - 1 ∧ (j : ℕ) + 1 = m - 1) then
      ((k : ℝ) - r) * (k : ℝ) ^ (-sStar k r) else 0)

/-- The vector `F_T = (R^{(m)})^T 𝟙` of the proof of Lemma C.1 (p.22), read as a function of
the potential `d`: `F_T(d)` for `1 ≤ d ≤ m − 1`, and `0` otherwise (in particular `F_T(0) = 0`). -/
noncomputable def reflF (k r m T d : ℕ) : ℝ :=
  if hd : 1 ≤ d ∧ d ≤ m - 1 then
    ((reflMatrix k r m ^ T).mulVec (fun _ => (1 : ℝ))) ⟨d - 1, by omega⟩
  else 0

end CorrelatedLocalSearch


