-- Prove2me | Definitions.Def_TriFormQ_fiber
-- name    : TriFormQ_fiber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:29.410475+00:00
-- url     : https://prove2.me/theorems/f64ddbc9-dd2e-40d9-8987-851184e167d0
-- title:
--   Fiber $Z_v$ of the zero locus
-- statement:
--   For a trilinear form $f$ and a base point $v\in\mathbb F_q^n$, the **fiber** of the zero locus over $v$ is
--
--   $$Z_v=\{u\in\mathbb F_q^n:\ (u,v)\in Z_f\}=\{u:\ f(u,v,w)=0\ \text{for all } w\}.$$
--
--   It is a linear subspace (see `fiberSub`), and $Z_f$ is the disjoint union of $Z_v\times\{v\}$ over $v$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16)

import Definitions.Def_TriFormQ_TriForm_eval

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16): "the
fiber of π over a fixed v ∈ V is Z_v = {u ∈ U : (u, v) ∈ Z}", i.e. the `u` with
`f(u, v, ·) ≡ 0`. -/
def fiber {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n)
    (v : Vec F n) : Finset (Vec F n) :=
  Finset.univ.filter fun u => ∀ w : Vec F n, TriForm.eval θ u v w = 0

end TriFormQ


