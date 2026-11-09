-- Prove2me | Definitions.Def_TriFormQ_zeroLocus
-- name    : TriFormQ_zeroLocus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:31.250453+00:00
-- url     : https://prove2.me/theorems/61797aec-4c34-41b6-a975-4ea9e75d513e
-- title:
--   Zero locus $Z_f$ of a trilinear form
-- statement:
--   For a trilinear form $f$ on $\mathbb F_q^n\times\mathbb F_q^n\times\mathbb F_q^n$, its zero locus with respect to the third argument is
--
--   $$Z_f=\{(u,v)\in\mathbb F_q^n\times\mathbb F_q^n:\ f(u,v,z)=0\ \text{for all } z\in\mathbb F_q^n\},$$
--
--   the zero set of the bilinear map $(u,v)\mapsto f(u,v,\cdot)$. Its size determines the analytic rank of $f$ and the distribution $p_Z$ on base points.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16)

import Definitions.Def_TriFormQ_TriForm_eval

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16):
"Z_f := {(u, v) ∈ U × V : f(u, v, z) = 0 for all z ∈ W}", the zero locus of the bilinear map
`(u, v) ↦ f(u, v, ·)`. -/
def zeroLocus {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n) :
    Finset (Vec F n × Vec F n) :=
  Finset.univ.filter fun p => ∀ z : Vec F n, TriForm.eval θ p.1 p.2 z = 0

end TriFormQ


