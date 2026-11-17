-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_rmCount
-- name    : TwoFoldOPI_Supplement_rmCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:54:18.468057+00:00
-- url     : https://prove2.me/theorems/5274ba15-25ce-41f9-a3f9-37fabde7b636
-- title:
--   The reduced-monomial count $\mathrm{Count}_q(v,r)$
-- statement:
--   For integers $q\ge2$, $v\ge0$ and $r\ge0$,
--   $$\mathrm{Count}_q(v,r)=\#\{\alpha\in\{0,\dots,q-1\}^v:\ \alpha_1+\dots+\alpha_v\le r\}.$$
--   It is the dimension of the Reed–Muller code $\mathrm{RM}_{\mathbb F_q,v,r}$ and the number $n$ of rows of the matrix $B$ in $\mathrm{RMSyndrome}_{q,\rho,c}(v)$.
--
--   **Formalization Note** The threshold is a natural number; the paper's real threshold enters only as $\lfloor\rho v\rfloor$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.10, p. 22

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **The reduced-monomial count `Count_q(v, r)`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.10, p.22: "For integers q ≥ 2, v ≥ 1, and a real threshold r ≥ 0,
define Count_q(v, r) := #{α ∈ {0, …, q − 1}^v : ‖α‖_1 ≤ r}. Thus Count_q(v, r) = Count_q(v, ⌊r⌋)."

`rmCount q v r` is the number of exponent vectors `α ∈ {0, …, q−1}^v` with `α_1 + ⋯ + α_v ≤ r`.

**Formalization Note.** The threshold is a natural number; the paper's real threshold enters only
through `Count_q(v, ⌊ρv⌋)` (Definition 6.1), which statements write with `⌊ρv⌋₊`. -/
def rmCount (q v r : ℕ) : ℕ :=
  (Finset.univ.filter fun α : Fin v → Fin q => ∑ i, (α i : ℕ) ≤ r).card

end Supplement

end TwoFoldOPI


