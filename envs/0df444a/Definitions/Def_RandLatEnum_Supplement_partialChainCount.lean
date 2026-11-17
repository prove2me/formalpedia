-- Prove2me | Definitions.Def_RandLatEnum_Supplement_partialChainCount
-- name    : RandLatEnum_Supplement_partialChainCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:00:41.502728+00:00
-- url     : https://prove2.me/theorems/29adea97-9ad5-4af8-b644-9a734f1dcfd3
-- title:
--   Number $C_{J,n}(L)$ of partial chains indexed by $J$
-- statement:
--   Fix $r$, rank fractions $x_0,\dots,x_r$, exponents $h_0,\dots,h_r$ and a nonempty $J\subseteq\{1,\dots,r-1\}$. For a lattice $L\subset\mathbb R^n$, $C_{J,n}(L)$ is the number of strictly nested families $(M_j)_{j\in J}$ of primitive sublattices of $L$ with
--   $$\operatorname{rank}M_j=\lfloor x_jn\rfloor,\qquad \det M_j\le n^{h_jn}\qquad(j\in J),$$
--   whether or not they extend to a full chain as in $C_n(L)$.
--
--   These are the subchain counts whose expectations Assumption 1 constrains.
--
--   **Formalization Note** Families are strictly monotone maps on the subtype of $J$; primitivity, determinant and counting as in `prescribedChainCount`.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), §6, p.26

import Mathlib
import Definitions.Def_RandLatEnum_IsPrimitiveSub
import Definitions.Def_RandLatEnum_subDet

namespace RandLatEnum.Supplement

open RandLatEnum

/-- `C_{J,n}(L)`, the number of chains satisfying just the ranks and bounds indexed by `J`
(Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §6, p.26: "For nonempty J ⊆ {1, …, r − 1}, let C_{J,n}(L) count chains satisfying
just the ranks and bounds indexed by J, whether or not they extend to a full chain"): strictly
nested families `(M_j)_{j ∈ J}` of primitive sublattices of `L` with `rank M_j = ⌊x_j n⌋` and
`det M_j ≤ n^{h_j n}`.

**Formalization Note.** A family is a strictly monotone map from the subtype `↥J` (ordered as a
subset of `Fin (r+1)`), so only the members indexed by `J` are counted. Primitive, rank, det and
the count as in `prescribedChainCount`. -/
noncomputable def partialChainCount (n r : ℕ) (xs hs : Fin (r + 1) → ℝ) (J : Finset (Fin (r + 1)))
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℕ∞ :=
  {M : J → Submodule ℤ (EuclideanSpace ℝ (Fin n)) |
    StrictMono M ∧
      ∀ j : J, IsPrimitiveSub L (M j) ∧ Module.finrank ℤ (M j) = ⌊xs j * n⌋₊ ∧
        subDet (M j) ≤ (n : ℝ) ^ (hs j * n)}.encard

end RandLatEnum.Supplement


