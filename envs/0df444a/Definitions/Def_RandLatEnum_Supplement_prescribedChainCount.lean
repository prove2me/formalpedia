-- Prove2me | Definitions.Def_RandLatEnum_Supplement_prescribedChainCount
-- name    : RandLatEnum_Supplement_prescribedChainCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:00:18.718207+00:00
-- url     : https://prove2.me/theorems/5a338044-09cb-4cea-bc6c-84853e710e52
-- title:
--   Number $C_n(L)$ of prescribed chains of primitive sublattices
-- statement:
--   Fix $r$, rank fractions $x_0,\dots,x_r$ and determinant exponents $h_0,\dots,h_r$. For a lattice $L\subset\mathbb R^n$, $C_n(L)$ is the number of chains of primitive sublattices
--   $$\{0\}=M_0\subset M_1\subset\dots\subset M_r=L,\qquad \operatorname{rank}M_i=\lfloor x_in\rfloor,\qquad \det M_i\le n^{h_in}\quad(1\le i<r).$$
--
--   It is the count whose positivity Assumption 1 predicts.
--
--   **Formalization Note** Chains are strictly monotone families indexed by $\{0,\dots,r\}$; primitivity and $\det$ are the published `IsPrimitiveSub` and `subDet`; the count is an extended natural number (`Set.encard`).
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), §6, (6.2), p.26

import Mathlib
import Definitions.Def_RandLatEnum_IsPrimitiveSub
import Definitions.Def_RandLatEnum_subDet

namespace RandLatEnum.Supplement

open RandLatEnum

/-- `C_n(L)`, the number of chains of primitive sublattices with prescribed ranks and determinant
bounds (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §6, (6.2), p.26):
`{0} = M_0 ⊂ ⋯ ⊂ M_r = L`, `rank M_i = ⌊x_i n⌋`, `det M_i ≤ n^{h_i n}` `(1 ≤ i < r)`.

**Formalization Note.** A chain is a strictly monotone family `M : Fin (r+1) → Submodule` with
`M 0 = {0}`, `M r = L`, every `M i` primitive in `L` (published `IsPrimitiveSub`) of rank
`⌊x_i n⌋₊` (`Module.finrank ℤ`); the bound uses the published `subDet` and is imposed only for
`1 ≤ i < r`. The count is `Set.encard` (an infinite count is `⊤`, never `0`), as in the
published `chainCount`. -/
noncomputable def prescribedChainCount (n r : ℕ) (xs hs : Fin (r + 1) → ℝ)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℕ∞ :=
  {M : Fin (r + 1) → Submodule ℤ (EuclideanSpace ℝ (Fin n)) |
    M 0 = ⊥ ∧ M (Fin.last r) = L ∧ StrictMono M ∧
      ∀ i : Fin (r + 1), IsPrimitiveSub L (M i) ∧ Module.finrank ℤ (M i) = ⌊xs i * n⌋₊ ∧
        (i ≠ 0 → i ≠ Fin.last r → subDet (M i) ≤ (n : ℝ) ^ (hs i * n))}.encard

end RandLatEnum.Supplement


