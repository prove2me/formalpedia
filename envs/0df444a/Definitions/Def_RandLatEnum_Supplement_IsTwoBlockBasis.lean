-- Prove2me | Definitions.Def_RandLatEnum_Supplement_IsTwoBlockBasis
-- name    : RandLatEnum_Supplement_IsTwoBlockBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:15.372755+00:00
-- url     : https://prove2.me/theorems/69acf338-c383-4077-b75e-2813cd2e854a
-- title:
--   Two-block basis over a sublattice $M$
-- statement:
--   Let $L\subset\mathbb R^n$ be a lattice, $M$ a sublattice and $m\le n$. An ordered family $B=(b_1,\dots,b_n)$ is a **two-block basis over $M$** if, writing $B'=(b_1,\dots,b_m)$,
--
--   1. $B'$ generates $M$ over $\mathbb Z$;
--   2. $B'$ is a **reversed dual-HKZ** basis of $M$: reversing its dual basis (taken in $\operatorname{span}M$) gives an HKZ basis of the dual lattice $M^*$;
--   3. the projections of $b_{m+1},\dots,b_n$ orthogonally to $\operatorname{span}_{\mathbb R}M$ form an HKZ-reduced family, i.e. an HKZ basis of the orthogonal quotient $Q=\pi_{M^\perp}(L)$, of which $b_{m+1},\dots,b_n$ are lifts.
--
--   This is the basis "combining a reversed dual-HKZ basis of $M$ with lifts of an HKZ basis of its orthogonal quotient" of Theorem 1.2.
--
--   **Formalization Note** Reversed dual-HKZ uses the encoding of the published milestone `RandLatEnum.eq_4_5`, `IsReduced (revBasis (dualBasis B'))`. The lifts are arbitrary; that $B$ is a basis of $L$ is imposed where the predicate is used.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), Theorem 1.2, p.4; §5.2, p.24

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced
import Definitions.Def_RandLatEnum_dualBasis
import Definitions.Def_RandLatEnum_revBasis

namespace RandLatEnum.Supplement

open KannanLattice.Core RandLatEnum

/-- `b` is a **two-block basis over `M`** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.2, p.4, and §5.2, p.24:
"Combining a reversed dual-HKZ basis of M with lifts of an HKZ basis of its orthogonal quotient
gives a basis B2 of L"): with `b' = (b_1, …, b_m)` its first `m` vectors,
1. `b'` spans `M` over `ℤ`;
2. `b'` is a reversed dual-HKZ basis of `M`: the reversal of its dual basis (in `span M`) is HKZ;
3. the last `n − m` vectors, projected orthogonally to `span_ℝ M`, form an HKZ family: they are an
   HKZ basis of the orthogonal quotient `Q = π_{M⊥}(L)`, and the `b_{m+j}` are lifts of it.

**Formalization Note.** "Reversed dual-HKZ" is the encoding of the published `RandLatEnum.eq_4_5`:
`IsReduced (revBasis (dualBasis b'))`. HKZ is the published `KannanLattice.Core.IsReduced`. The
lifts are arbitrary: only their projections are constrained (the paper's optional size reduction
does not change Gram–Schmidt lengths and is not required). That `b` is a basis of `L` is imposed
where the predicate is used. -/
def IsTwoBlockBasis {n k : ℕ} (m : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin k)))
    (b : Fin n → EuclideanSpace ℝ (Fin k)) : Prop :=
  ∃ hm : m ≤ n,
    lattice (fun i : Fin m => b (Fin.castLE hm i)) = M ∧
    IsReduced (revBasis (dualBasis (fun i : Fin m => b (Fin.castLE hm i)))) ∧
    IsReduced (fun j : Fin (n - m) =>
      (Submodule.span ℝ (Set.range (fun i : Fin m => b (Fin.castLE hm i))))ᗮ.starProjection
        (b ⟨m + j.val, by have := j.isLt; omega⟩))

end RandLatEnum.Supplement


