-- Prove2me | Definitions.Def_MaxEntOCRS_IsRHPZeroFree
-- name    : MaxEntOCRS_IsRHPZeroFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:14.415645+00:00
-- url     : https://prove2.me/theorems/493b801f-9bdb-4504-8757-3fe536a01b81
-- title:
--   Right-half-plane zero-free laws
-- statement:
--   A law $\nu$ of a random subset of a finite index set is **right-half-plane zero-free** if its generating polynomial
--   $$
--   g_\nu(z) = \sum_F \nu(F) \prod_{i \in F} z_i
--   $$
--   has no zeros when all real parts are positive: $g_\nu(z) \ne 0$ whenever $\operatorname{Re} z_i > 0$ for every $i$. For a nonnegative $\nu$ this polynomial is automatically multiaffine with nonnegative coefficients. The property is weaker than real stability and allows positive correlations.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 4, p.6

import Mathlib

namespace MaxEntOCRS

/-- A law `ν` of a random subset of a finite index set is *right-half-plane zero-free* if its
generating polynomial `g_ν(z) = ∑_F ν(F) ∏_{i ∈ F} z_i` has no zeros when all real parts are
positive (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §4, p.6). Multiaffinity and nonnegative coefficients are automatic for a
nonnegative `ν`; nonnegativity and normalization are separate hypotheses where used. -/
def IsRHPZeroFree {ι : Type} [Fintype ι] (ν : Finset ι → ℝ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, 0 < (z i).re) → ∑ F, (ν F : ℂ) * ∏ i ∈ F, z i ≠ 0

end MaxEntOCRS


