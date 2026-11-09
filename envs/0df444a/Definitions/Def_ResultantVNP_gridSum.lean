-- Prove2me | Definitions.Def_ResultantVNP_gridSum
-- name    : ResultantVNP_gridSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:16.814673+00:00
-- url     : https://prove2.me/theorems/644192db-4ea3-4650-9baf-5c77966b9339
-- title:
--   Grid assignment sum $H_m(A)$ on the toroidal grid $\mathbb Z_m^2$
-- statement:
--   Consider the toroidal grid $\mathbb Z_m^2$ with one triangle $\{(i,j),(i+1,j),(i,j+1)\}$ anchored at each position $(i,j)$, coordinates modulo $m$. Every position $(i,j)$ carries an index class $\Omega_{ij}$; the classes are pairwise disjoint. For a symmetric tensor $A$ the **grid assignment sum** is
--
--   $$
--   H_m(A):=\sum_{\nu_{ij}\in\Omega_{ij}}\ \prod_{(i,j)\in\mathbb Z_m^2} a_{\nu_{ij},\nu_{i+1,j},\nu_{i,j+1}} ,
--   $$
--
--   each summand choosing one index at each position and using one tensor entry for each triangle. The product $\prod_{(i,j)}a_{\nu_{ij},\nu_{i+1,j},\nu_{i,j+1}}$ is the **monomial** of the assignment $\nu$.
--
--   **Formalization Note** The classes are the fibres of a class map $\mathrm{cls}:\iota\to\mathbb Z_m^2$; nonemptiness of the classes (surjectivity of $\mathrm{cls}$) is assumed in the statements that need it. Tensor entries lie in an arbitrary commutative ring.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.2, Eq. (4), pp.14–15

import Mathlib

namespace ResultantVNP

/-- The position `(i + 1, j)` of the toroidal grid `ℤ_m²`. -/
def gridRight {m : ℕ} (p : ZMod m × ZMod m) : ZMod m × ZMod m := (p.1 + 1, p.2)

/-- The position `(i, j + 1)` of the toroidal grid `ℤ_m²`. -/
def gridDown {m : ℕ} (p : ZMod m × ZMod m) : ZMod m × ZMod m := (p.1, p.2 + 1)

/-- The unordered index triple `{ν_{ij}, ν_{i+1,j}, ν_{i,j+1}}` used by an assignment `ν` on the
triangle anchored at `p = (i, j)`. -/
def assignTriple {m : ℕ} {ι : Type} (cls : ι → ZMod m × ZMod m)
    (ν : ∀ p : ZMod m × ZMod m, {α // cls α = p}) (p : ZMod m × ZMod m) : Sym ι 3 :=
  (ν p).1 ::ₛ (ν (gridRight p)).1 ::ₛ (ν (gridDown p)).1 ::ₛ Sym.nil

/-- The **monomial of an assignment** `ν` in `H_m`: `∏_{(i,j)} a_{ν_{ij}, ν_{i+1,j}, ν_{i,j+1}}`, as an
exponent vector over the unordered triples. -/
noncomputable def assignMonomial {m : ℕ} [NeZero m] {ι : Type} (cls : ι → ZMod m × ZMod m)
    (ν : ∀ p : ZMod m × ZMod m, {α // cls α = p}) : Sym ι 3 →₀ ℕ :=
  ∑ p : ZMod m × ZMod m, Finsupp.single (assignTriple cls ν p) 1

/-- The **grid assignment sum**
`H_m(A) := ∑_{ν_{ij} ∈ Ω_{ij}} ∏_{(i,j) ∈ ℤ_m²} a_{ν_{ij}, ν_{i+1,j}, ν_{i,j+1}}` of a symmetric tensor `A`:
each summand chooses one index at each position of the toroidal grid `ℤ_m²` and uses one tensor entry
for each triangle `{(i,j), (i+1,j), (i,j+1)}`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.2, Eq. (4), pp.14–15.

**Formalization Note** The index classes `Ω_{ij}` are the fibres `{α | cls α = (i, j)}` of a class map
`cls : ι → ℤ_m²` (pairwise disjoint automatically; the paper's nonemptiness is the surjectivity of
`cls`, assumed where the paper assumes it). A symmetric tensor is a function on unordered triples
`Sym ι 3` with values in a commutative ring `S`; an assignment is a dependent choice
`ν p ∈ Ω_p`. -/
noncomputable def gridSum {m : ℕ} [NeZero m] {ι : Type} [Fintype ι] [DecidableEq ι] {S : Type}
    [CommRing S] (cls : ι → ZMod m × ZMod m) (A : Sym ι 3 → S) : S :=
  ∑ ν : (∀ p : ZMod m × ZMod m, {α // cls α = p}), ∏ p : ZMod m × ZMod m, A (assignTriple cls ν p)

end ResultantVNP


