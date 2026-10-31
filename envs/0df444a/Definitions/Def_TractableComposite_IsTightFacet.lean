-- Prove2me | Definitions.Def_TractableComposite_IsTightFacet
-- name    : TractableComposite_IsTightFacet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:46.046993+00:00
-- url     : https://prove2.me/theorems/f8ee7be4-ff2a-4e18-9fb8-b02c9c16fb5e
-- title:
--   A facet-defining inequality tight at a point
-- statement:
--   Let $f$ be a function on a set $D$ (in every use, a concave envelope over $D$) and $h(u)=\langle\alpha,u\rangle+b$ an affine function. The inequality $f\le h$ is a facet-defining inequality of $f$ over $D$, tight at $x$, if
--
--   1. it is valid: $f(u)\le h(u)$ for all $u\in D$;
--   2. $x$ lies in the tight set $T=\{u\in D\mid f(u)=h(u)\}$;
--   3. $\dim T=\dim D$ (dimensions of affine hulls).
--
--   The face of the hypograph of $f$ cut out by $h$ is the graph of $h$ over $T$, so condition 3 says this face is a facet. An inequality of the form $\phi\le\langle\alpha,u\rangle+b$ is non-vertical.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), p.12 (tight set $T^{(\alpha,b)}_f(X)$) and the proofs of Corollary 2 and Theorem 2, pp.13–14

import Mathlib

namespace TractableComposite

/-- **A facet-defining inequality `f ≤ h` of a function over `D`, tight at `x`.** He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.12
(tight set `T_f^{(α,b)}(X) = {x ∈ X | conc_X(f)(x) = ⟨α,x⟩ + b}`) and the proofs of Corollary 2 and
Theorem 2, pp.13–14 (a facet is a valid inequality whose tight set has dimension `dim` of the domain).

`IsTightFacet D f h x` says, for the function `f` (in every use, a concave envelope `conc_D(·)`) and
the affine function `h` (in every use, `u ↦ ⟨α,u⟩ + b`):
1. validity: `f u ≤ h u` for all `u ∈ D`;
2. tightness at `x`: `x ∈ T`, where `T = {u ∈ D | f u = h u}`;
3. facet: the affine hull of `T` has the dimension of the affine hull of `D`.

**Formalization Note.** Reading R5: the face of the hypograph of `f` cut out by `h` is the graph of
`h` over `T`, so it is a facet exactly when `dim T = dim D`; an inequality of the form `φ ≤ ⟨α,u⟩ + b`
is automatically non-vertical. Dimensions are `Module.finrank` of `vectorSpan`. -/
def IsTightFacet {E : Type*} [AddCommGroup E] [Module ℝ E] (D : Set E) (f h : E → ℝ) (x : E) :
    Prop :=
  (∀ u ∈ D, f u ≤ h u) ∧ x ∈ {u ∈ D | f u = h u} ∧
    Module.finrank ℝ (vectorSpan ℝ {u ∈ D | f u = h u}) = Module.finrank ℝ (vectorSpan ℝ D)

end TractableComposite


