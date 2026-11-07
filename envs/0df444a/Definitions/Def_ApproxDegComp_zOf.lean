-- Prove2me | Definitions.Def_ApproxDegComp_zOf
-- name    : ApproxDegComp_zOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:00.239827+00:00
-- url     : https://prove2.me/theorems/ae793e09-c61e-4b8e-9fe8-4321e6ea2a22
-- title:
--   Sign points $z\in\{-1,1\}$ and the index $(1+z)/2$
-- statement:
--   A sign $z\in\{-1,1\}$ is encoded by a Boolean value $b$, with $z=1$ for $b=\mathrm{true}$ and $z=-1$ for $b=\mathrm{false}$. Then $(1+z)/2$ is the 0/1 value of $b$, so $\nu_{(1+z)/2}$ is $\nu_b$: $z=1$ corresponds to $\nu_1$ and to $g=1$.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 21, p.22; Lemma 9, p.16

import Mathlib

namespace ApproxDegComp

/-- **The sign point** `z ∈ {−1, 1}` (Lemmas 9, 21, 22, pp.16, 22).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 21, p.22: "Consequently, for z ∈ {−1, 1}, ν_{(1+z)/2} = ρ₀ + (z/κ) ρ′₀."

`zOf b` is `1` for `true` and `−1` for `false`, so that `(1 + zOf b)/2` is the 0/1 value
of `b` and `ν_{(1+z)/2}` is `ν b`.

**Formalization Note** A point `z ∈ {−1,1}ⁿ` is `z : Fin n → Bool` read through `zOf`; then
`z = 1 ↔ ν₁ ↔ g = 1`. -/
def zOf (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem zOf_true : zOf true = 1 := rfl
@[simp] theorem zOf_false : zOf false = -1 := rfl

end ApproxDegComp


