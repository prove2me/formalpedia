-- Prove2me | Definitions.Def_NoPerfectRandComp_IsPrivateMap
-- name    : NoPerfectRandComp_IsPrivateMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:21.441936+00:00
-- url     : https://prove2.me/theorems/7c543e71-3951-4748-b5d8-eb2bd318701d
-- title:
--   Linear map $H:\mathbb F_2^{36a}\to\mathbb F_2^{a}$ with private marginals
-- statement:
--   A linear map $H : \mathbb F_2^{36a} \to \mathbb F_2^{a}$ has **private marginals** when it is surjective and the uniform distributions on any two fibres of $H$ have identical marginals on every set $J$ of at most $12a$ input coordinates, these marginals being uniform. Equivalently: for every $J$ with $|J| \le 12a$, all $v, v' \in \mathbb F_2^a$ and all patterns $\rho, \rho' \in \mathbb F_2^J$,
--   $$
--   \big|\{x \in H^{-1}(v) : x|_J = \rho\}\big| = \big|\{x \in H^{-1}(v') : x|_J = \rho'\}\big| .
--   $$
--
--   A cell encoded through such a map conceals its payload until more than $12a$ of its bits have been read.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 4.5, p.14

import Mathlib

namespace NoPerfectRandComp

/-- A linear map `H : 𝔽₂^{36a} → 𝔽₂^a` with private marginals (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Lemma 4.5, p.14): `H` is
surjective, and the uniform distributions on any two fibres of `H` have identical marginals on any
set `J` of at most `12a` input coordinates, and these marginals are uniform.

**Formalization Note** Both marginal properties are stated as one count identity: for every such
`J`, every two fibres `H⁻¹(v)`, `H⁻¹(v')` and every two patterns `ρ, ρ'` on `J`, the number of
points of `H⁻¹(v)` agreeing with `ρ` on `J` equals the number of points of `H⁻¹(v')` agreeing with
`ρ'` on `J`. -/
def IsPrivateMap (a : ℕ) (H : (Fin (36 * a) → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2)) : Prop :=
  Function.Surjective H ∧
  ∀ J : Finset (Fin (36 * a)), J.card ≤ 12 * a →
    ∀ (v v' : Fin a → ZMod 2) (ρ ρ' : J → ZMod 2),
      (Finset.univ.filter (fun x => H x = v ∧ ∀ j : J, x j = ρ j)).card =
        (Finset.univ.filter (fun x => H x = v' ∧ ∀ j : J, x j = ρ' j)).card

end NoPerfectRandComp


