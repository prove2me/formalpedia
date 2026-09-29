-- Prove2me | Definitions.Def_Gamma0UnitsChar
-- name    : Gamma0UnitsChar
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/1f1e66f3-b333-535f-9679-d5489717fb4b
-- title:
--   The units-valued character of Γ0​(N) on lower-right entries
-- statement:
--   For a natural number $N$, Mathlib's `CongruenceSubgroup.Gamma0Map N` is the monoid homomorphism sending a matrix in $\Gamma_0(N)$ to the reduction mod $N$ of its lower right-hand entry; this is multiplicative because the upper right-hand entry is divisible by $N$. Since $\Gamma_0(N)$ is a group, every value of this map is a unit (the determinant condition makes the reduced upper left-hand entry an inverse), and [`Ihara.gamma0UnitsHom N`](../def/Gamma0UnitsChar.html#L5) is the resulting homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ obtained by lifting `Gamma0Map N` along the unit group. Its defining property is recorded by [`Ihara.gamma0UnitsHom_coe`](../def/Gamma0UnitsChar.html#L9): for $g \in \Gamma_0(N)$, the image of `gamma0UnitsHom N g` in $\mathbb{Z}/N$ is `CongruenceSubgroup.Gamma0Map N g`, i.e. the class of the lower right-hand entry of $g$.
--
--   The second declaration [`Ihara.gamma0UnitsChar N`](../def/Gamma0UnitsChar.html#L13) is the same homomorphism written additively: it is a homomorphism of additive groups $\mathrm{Additive}(\Gamma_0(N)) \to+ \mathrm{Additive}((\mathbb{Z}/N)^\times)$, obtained by transporting `gamma0UnitsHom N` along the `Additive` type synonym, so that it can be composed with additive homomorphisms out of $\mathrm{Additive}((\mathbb{Z}/N)^\times)$. The companion lemma [`Ihara.gamma0UnitsChar_apply`](../def/Gamma0UnitsChar.html#L18) states that on an element $g$ of $\mathrm{Additive}(\Gamma_0(N))$ its value is the image under `Additive.ofMul` of `gamma0UnitsHom N` applied to the corresponding element of $\Gamma_0(N)$. Both declarations are made for an arbitrary $N$, with no coprimality or positivity restriction; for $N \le 1$ the target is trivial.
--
--   **Relation to Mathlib.** `CongruenceSubgroup.Gamma0` and `CongruenceSubgroup.Gamma0Map` (the lower right-hand entry mod $N$, valued in the ring $\mathbb{Z}/N$) are Mathlib's; what is added here is the units-valued form of that map together with its `Additive`-wrapped counterpart.
--
--   **Where it is used.** These two forms of the character are the target of the factorisation asserted by Ihara's lemma as formalised in this development: homomorphisms from $\Gamma_0(N)$ to a suitable abelian group satisfying the hypotheses of the lemma are shown to factor as a character of $(\mathbb{Z}/N)^\times$ composed with `gamma0UnitsChar N`, the additive form being the one against which such a composition is stated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Gamma0UnitsChar.lean

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Ihara

def gamma0UnitsHom (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

@[simp]
theorem gamma0UnitsHom_coe (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    (gamma0UnitsHom N g : ZMod N) = CongruenceSubgroup.Gamma0Map N g :=
  rfl

def gamma0UnitsChar (N : ℕ) :
    Additive (CongruenceSubgroup.Gamma0 N) →+ Additive (ZMod N)ˣ :=
  MonoidHom.toAdditive (gamma0UnitsHom N)

@[simp]
theorem gamma0UnitsChar_apply (N : ℕ) (g : Additive (CongruenceSubgroup.Gamma0 N)) :
    gamma0UnitsChar N g = Additive.ofMul (gamma0UnitsHom N g.toMul) :=
  rfl

end Ihara


