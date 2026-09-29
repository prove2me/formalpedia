-- Prove2me | Definitions.Def_LanglandsTunnell_BcWeight
-- name    : LanglandsTunnell_BcWeight
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/5c7d38ba-4953-5a9d-87cc-e66270ba7837
-- title:
--   Base-changed weight function on primes of the upper field
-- statement:
--   The setting is a pair of fields $F$, $K$ together with an algebra structure of $\mathcal{O}_F$ on $\mathcal{O}_K$ which is integral, and a commutative ring $R$ of coefficients. In this context a *weight* over $F$ is simply a function $\chi$ from the height-one spectrum of $\mathcal{O}_F$ to $R$, i.e. an arbitrary $R$-valued function on the nonzero primes of $\mathcal{O}_F$, with no multiplicativity or automorphic condition imposed.
--
--   The single definition [`LanglandsTunnell.bcWeight`](../def/LanglandsTunnell_BcWeight.html#L12) transports such a weight to the height-one spectrum of $\mathcal{O}_K$: for a prime $\mathfrak{P}$ of $\mathcal{O}_K$, let $\mathfrak{p} = \mathfrak{P}.\mathrm{under}\,(\mathcal{O}_F)$ be the prime of $\mathcal{O}_F$ lying under it (the contraction of $\mathfrak{P}$ along the algebra map), and let $f$ be Mathlib's `Ideal.inertiaDeg'` of $\mathfrak{P}$ over $\mathfrak{p}$, the residue degree $[\,\mathcal{O}_K/\mathfrak{P} : \mathcal{O}_F/\mathfrak{p}\,]$. Then
--   $$(\mathrm{bcWeight}\ F\ K\ \chi)(\mathfrak{P}) \;=\; \chi(\mathfrak{p})^{\,f}.$$
--   This is the shape a character-type weight acquires under base change at unramified places: the local parameter at $\mathfrak{P}$ is the $f$-th power of the local parameter at $\mathfrak{p}$. Exponentiation is the monoid power in $R$, so for $f = 0$ the value is $1$; in particular the constant weight $1$ is sent to the constant weight $1$.
--
--   The accompanying `@[simp]` lemma `bcWeight_apply` records this defining equation, making it available for rewriting. Nothing here asserts automorphy, cuspidality, or that any eigensystem is a base change; the definition is the weight-level companion of the formal base change of Hecke eigensystems, whose $b$-component is likewise the $f$-th power of the datum below and whose $a$-component is the corresponding `satakePow`.
--
--   **Relation to Mathlib.** Built directly on Mathlib's `IsDedekindDomain.HeightOneSpectrum`, the `under` operation on primes, and `Ideal.inertiaDeg'`; the weight-transport function itself is the project's own.
--
--   **Where it is used.** The function is used alongside the project's formal base change of Hecke eigensystems ([`AutomorphicForm.formalBaseChange`](../def/AutomorphicForm_FormalBaseChange.html#L16), with its `satakePow` recursion for the $a$-parameters) to express the compatibility of base change with twisting: twisting over $F$ by $\chi$ and then base-changing to $K$ yields the base change twisted by $\mathrm{bcWeight}\ F\ K\ \chi$. This bookkeeping belongs to the Langlands–Tunnell input used to make the mod $3$ representation attached to a Frey curve modular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_BcWeight.lean

import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField IsDedekindDomain

variable (F K : Type) [Field F] [Field K] [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]

noncomputable def bcWeight (χ : HeightOneSpectrum (𝓞 F) → R) : HeightOneSpectrum (𝓞 K) → R :=
  fun 𝔓 => χ (𝔓.under (𝓞 F)) ^ (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal

@[simp] theorem bcWeight_apply (χ : HeightOneSpectrum (𝓞 F) → R) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    bcWeight F K χ 𝔓 = χ (𝔓.under (𝓞 F)) ^ (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal :=
  rfl

end LanglandsTunnell


