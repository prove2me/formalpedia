-- Prove2me | Definitions.Def_HeckeCharacter_FiniteOrder
-- name    : HeckeCharacter_FiniteOrder
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/dd915941-6625-5166-bcc0-c10448370ee2
-- title:
--   Finite-order Hecke characters and their congruence moduli
-- statement:
--   Fix a number field $K$, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K`, whose elements are pairs consisting of an infinite and a finite component. The module introduces three declarations concerning characters $\chi : \mathbb{A}_K^\times \to \mathbb{C}^\times$ (monoid homomorphisms into $\mathbb{C}^\times$).
--
--   `IsFiniteOrderHeckeChar K χ` is a structure in `Prop` bundling three conditions on $\chi$: that [`AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ`](../def/AutomorphicForm_AdelicLsXi.html#L21) holds, i.e. $\chi$ kills the image of $K^\times$ under the diagonal embedding $K^\times \to \mathbb{A}_K^\times$, so that $\chi$ is a character of the idele class group; that $\chi$ is continuous; and that $\chi$ is of finite order in the (pointwise) group of characters, i.e. $\chi^n = 1$ for some $n \ge 1$, so all values of $\chi$ are roots of unity of bounded order.
--
--   `idealMultiplicity K v 𝔣` attaches to a height-one prime $v$ of $\mathcal{O}_K$ and an ideal $\mathfrak{f} \subseteq \mathcal{O}_K$ the natural number counting how often the prime $v$ occurs among the factors of $\mathfrak{f}$, taken in the associates monoid; for $\mathfrak{f} = \mathcal{O}_K$ all these multiplicities vanish. No nonvanishing hypothesis is imposed on $\mathfrak{f}$.
--
--   `AdmitsModulus K χ 𝔣` asserts that $\chi$ is trivial on the congruence subgroup of level $\mathfrak{f}$: for every idele unit $u$ whose infinite component is $1$ and whose finite component satisfies, at every height-one prime $v$, both $v(u_v) = 1$ and $v(u_v - 1) \le \exp(-n_v)$ with $n_v =$ `idealMultiplicity K v 𝔣` (valuations taken in `ℤᵐ⁰` through `Valued.v`), one has $\chi(u) = 1$. Thus the conditions say $u_v \in \mathcal{O}_v^\times$ at all finite places and $u_v \equiv 1 \bmod \mathfrak{p}_v^{n_v}$ at the primes dividing $\mathfrak{f}$. This is a triviality condition on a subgroup, not the assertion that $\mathfrak{f}$ is the conductor.
--
--   **Relation to Mathlib.** The adele ring, the height-one spectrum of a Dedekind domain, the `ℤᵐ⁰`-valued local valuations and `IsOfFinOrder` are Mathlib's; the three predicates here are the project's own, layered on the project notion [`AutomorphicForm.IsIdeleClassChar`](../def/AutomorphicForm_AdelicLsXi.html#L21).
--
--   **Where it is used.** These predicates single out the characters of the idele class group that serve as central characters and nebentypus data for adelic automorphic forms on $\mathrm{GL}_2$ over $K$, the setting in which the modular forms attached to elliptic curves are handled in the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HeckeCharacter_FiniteOrder.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain WithZero

noncomputable section

namespace HeckeCharacter

variable (K : Type*) [Field K] [NumberField K]

structure IsFiniteOrderHeckeChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop where
  isIdeleClassChar : IsIdeleClassChar (𝓞 K) K χ
  continuous : Continuous χ
  isOfFinOrder : IsOfFinOrder χ

def idealMultiplicity (v : HeightOneSpectrum (𝓞 K)) (𝔣 : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors

def AdmitsModulus (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ u : (AdeleRing (𝓞 K) K)ˣ,
    (u : AdeleRing (𝓞 K) K).1 = 1 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 ∧
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v - 1)
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) →
    χ u = 1

end HeckeCharacter


