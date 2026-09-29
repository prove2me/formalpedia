-- Prove2me | Definitions.Def_CuspForm_IntegralLattice
-- name    : CuspForm_IntegralLattice
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/77625404-58b4-5919-8a01-ebd9c7d965a5
-- title:
--   Integral q-expansion lattices and the mod-3 Eisenstein bridge
-- statement:
--   Fix a level $N$. [`CuspForm.qIntegralSet N`](../def/CuspForm_IntegralLattice.html#L11) is the set of weight-two cusp forms $f$ on $\Gamma_0(N)$ whose $q$-expansion coefficients are all rational integers: the coefficients are taken to be [`ModularFormClass.qCoeff f n`](../def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the expansion of $f$ in $q = e^{2\pi i z}$ (Mathlib's `qExpansion` with width $1$), and integrality is expressed as membership in $(\bot : \mathrm{Subring}\ \mathbb{C})$, the smallest subring of $\mathbb{C}$, i.e. the image of $\mathbb{Z}$. [`CuspForm.qIntegralLattice N`](../def/CuspForm_IntegralLattice.html#L14) is defined as the $\mathbb{Z}$-span of this set inside $S_2(\Gamma_0(N))$ (the set is already closed under the module operations, so the span adds nothing mathematically, but the span presentation is what is recorded). [`CuspForm.HasIntegralBasis N`](../def/CuspForm_IntegralLattice.html#L17) is the proposition that the $\mathbb{C}$-span of `qIntegralSet N` is all of $S_2(\Gamma_0(N))$; it is the assertion of the $q$-expansion principle for this level, stated as a predicate on $N$ rather than proved here.
--
--   [`bridgeProduct`](../def/CuspForm_IntegralLattice.html#L22) takes a commutative ring $R$ and a sequence $a : \mathbb{N} \to R$ and returns the formal power series $\bigl(\sum_{n} a_n q^n\bigr)\cdot E_1(\chi_{-3})$, where $E_1(\chi_{-3})$ is the weight-one Eisenstein series $1 + 6\sum_{n\ge 1}\bigl(\sum_{d \mid n}\chi_{-3}(d)\bigr)q^n$ realised over $R$ by `e1Chi3In`, with $\chi_{-3}$ the quadratic character of conductor $3$. Finally, [`CuspForm.IsLatticeRealized N a`](../def/CuspForm_IntegralLattice.html#L27), for a sequence $a : \mathbb{N} \to \mathbb{Z}$, asserts the existence of a weight-two cusp form $f$ on $\Gamma_0(N)$ lying in `qIntegralSet N`, together with integers $a_f(n)$ whose complex images are the coefficients `qCoeff f n`, such that $3 \mid a_f(n) - c_n$ for every $n$, where $c_n$ is the $n$-th coefficient of [`bridgeProduct a`](../def/CuspForm_IntegralLattice.html#L22) over $\mathbb{Z}$. This is a purely coefficientwise congruence modulo $3$: no eigenform, newform or Hecke-equivariance condition is imposed on $f$, and no isomorphism of Galois representations is asserted.
--
--   **Relation to Mathlib.** Mathlib supplies `CuspForm`, the congruence subgroups `Gamma0`/`Gamma1` and the $q$-expansion machinery; the integrality predicate on $q$-expansions, the resulting lattice, the $q$-expansion-principle statement, the formal weight-one Eisenstein series for $\chi_{-3}$ and the bridge product are the project's own.
--
--   **Where it is used.** These notions package the passage from weight one to weight two in the Langlands–Tunnell step: a weight-one form with integral coefficients is multiplied by the weight-one Eisenstein series $E_1(\chi_{-3})$, whose $q$-expansion is $\equiv 1 \pmod 3$, and the product is matched modulo $3$ with a genuine integral weight-two cusp form of level $N$, the existence of such a form being the content of `IsLatticeRealized`. `HasIntegralBasis` records the $q$-expansion principle needed to produce the weight-two lift from its reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_IntegralLattice.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularFormClass CongruenceSubgroup EisensteinWeightOne

namespace CuspForm

def qIntegralSet (N : ℕ) : Set (CuspForm (Gamma0 N) 2) :=
  {f | ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ (⊥ : Subring ℂ)}

def qIntegralLattice (N : ℕ) : Submodule ℤ (CuspForm (Gamma0 N) 2) :=
  Submodule.span ℤ (qIntegralSet N)

def HasIntegralBasis (N : ℕ) : Prop :=
  Submodule.span ℂ (qIntegralSet N) = ⊤

end CuspForm

noncomputable def bridgeProduct {R : Type*} [CommRing R] (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk a * e1Chi3In R

namespace CuspForm

def IsLatticeRealized (N : ℕ) (a : ℕ → ℤ) : Prop :=
  ∃ f : CuspForm (Gamma0 N) 2, f ∈ qIntegralSet N ∧
    ∃ af : ℕ → ℤ, (∀ n, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
      ∀ n, (3 : ℤ) ∣ af n - (bridgeProduct a).coeff n

end CuspForm


