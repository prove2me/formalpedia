-- Prove2me | Definitions.Def_AutomorphicForm_TwistedAdelicKernel
-- name    : AutomorphicForm_TwistedAdelicKernel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a4dec4b9-295a-5f95-94ee-b6f56ae7ed2a
-- title:
--   Twisted adelic kernel for GL2​ over a number field
-- statement:
--   Fix a number field $F$; write $\mathbb{A}_F$ for the adele ring of $F$ (the Mathlib `AdeleRing (𝓞 F) F`) and $\mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`, the general linear group of $2\times 2$ matrices over $\mathbb{A}_F$. Let `globalPoints` denote the group homomorphism $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_F)$ obtained by applying the structure map $F\to\mathbb{A}_F$ entrywise. For a monoid endomorphism $\sigma_A$ of $\mathrm{GL}_2(\mathbb{A}_F)$, a function $f\colon\mathrm{GL}_2(\mathbb{A}_F)\to M$ with values in an additive commutative monoid $M$, and $x,y\in\mathrm{GL}_2(\mathbb{A}_F)$, the definition `twistedAdelicKernel` sets
--   $$K^{\sigma_A}_f(x,y)\;=\;\sum_{\gamma\in\mathrm{GL}_2(F)}^{\mathrm{f}} f\bigl(x^{-1}\,\gamma\,\sigma_A(y)\bigr),$$
--   where $\gamma$ is transported to $\mathrm{GL}_2(\mathbb{A}_F)$ by `globalPoints` and the sum is the finitely-supported sum `∑ᶠ`: it is the sum over the support when that support is finite and $0$ otherwise, so that any statement needing genuine summation must supply its own finiteness input. No hypothesis relating $\sigma_A$ to the rational points, nor any continuity or compact-support condition on $f$, is imposed; $\sigma_A$ is an arbitrary monoid endomorphism.
--
--   Two identities record the behaviour at the two degenerate choices of twist. `twistedAdelicKernel_id` states that for $\sigma_A$ the identity endomorphism the twisted kernel agrees, for all $f$, $x$, $y$, with the untwisted kernel `adelicKernel F f x y`, which is the same sum with $\sigma_A(y)$ replaced by $y$. `twistedAdelicKernel_one` states that for $\sigma_A$ the trivial homomorphism (constant value $1$) the resulting kernel is independent of its second argument: its values at $y$ and at $y'$ coincide for all $y,y'$.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, `Matrix.GeneralLinearGroup` and the finitely-supported sum `∑ᶠ`; the automorphic kernel, twisted or not, is the project's own notion.
--
--   **Where it is used.** These kernels belong to the project's adelic layer for automorphic forms on $\mathrm{GL}_2$, alongside the untwisted kernel and its decomposition into central, unipotent, hyperbolic and elliptic cells of $\mathrm{GL}_2(F)$ and the local-finiteness predicate `AdelicKernelLocalFiniteness`, which quantifies over all second arguments and hence applies after transport along $y\mapsto\sigma_A(y)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_TwistedAdelicKernel.lean

import Definitions.Def_AutomorphicForm_AdelicKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NumberField

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def twistedAdelicKernel {M : Type*} [AddCommMonoid M]
    (σA : AdelicGL2 (𝓞 F) F →* AdelicGL2 (𝓞 F) F)
    (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ : Matrix.GeneralLinearGroup (Fin 2) F,
    f (x⁻¹ * globalPoints (𝓞 F) F γ * σA y)

theorem twistedAdelicKernel_id {M : Type*} [AddCommMonoid M]
    (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) :
    twistedAdelicKernel F (MonoidHom.id _) f x y = adelicKernel F f x y :=
  rfl

theorem twistedAdelicKernel_one {M : Type*} [AddCommMonoid M]
    (f : AdelicGL2 (𝓞 F) F → M) (x y y' : AdelicGL2 (𝓞 F) F) :
    twistedAdelicKernel F 1 f x y = twistedAdelicKernel F 1 f x y' :=
  rfl

end AutomorphicForm


