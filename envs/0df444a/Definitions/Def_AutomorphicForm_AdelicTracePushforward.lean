-- Prove2me | Definitions.Def_AutomorphicForm_AdelicTracePushforward
-- name    : AutomorphicForm_AdelicTracePushforward
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/ce7c548e-c4fa-5f8a-a5f8-34afd7dded30
-- title:
--   Adelic trace fibres, push-forwards and semi-local factorisation
-- statement:
--   Throughout, $K \subseteq L$ is an extension of number fields, with $n = \dim_K L$ and with $\mathbb{A}_K$, $\mathbb{A}_L$ the adele rings of $K$ and $L$ (each a product of the infinite and finite adeles). Write $H = \ker(\mathrm{Tr}_{L/K} \colon L \to K)$ and let $c_0,\dots$ be the entries of `Module.finBasis K H`, a chosen $K$-basis of $H$, indexed by `Fin (Module.finrank K H)`.
--
--   `traceFibre` parametrises the fibres of the trace in additive coordinates: given $r \in \mathbb{A}_K$ and a tuple $w$ of elements of $\mathbb{A}_K$ indexed by the basis of $H$, it returns $\beta(r)\cdot n^{-1} + \sum_i \beta(w_i)\, c_i$ in $\mathbb{A}_L$, where $\beta$ is the conorm ring homomorphism [`M4aHerbrand.Bridge.genuineβ`](../def/M4aHerbrand_GenuineBeta.html#L14) from $\mathbb{A}_K$ to $\mathbb{A}_L$ (archimedean conorm times finite conorm), $n^{-1}$ and the $c_i$ being viewed in $\mathbb{A}_L$ through $L$. `tracePushforward` integrates a function $F$ on $\mathbb{A}_L$ over these coordinates: $r \mapsto \int F(\mathrm{traceFibre}(r,w))\,dw$ against the product, over the basis index, of the adelic additive Haar measure `adelicAddHaar` of $K$.
--
--   `localTraceFibre` and `localTracePushforward` are the semi-local analogues at a finite place $v$ of $K$, with $L \otimes_K K_v$ in place of $\mathbb{A}_L$: the fibre coordinate is $n^{-1} \otimes r + \sum_i c_i \otimes w_i$, and the integration uses the product of copies of the additive Haar measure of $K_v$ rescaled so that the valuation ring $\mathcal{O}_v$ has mass $1$.
--
--   `actSubId` is the increment $\sigma\!\cdot\!x - x$ of an automorphism $\sigma \in \mathrm{Gal}(L/K)$ acting on $\mathbb{A}_L$ through a descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent`](../def/M4aHerbrand_IdeleClassVocab.html#L28).
--
--   Finally, for a finite set $S_K$ of finite places of $K$, `semiLocalIntegralOutside` is the set of adeles $x$ of $L$ whose semi-local component [`AutomorphicForm.semiLocalEval K L v`](../def/AutomorphicForm_TwistedOrbital.html#L441) of the finite part lies in [`AutomorphicForm.semiLocalIntegers K L v`](../def/AutomorphicForm_TwistedOrbital.html#L98) for every $v \notin S_K$, and `IsSemiLocallyFactorizable` asserts pointwise that $F$ equals the indicator of that set times $\bigl(\prod_{w \mid \infty} g_L(w)(x_w)\bigr)\prod_{v \in S_K} F_v\bigl(\mathrm{semiLocalEval}(v, x)\bigr)$, with the archimedean factors $g_L$ evaluated on the completions $L_w$; it is thus a predicate relating $F$ to a presented collection of local factors, not an existence statement.
--
--   **Relation to Mathlib.** Mathlib supplies the adele rings, the additive Haar measures and product measures used here, but has no notion of trace-fibre coordinates, adelic or semi-local trace push-forwards, or semi-local factorisation of a function on the adeles of $L$ relative to a subfield; these, together with the conorm `genuineβ` and the semi-local integrality sets, are the project's own.
--
--   **Where it is used.** These coordinates and push-forwards provide the measure-theoretic bookkeeping for comparing test functions and integrals on the adeles of $L$ with those on the adeles of $K$, alongside the twisted orbital integral vocabulary used in the base-change step for $\mathrm{GL}_2$ automorphic forms in this route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_AdelicTracePushforward.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal TensorProduct

namespace AutomorphicForm.AdelicTracePushforward

section

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable def traceFibre (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (r : AdeleRing (𝓞 K) K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    AdeleRing (𝓞 L) L :=
  M4aHerbrand.Bridge.genuineβ K L r * algebraMap L (AdeleRing (𝓞 L) L) (Module.finrank K L : L)⁻¹ +
    ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) *
      algebraMap L (AdeleRing (𝓞 L) L) (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)

noncomputable def tracePushforward (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (F : AdeleRing (𝓞 L) L → ℂ) (r : AdeleRing (𝓞 K) K) : ℂ :=
  ∫ w, F (traceFibre K L r w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K)

noncomputable def actSubId (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) : AdeleRing (𝓞 L) L :=
  D.act σ x - x

noncomputable def localTraceFibre (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (r : v.adicCompletion K)
    (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) :
    L ⊗[K] v.adicCompletion K :=
  (Module.finrank K L : L)⁻¹ ⊗ₜ[K] r + ∑ i, (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L) ⊗ₜ[K] w i

noncomputable def localTracePushforward (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (f : L ⊗[K] v.adicCompletion K → ℂ) (r : v.adicCompletion K) : ℂ :=
  ∫ w, f (localTraceFibre K L v r w)
    ∂(Measure.pi fun _ =>
      ((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
        (Measure.addHaar : Measure (v.adicCompletion K)))

def semiLocalIntegralOutside (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 L) L) :=
  {x | ∀ v ∉ SK, AutomorphicForm.semiLocalEval K L v x.2 ∈ AutomorphicForm.semiLocalIntegers K L v}

def IsSemiLocallyFactorizable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (F : AdeleRing (𝓞 L) L → ℂ) (SK : Finset (HeightOneSpectrum (𝓞 K))) (gL : (w : InfinitePlace L) → w.Completion → ℂ)
    (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ) : Prop :=
  ∀ x, F x = (semiLocalIntegralOutside K L SK).indicator
    (fun x => (∏ w, gL w (x.1 w)) * ∏ v ∈ SK, Fv v (AutomorphicForm.semiLocalEval K L v x.2)) x

end

end AutomorphicForm.AdelicTracePushforward


