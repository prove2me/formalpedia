-- Prove2me | Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
-- name    : TwistedUnipotentTerm_SemiLocalOrbitalVocab
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/a385f2b3-358a-5fc0-9aaa-f1adf4e15f2b
-- title:
--   Semi-local unipotent orbital integrals and twisted local factors
-- statement:
--   Throughout, $L/K$ is an extension of number fields, $v$ a nonzero prime of $\mathcal O_K$, and $A_v = L\otimes_K K_v$ the semi-local algebra above $v$; $w$ ranges over the type `v.Extension (𝓞 L)` of extensions of $v$ to $\mathcal O_L$, with associated completion $L_w$. Four elementary constructions come first: `semiLocalUnipotent` is the unit of $\mathrm{GL}_2(A_v)$ with value $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and inverse $\begin{pmatrix}1&-x\\0&1\end{pmatrix}$; `semiLocalCentral` sends $\zeta \in A_v^{\times}$ to the scalar unit $\mathrm{diag}(\zeta,\zeta)$, the image of $\zeta$ under `Matrix.scalar (Fin 2)`; `semiLocalUnitComponent` transports $\zeta$ along the base-change isomorphism `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v` identifying $A_v$ with $\prod_{w} L_w$ and evaluates at a chosen $w$, yielding a unit of $L_w$; and `semiLocalCharacter`, for a homomorphism $\xi_L$ from the full subgroup $\top$ of $(\mathbb A_L)^{\times}$ to $\mathbb C^{\times}$, is the finitely-supported product over all $w \mid v$ of $\xi_L$ evaluated at the determinant of [`NumberField.AdelicLevel.heckeGenAt (𝓞 L) L w.1`](../def/NumberField_AdelicLevel.html#L708) applied to the $w$-component of $\zeta$ (membership in $\top$ being automatic). Next, `wordIndicator`, given $m$ elements $r_1,\dots,r_m$ and an element $z$ of $\mathrm{GL}_2(L_w)$ and numbers $k,j$, is the sum over all $\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,m$ of the $\{0,1\}$-valued indicator of [`AutomorphicForm.semiLocalIntegralSet K L v`](../def/AutomorphicForm_TwistedOrbital.html#L136) evaluated at $\iota_w(r_{\iota(0)}\cdots r_{\iota(k-1)}z^{j})^{-1}x$, where the ordered word is placed at $w$ inside $\mathrm{GL}_2$ of the finite adeles of $L$ by [`AdelicDock.localEmbed`](../def/AdelicDock_LocalEmbedding.html#L97) and its semi-local component at $v$ is read off by [`AutomorphicForm.semiLocalComponent`](../def/AutomorphicForm_TwistedOrbital.html#L446). Then `unipotentOrbitalFn` sends $x \in A_v$ to $\int_{A_v^{\times}} \xi_v(\zeta)\big(\int_{\mathcal K} \mathbf 1_{k,j}(\kappa^{-1}\,\mathrm{diag}(\zeta,\zeta)\,n(x))\,d\kappa\big)d\zeta$, the inner integral over [`AutomorphicForm.semiLocalIntegralSet`](../def/AutomorphicForm_TwistedOrbital.html#L136) against [`AutomorphicForm.semiLocalHaar`](../def/AutomorphicForm_TwistedOrbital.html#L169) and the outer one against Haar measure on $A_v^{\times}$.
--
--   Two further definitions sit outside the namespace. [`twistedLocalFactor`](../def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L85) is the function on $K_v$ obtained by applying [`AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v`](../def/AutomorphicForm_AdelicTracePushforward.html#L38) to [`TwistedUnipotentTerm.unipotentOrbitalFn`](../def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L57): explicitly, $r \mapsto \int \Phi\big((\,[L:K]\,)^{-1}\otimes r + \sum_i e_i \otimes w_i\big)$, the integral over tuples $(w_i)$ indexed by a basis $(e_i)$ of $\ker(\mathrm{Tr}_{L/K})$ against the product of the additive Haar measure on $K_v$ normalised to give $\mathcal O_v$ measure $1$; besides the data above it takes an idele-theoretic Galois descent datum [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](../def/M4aHerbrand_IdeleClassVocab.html#L28) and a $K$-automorphism $\sigma$ of $L$ as arguments, which index the definition without entering the value. Finally, [`IsJointFactorizableStandardOutside`](../def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L97) is the predicate on a function $f$ on the adeles of a number field $F$, a finite set $S$ of finite places, a function $g$ on the infinite adele ring and a family $h_v$ on the completions $F_v$, asserting that for every adele $x$, $f(x)$ equals the value at $x$ of the indicator of [`NumberField.TateGlobal.integralOutside S`](../def/NumberField_TateGlobalZeta.html#L64) applied to $x \mapsto g(x_\infty)\prod_{v\in S} h_v(x_v)$. It differs from [`NumberField.TateGlobal.IsFactorizableStandardOutside`](../def/NumberField_TateGlobalZeta.html#L67) in treating the archimedean part as a single function on the infinite adeles rather than as a product over the infinite places.
--
--   **Relation to Mathlib.** Mathlib has no semi-local orbital integrals, word indicators or factorizability predicates of this kind; these are the project's own, built on Mathlib's adele rings, adic completions, general linear groups and Haar measure. [`IsJointFactorizableStandardOutside`](../def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L97) is a variant of the project's [`NumberField.TateGlobal.IsFactorizableStandardOutside`](../def/NumberField_TateGlobalZeta.html#L67).
--
--   **Where it is used.** These are the local ingredients of the unipotent contributions to a twisted trace formula for $\mathrm{GL}_2$ over an extension $L/K$ with a central character of the ideles of $L$: the orbital function at $v$, its push-forward along the trace map to a function on $K_v$, and the shape condition under which a global test function is a product of such local factors and standard outside a finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab.lean

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace TwistedUnipotentTerm

section Definitions

noncomputable def semiLocalUnipotent
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : L ⊗[K] v.adicCompletion K) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

noncomputable def semiLocalCentral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  Units.map (Matrix.scalar (Fin 2) : L ⊗[K] v.adicCompletion K →+* Matrix (Fin 2) (Fin 2) _).toMonoidHom ζ

noncomputable def semiLocalUnitComponent (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (ζ : (L ⊗[K] v.adicCompletion K)ˣ) : (w.1.adicCompletion L)ˣ :=
  Units.map (Pi.evalMonoidHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w)
    (Units.mapEquiv (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv.toMulEquiv ζ)

noncomputable def semiLocalCharacter (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ζ : (L ⊗[K] v.adicCompletion K)ˣ) : ℂ :=
  ∏ᶠ w : v.Extension (𝓞 L),
    ((ξL ⟨Matrix.GeneralLinearGroup.det
        (NumberField.AdelicLevel.heckeGenAt (𝓞 L) L w.1 (semiLocalUnitComponent K L v w ζ)),
      Subgroup.mem_top _⟩ : ℂˣ) : ℂ)

noncomputable def wordIndicator (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (m : ℕ)
    (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ)
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : ℂ :=
  ∑ ι : Fin k → Fin m,
    (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
      ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
        ((List.ofFn fun i => rT (ι i)).prod * z ^ j)))⁻¹ * x)

open scoped TensorProduct.RightActions in

noncomputable def unipotentOrbitalFn (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L)) (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L))
    (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ) (x : L ⊗[K] v.adicCompletion K) : ℂ :=
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI : LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  letI : MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ := borel _
  haveI : BorelSpace (L ⊗[K] v.adicCompletion K)ˣ := ⟨rfl⟩
  ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
    semiLocalCharacter K L ξL v ζ *
      ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
        wordIndicator K L v w m rT z k j (κ⁻¹ * semiLocalCentral K L v ζ * semiLocalUnipotent K L v x)
          ∂(AutomorphicForm.semiLocalHaar K L v)
    ∂(Measure.haar : Measure (L ⊗[K] v.adicCompletion K)ˣ)

end Definitions

end TwistedUnipotentTerm

section RootDefinitions

open AutomorphicForm in

noncomputable def twistedLocalFactor
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ) :
    v.adicCompletion K → ℂ :=
  have _ := D
  have _ := σ
  letI : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  AdelicTracePushforward.localTracePushforward K L v (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j)

def IsJointFactorizableStandardOutside {F : Type} [Field F] [NumberField F] (f : AdeleRing (𝓞 F) F → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (g : InfiniteAdeleRing F → ℂ)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) : Prop :=
  ∀ x, f x = (NumberField.TateGlobal.integralOutside S).indicator
    (fun x => g x.1 * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x

end RootDefinitions

end


