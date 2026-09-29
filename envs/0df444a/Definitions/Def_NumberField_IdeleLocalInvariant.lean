-- Prove2me | Definitions.Def_NumberField_IdeleLocalInvariant
-- name    : NumberField_IdeleLocalInvariant
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c448c9f2-19d2-5211-98d7-7a0328e3dfdb
-- title:
--   Local invariant of a degree-two idèle cohomology class
-- statement:
--   Throughout, $E \subseteq K$ is a Galois extension of number fields, $D$ is an idèle Galois descent datum for $\mathcal{O}_K$, $E$, $K$ (it supplies for each $g \in \mathrm{Gal}(K/E)$ a multiplicative automorphism `D.unitsAct g` of the idèle group $(\mathbb{A}_K)^\times$), and the ambient multiplicative-distributive action of $\mathrm{Gal}(K/E)$ on $(\mathbb{A}_K)^\times$ is assumed to be given by $D$. The predicate `HasLocalInv` takes a class $x$ in degree-two group cohomology of $\mathrm{Gal}(K/E)$ acting on $(\mathbb{A}_K)^\times$ (viewed additively as a $\mathbb{Z}$-linear representation), a finite place $v$ of $E$, and an element $t$ of $\mathbb{Q}/\mathbb{Z}$, written as `AddCircle (1 : ℚ)`. It asserts the existence of a complete reading of the local invariant of $x$ at $v$ equal to $t$: namely of a family of representation morphisms $\mathrm{pr}_w$ from the restriction of the idèle representation to the decomposition subgroup $D_w$ (the stabiliser of the valuation subring of $w$ in $\mathrm{Gal}(K/E)$) to $(K_w)^\times$, each given on elements by the $w$-component `finPart w` of an idèle; of a place $w$ of $K$ with $w \cap \mathcal{O}_E = v$; of a residue characteristic $q$ together with a finite extension $L'$ of $\mathbb{Q}_q$ inside $\overline{\mathbb{Q}}_q$ carrying a faithful $D_w$-action by ring automorphisms fixing $\mathbb{Q}_q$, a $D_w$-equivariant ring isomorphism $\Phi \colon K_w \cong L'$, a finite base field $K_0$ which by `IsBase` satisfies $K_0 \le L'$ and consists exactly of the $D_w$-fixed elements of $L'$, and a morphism $\theta$ of $D_w$-representations from $(L')^\times$ to $(K_w)^\times$ acting as $\Phi^{-1}$; of a class $u' \in H^2(D_w, (L')^\times)$ satisfying the predicate `IsLocalFundamentalClass` for the data $q, L', D_w, K_0$; and finally of an integer $n$ with $$\mathrm{res}_{D_w}(\mathrm{pr}_w)_*\,x = n \cdot \theta_* u' \quad\text{and}\quad t = \frac{n}{|D_w|} \bmod 1 .$$ Thus the invariant is recorded as a property of a pair $(v,t)$, existentially quantified over all the local data used to read it, rather than as the value of a constructed map $\mathrm{inv}_v$.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients used (group cohomology of representations, `Rep.ofMulDistribMulAction`, adèle rings and adic completions, decomposition subgroups of valuation subrings), but has no local invariant map or local fundamental class of class field theory; `HasLocalInv` is the project's own predicate, and the local fundamental class enters only through the predicate [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](../def/ExtCitation_LocalLevel_FundamentalClass.html#L60).
--
--   **Where it is used.** This is the vocabulary in which the local invariants $\mathrm{inv}_v$ of degree-two idèle cohomology classes are recorded, normalised so that the local fundamental class of $K_w/E_v$ has invariant $1/[K_w:E_v]$. It is the interface through which Shapiro's lemma and the reciprocity law (vanishing of the sum of local invariants) are stated in the cohomological class-field-theory input to the class-group computations used in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_IdeleLocalInvariant.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

namespace NumberField.IdeleLocalInv

def HasLocalInv (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (_hactI : ∀ (g : K ≃ₐ[E] K) (y : (AdeleRing (𝓞 K) K)ˣ), g • y = D.unitsAct g y)
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ)) : Prop :=
  ∃
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))

    (w : HeightOneSpectrum (𝓞 K)) (_ : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)

    (q : ℕ) (_ : Fact q.Prime) (_ : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L')
    (_ : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L') (_ : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) L')
    (_ : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ)
    (Φ : w.adicCompletion K ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K₀)
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E K w)) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L'))

    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E K w)) K₀ u')
    (n : ℤ),
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom x =
        n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u' ∧
      t = (((n : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w) : ℚ) : ℚ) : AddCircle (1 : ℚ))

end NumberField.IdeleLocalInv


