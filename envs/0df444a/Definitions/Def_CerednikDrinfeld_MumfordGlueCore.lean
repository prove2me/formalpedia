-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordGlueCore
-- name    : CerednikDrinfeld_MumfordGlueCore
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/59c30d0c-c10e-54fd-93a3-733d9e4df953
-- title:
--   Mumford gluing core for formal upper half-plane charts
-- statement:
--   Throughout, $\mathcal O$ is a commutative ring, $\pi\in\mathcal O$, $K_0$ a field that is an $\mathcal O$-algebra, $r$ a natural number, $g_1\in GL_2(K_0)$ and $N$ a subgroup of $\mathrm{PGL}(2,K_0)$. Write $\mathcal O_n=\mathcal O/(\pi^{n+1})$, $A_n=(\mathtt{chartERing}\ \mathcal O\ \pi\ r)/(\pi^{n+1})$ — the localisation of $\mathcal O[X_0,X_1]/(X_0X_1-\pi)$ away from $(\xi^{r-1}-1)(\eta^{r-1}-1)$, with $\xi,\eta$ the images of $X_0,X_1$, truncated — and $V_n=(\mathtt{chartVRing}\ \mathcal O\ r)/(\pi^{n+1})$, the analogous truncation of $\mathrm{Localization.Away}(X^r-X)$ over $\mathcal O[X]$, with $\zeta$ the image of $X$. The structure `MumfordGlueCore` bundles, first, a tower: schemes $Z_n$ with flat separated morphisms $zb_n:Z_n\to\operatorname{Spec}\mathcal O_n$ and transitions $zt_n:Z_n\to Z_{n+1}$ whose square over $\operatorname{Spec}\mathcal O_n\to\operatorname{Spec}\mathcal O_{n+1}$ is cartesian; and charts $\zeta_{h,n}:\operatorname{Spec}A_n\to Z_n$ for every $h\in GL_2(K_0)$, which are open immersions of $\mathcal O$-schemes, compatible with both towers, such that finitely many of them cover $Z_n$ and $\zeta_{gh,n}=\zeta_{h,n}$ whenever the class of $g$ lies in $N$. Secondly, the data the gluing is made of: $\mathcal O$-algebra maps $\iota_n:A_n\to V_n$ with $\iota_n(\xi)=\zeta$ and $\iota_n(\eta)\zeta=\pi$, exhibiting $V_n$ as the localisation of $A_n$ away from $\xi$; and families of $\mathcal O$-algebra automorphisms $\tau_{g,n}$ of $V_n$ and $\alpha_{g,n}$ of $A_n$ indexed by all $g\in GL_2(K_0)$, whose characterising fields are imposed only for $g$ fixing `stdVertex`, respectively stabilising setwise the pair $\{\mathtt{stdVertex},g_1\cdot\mathtt{stdVertex}\}$: for such $g$, any $\mathcal O$-algebra $B$ and Deligne data $d,d'$ over $B$ whose lines on the standard lattice and its $g_1$-translate are the explicit spans attached to a chart point $y$ (resp. to $y\circ\tau_{g,n}$, resp. $\bar x\circ\alpha_{g,n}$) and which lie in the edge chart `InEdgeChart` for that pair of lattices, are related by `DeligneDatum.IsPullback` with parameter $g^{-1}$. Thirdly, the relations: $\zeta_{hg,n}=\operatorname{Spec}(\alpha_{g,n})$ followed by $\zeta_{h,n}$ for $g$ stabilising the standard edge; the same for $\tau_{g,n}$ after restriction along $\iota_n$ when $g$ fixes `stdVertex`; an overlap bound stating that, when no $N$-translate of $h e_0$ is $h'e_0$, the preimage under $\zeta_{h',n}$ of the open image of $\zeta_{h,n}$ lies in the join of the basic opens of $\xi$ and of $\eta$, each piece being present only under the corresponding incidence of an end of $h'e_0$ with an end of some $N$-translate of $he_0$ (a supremum indexed by that existential, hence $\bot$ when it fails). Finally, the field `desc` carries the chart-level universal property: a family $t_h:\operatorname{Spec}A_n\to T$ that is $N$-invariant and satisfies the same $\alpha$- and $\tau$-equivariances factors uniquely through the charts as a morphism $Z_n\to T$.
--
--   **Relation to Mathlib.** Mathlib has no notion of Mumford gluing data, Deligne data or Bruhat–Tits chart rings; the structure is the project's own. Its scheme-theoretic fields are phrased with Mathlib's `Flat`, `IsSeparated`, `IsOpenImmersion`, `CategoryTheory.IsPullback`, `Spec`/`Spec.map`, `PrimeSpectrum.basicOpen` and `IsLocalization.Away`.
--
--   **Where it is used.** The charts $\operatorname{Spec}A_n$ and $\operatorname{Spec}V_n$ are the edge and vertex charts of the formal model of Drinfeld's upper half-plane over $\mathcal O$; a gluing core packages the level-$n$ scheme together with the Deligne-datum dictionary and the descent property from which the gluing laws and the quotient by the discrete group $N$ are obtained. This is part of the Čerednik–Drinfeld uniformisation of Shimura curves used on the Shimura-curve side of the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordGlueCore.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure MumfordGlueCore
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀))) : Type 1 where

  Z : ℕ → Scheme.{0}

  zb : ∀ n : ℕ, Z n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))

  zt : ∀ n : ℕ, Z n ⟶ Z (n + 1)

  zt_isPullback : ∀ n : ℕ, IsPullback (zt n) (zb n) (zb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))

  zb_flat : ∀ n : ℕ, Flat (zb n)

  zb_isSeparated : ∀ n : ℕ, IsSeparated (zb n)

  ζ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) ⟶ Z n

  ζ_over : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    ζ h n ≫ zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))))

  ζ_zt : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    ζ h n ≫ zt n = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))) ≫ ζ h (n + 1)

  ζ_isOpenImmersion : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), IsOpenImmersion (ζ h n)

  ζ_cover : ∀ n : ℕ, ∃ S : Finset (Matrix.GeneralLinearGroup (Fin 2) K₀), ∀ z : Z n, ∃ h ∈ S, z ∈ Set.range (ζ h n).base

  ζ_inv : ∀ (g h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Matrix.ProjGenLinGroup.mk g ∈ N → ζ (g * h) n = ζ h n

  ι : ∀ n : ℕ, ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)})

  ι_ξ : ∀ n : ℕ, ι n (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) = Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)

  ι_η : ∀ n : ℕ, ι n (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)) * Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r) =
    algebraMap 𝒪 (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) π

  ι_isLocalization : ∀ n : ℕ, @IsLocalization.Away ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) _ (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) _ (ι n).toRingHom.toAlgebra

  τ : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) ≃ₐ[𝒪] (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)})

  τ_spec : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) → ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (y : (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
              (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((y.comp (τ g n).toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {((y.comp (τ g n).toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
              (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d'

  α : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ≃ₐ[𝒪] ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))

  α_spec : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀),
    (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) →
    ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (xq : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {(((xq.comp (α g n).toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (((xq.comp (α g n).toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d'

  ζ_edge : ∀ (h g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) →
    ζ (h * g) n = Spec.map (CommRingCat.ofHom (α g n).toAlgHom.toRingHom) ≫ ζ h n

  ζ_vertex : ∀ (h g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) →
    Spec.map (CommRingCat.ofHom (ι n).toRingHom) ≫ ζ (h * g) n =
      Spec.map (CommRingCat.ofHom (τ g n).toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom (ι n).toRingHom) ≫ ζ h n

  ζ_preimage_le : ∀ (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
    (∀ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N →
      ¬ ((Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
         (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀)))) →
    (ζ h' n) ⁻¹ᵁ (@Scheme.Hom.opensRange _ _ (ζ h n) (ζ_isOpenImmersion h n)) ≤
      (⨆ (_ : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
          (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))),
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.ξ 𝒪 π r))) ⊔
      (⨆ (_ : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
          (Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))),
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.η 𝒪 π r)))

  desc : ∀ (n : ℕ) (T : Scheme.{0}) (t : Matrix.GeneralLinearGroup (Fin 2) K₀ → (Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) ⟶ T)),
    (∀ g h : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N → t (g * h) = t h) →
    (∀ h g : Matrix.GeneralLinearGroup (Fin 2) K₀,
      (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) →
      t (h * g) = Spec.map (CommRingCat.ofHom (α g n).toAlgHom.toRingHom) ≫ t h) →
    (∀ h g : Matrix.GeneralLinearGroup (Fin 2) K₀, Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) →
      Spec.map (CommRingCat.ofHom (ι n).toRingHom) ≫ t (h * g) =
        Spec.map (CommRingCat.ofHom (τ g n).toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom (ι n).toRingHom) ≫ t h) →
    ∃! u : Z n ⟶ T, ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀, ζ h n ≫ u = t h

end FormalOmega
end CerednikDrinfeld


