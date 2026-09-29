-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordGlue
-- name    : CerednikDrinfeld_MumfordGlue
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/dd48c8cf-af58-5797-8630-cc03be422369
-- title:
--   Mumford gluing data for the formal upper half-plane
-- statement:
--   Fix a commutative ring $\mathcal O$, an element $\pi\in\mathcal O$, a field $K_0$ that is an $\mathcal O$-algebra, a natural number $r$, an element $g_1\in GL_2(K_0)$ and a subgroup $N\le PGL_2(K_0)$. Write $\mathcal O_n=\mathcal O/(\pi^{n+1})$, let $A=$ `chartERing 𝒪 π r` be the localisation of $\mathcal O[X_0,X_1]/(X_0X_1-\pi)$ away from $(\xi^{r-1}-1)(\eta^{r-1}-1)$, where $\xi,\eta$ are the images of $X_0,X_1$, and let $A_n=A/(\pi^{n+1}A)$. The structure `MumfordGlue` records, as data and axioms: schemes $Z_n$ (in universe $0$) with morphisms $\mathrm{zb}_n\colon Z_n\to\operatorname{Spec}\mathcal O_n$, flat and separated, and transition morphisms $\mathrm{zt}_n\colon Z_n\to Z_{n+1}$ making $Z_n$ the fibre product of $Z_{n+1}$ with $\operatorname{Spec}\mathcal O_n$ over $\operatorname{Spec}\mathcal O_{n+1}$; and for every $h\in GL_2(K_0)$ and every $n$ a morphism $\zeta_{h,n}\colon\operatorname{Spec}A_n\to Z_n$ which is an open immersion, lies over $\operatorname{Spec}\mathcal O$, and is compatible with the transition maps $\operatorname{Spec}A_n\to\operatorname{Spec}A_{n+1}$ and $\mathrm{zt}_n$. Two finiteness/invariance axioms say that for each $n$ some finite set of $h$'s suffices for the images of the $\zeta_{h,n}$ to cover the points of $Z_n$, and that $\zeta_{gh,n}=\zeta_{h,n}$ whenever the class of $g$ lies in $N$.
--
--   The remaining fields express the overlap law in terms of Deligne data. For an $\mathcal O$-algebra $B$ and an $\mathcal O$-algebra map $x\colon A_n\to B$, the relevant data $d$ over $B$ are those whose line at the standard full lattice $M_0$ is spanned by $x(\xi)\otimes e_0+1\otimes e_1$, whose line at $g_1M_0$ is the corresponding image of the span of $1\otimes e_0+x(\eta)\otimes e_1$, and which satisfy `InEdgeChart` for the pair $(g_1M_0,M_0)$, i.e. at every prime of $B$ the edge non-degeneracy conditions $g_1M_0\subseteq M_0$, $\pi M_0\subseteq g_1M_0$ and the two mod-$\mathfrak p$ conditions on vectors of $M_0$ outside $g_1M_0$ and on vectors of $g_1M_0$ not divisible by $\pi$. With $P$, $P'$ related to $d$, $d'$ by `DeligneDatum.IsPullback` along $h^{-1}$, $h'^{-1}$: `ζ_rel` asserts that if $P$ and $P'$ are related by some $g$ whose class lies in $N$ then $\operatorname{Spec}(x)$ followed by $\zeta_{h,n}$ equals $\operatorname{Spec}(x')$ followed by $\zeta_{h',n}$; `ζ_overlap_local` upgrades this to an equivalence when $B$ is local; `ζ_overlap_zar` asserts, for arbitrary $B$, that equality of the two composites yields a finite family $f_i\in B$ generating the unit ideal such that over every localisation $C$ of $B$ away from $f_i$ the base changes of $P$ and $P'$ are related by an element with class in $N$. Finally `ζ_univ` is a universal property: any family $t_h\colon\operatorname{Spec}A_n\to T$ satisfying the compatibility of `ζ_rel` factors uniquely through a morphism $Z_n\to T$, so that $Z_n$ with the family $(\zeta_{h,n})_h$ is the colimit of the chart family in schemes. Thus the structure is a presentation of a formal quotient by $N$ chosen model by model, with flatness, separatedness, the covering property and the overlap equivalences carried as fields rather than derived; no uniqueness of a `MumfordGlue` is asserted here.
--
--   **Relation to Mathlib.** The scheme-theoretic vocabulary is Mathlib's (`Scheme`, `Spec`, `IsPullback`, `Flat`, `IsSeparated`, `IsOpenImmersion`, `IsLocalization.Away`); the chart rings, Deligne data and the gluing structure itself are the project's own, Mathlib having no formal upper half-plane or Mumford-quotient notions.
--
--   **Where it is used.** The structure packages the gluing of edge charts of the formal upper half-plane along a discrete subgroup, the algebraic input to the Čerednik–Drinfeld description of Shimura curves and their reduction at a prime dividing the level, which in turn feeds the analysis of the bad-reduction fibres used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordGlue.lean

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

structure MumfordGlue
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

  ζ_rel : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' P P' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P → DeligneDatum.IsPullback (K := K₀) (π := π) B h'⁻¹ d' P' →
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ ζ h' n

  ζ_overlap_local : ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' P P' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P → DeligneDatum.IsPullback (K := K₀) (π := π) B h'⁻¹ d' P' →
    (Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ ζ h' n ↔
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P')

  ζ_overlap_zar : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' P P' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P → DeligneDatum.IsPullback (K := K₀) (π := π) B h'⁻¹ d' P' →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ ζ h' n →
      ∃ (ι : Type) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : ι) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away (f i) C],
          ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
            DeligneDatum.IsPullback (K := K₀) (π := π) C g⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P)
              ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P')

  ζ_univ : ∀ (n : ℕ) (T : Scheme.{0}) (t : Matrix.GeneralLinearGroup (Fin 2) K₀ → (Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) ⟶ T)),
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
      (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' P P' : DeligneDatum (K := K₀) π B),
      (d.line (stdFullLattice K₀) =
            Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
      (d'.line (stdFullLattice K₀) =
            Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
      DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P → DeligneDatum.IsPullback (K := K₀) (π := π) B h'⁻¹ d' P' →
      (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') →
      Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ t h = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ t h') →
    ∃! u : Z n ⟶ T, ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀, ζ h n ≫ u = t h

end FormalOmega
end CerednikDrinfeld


