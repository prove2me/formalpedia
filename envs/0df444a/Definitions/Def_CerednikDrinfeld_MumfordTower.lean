-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordTower
-- name    : CerednikDrinfeld_MumfordTower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/56743485-e066-5234-af2e-15225f439520
-- title:
--   Mumford tower: levelwise presentation of a formal quotient of Ω̂
-- statement:
--   Fixed throughout are a commutative ring $\mathcal O$ with an element $\pi$, a field $K_0$ that is an $\mathcal O$-algebra, a natural number $r$, an element $g_1 \in \mathrm{GL}_2(K_0)$ and a subgroup $N \le \mathrm{PGL}_2(K_0)$. Write $\mathcal O_n = \mathcal O/(\pi^{n+1})$, let $A$ be the edge chart ring `chartERing 𝒪 π r`, namely the localisation of $\mathcal O[X_0,X_1]/(X_0X_1-\pi)$ in which $(\xi^{r-1}-1)(\eta^{r-1}-1)$ is inverted, $\xi,\eta$ the images of $X_0,X_1$, and let $A_n = A/(\pi^{n+1})$. `MumfordTower` is a structure, so a `MumfordTower 𝒪 π K₀ r g₁ N` is a package of data together with the properties listed as fields; nothing here asserts that one exists. The data are: schemes $Z_n$ ($n \in \mathbb N$) with morphisms $zb_n : Z_n \to \operatorname{Spec}\mathcal O_n$ and transition morphisms $zt_n : Z_n \to Z_{n+1}$ such that each square formed by $zt_n$, $zb_n$, $zb_{n+1}$ and $\operatorname{Spec}\mathcal O_n \to \operatorname{Spec}\mathcal O_{n+1}$ is a pullback; each $zb_n$ is proper and flat; and every finite subset of $Z_n$ lies in an affine open. Next, for every $\mathcal O$-algebra $B$ with $\pi^{n+1} = 0$ in $B$, a map $q_n : (\mathrm{Omega}\,K_0\,\pi)(B) \to \mathrm{Hom}(\operatorname{Spec} B, Z_n)$, required to lie over the structure morphism $\operatorname{Spec} B \to \operatorname{Spec}\mathcal O$, to be contravariantly natural in $\mathcal O$-algebra maps, to be compatible with $zt_n$ under raising the level, and to be constant on the relation `DeligneDatum.IsPullback B g⁻¹ P P'` for $g$ whose class lies in $N$. The chart clauses concern the datum $d$ over $A_n$ whose line at the standard lattice $M_0$ is spanned by $\bar\xi\otimes e_0 + 1\otimes e_1$, whose line at $g_1M_0$ is the image under base change of the span of $1\otimes e_0 + \bar\eta\otimes e_1$, and which satisfies `InEdgeChart π (g₁M₀) M₀` (at every prime $\mathfrak p$ of $A_n$: $g_1M_0 \subseteq M_0$, $\pi M_0 \subseteq g_1M_0$, and vectors of $M_0$ outside $g_1M_0$, respectively vectors of $g_1M_0$ not divisible by $\pi$ in $M_0$, have their images outside the line plus $\mathfrak p$ times the whole base change). For $h \in \mathrm{GL}_2(K_0)$ and $P$ related to $d$ by the $h^{-1}$ pullback relation, $q_n(P)$ is required to be an open immersion, and such charts are required to cover $Z_n$ set-theoretically. The fibre clauses: over a local $B$, $q_n(P) = q_n(P')$ holds exactly when $P,P'$ are related by some $g$ with class in $N$; over an arbitrary $B$, equality implies that after passing to the localisations $B[1/f_i]$ for some finite family $f_i$ generating the unit ideal, the images of $P$ and $P'$ are so related. Finally a levelwise universal property: any scheme $T$ together with an assignment $\rho$ of morphisms $\operatorname{Spec} B \to T$ to points of $(\mathrm{Omega}\,K_0\,\pi)(B)$ that is natural and invariant under the $N$-relation in the same two senses factors through $q_n$ by a unique $u : Z_n \to T$.
--
--   **Relation to Mathlib.** Schemes, properness, flatness, pullback squares and open immersions are Mathlib's; the functor of points $\mathrm{Omega}\,K_0\,\pi$ on $\mathcal O$-algebras, the Deligne data and their pullback relation, the edge chart ring and the tower structure itself are the project's own notions, Mathlib having no formal $p$-adic upper half plane or Mumford quotient.
--
--   **Where it is used.** The tower axiomatises, level by level, the formal quotient of the $p$-adic upper half plane by a discrete subgroup of $\mathrm{PGL}_2(K_0)$ acting freely, i.e. the Mumford-curve side of the Čerednik–Drinfel'd uniformisation of Shimura curves; it is the presentation on which the project's work with Mumford quotients and the associated component groups and Jacobians rests, used downstream in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordTower.lean

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

structure MumfordTower
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀))) : Type 1 where

  Z : ℕ → Scheme.{0}

  zb : ∀ n : ℕ, Z n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))

  zt : ∀ n : ℕ, Z n ⟶ Z (n + 1)

  zt_isPullback : ∀ n : ℕ, IsPullback (zt n) (zb n) (zb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))

  zb_isProper : ∀ n : ℕ, IsProper (zb n)

  zb_flat : ∀ n : ℕ, Flat (zb n)

  affineNbhd : ∀ (n : ℕ) (S : Set (Z n)), S.Finite → ∃ U : (Z n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Z n))

  q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
    (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ Z n)

  q_over : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (P : (Omega K₀ π).obj B),
    q n B hB P ≫ zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))

  q_natural : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (P : (Omega K₀ π).obj B),
    q n B' hB' ((Omega K₀ π).map φ P) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q n B hB P

  q_zt : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0) (P : (Omega K₀ π).obj B),
    q (n + 1) B hB' P = q n B hB P ≫ zt n

  q_inv : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk g ∈ N →
    ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → q n B hB P' = q n B hB P

  chart_isOpenImmersion : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
    (hA : (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) π) ^ (n + 1) = 0)
    (d P : DeligneDatum (K := K₀) π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})),
    (d.line (stdFullLattice K₀) =
            Submodule.span ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) {((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) {(1 : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h⁻¹ d P →
    IsOpenImmersion (q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P)

  cover : ∀ (n : ℕ) (hA : (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) π) ^ (n + 1) = 0) (z : Z n),
    ∃ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d P : DeligneDatum (K := K₀) π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})),
    (d.line (stdFullLattice K₀) =
            Submodule.span ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) {((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) {(1 : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) ∧
    DeligneDatum.IsPullback (K := K₀) (π := π) ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h⁻¹ d P ∧ z ∈ Set.range (q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P).base

  q_localFib : ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (P P' : (Omega K₀ π).obj B),
    q n B hB P = q n B hB P' ↔
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P'

  q_zarFib : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (P P' : (Omega K₀ π).obj B), q n B hB P = q n B hB P' →
      ∃ (ι : Type) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : ι) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away (f i) C],
          ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
            DeligneDatum.IsPullback (K := K₀) (π := π) C g⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P)
              ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P')

  univ_lvl : ∀ (n : ℕ) (T : Scheme.{0})
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
      (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ T)),
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (P : (Omega K₀ π).obj B),
      ρ B' hB' ((Omega K₀ π).map φ P) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ρ B hB P) →
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk g ∈ N →
      ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → ρ B hB P' = ρ B hB P) →
    ∃! u : Z n ⟶ T, ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (P : (Omega K₀ π).obj B),
      q n B hB P ≫ u = ρ B hB P

end FormalOmega
end CerednikDrinfeld


