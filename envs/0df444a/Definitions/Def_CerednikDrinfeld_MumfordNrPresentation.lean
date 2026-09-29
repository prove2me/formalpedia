-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordNrPresentation
-- name    : CerednikDrinfeld_MumfordNrPresentation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/656de340-d080-5979-aa9b-7f0a9abf6a0a
-- title:
--   Unramified presentations of a twisted Mumford tower
-- statement:
--   The module defines one structure, `NrPresentation`, a predicate-with-data on a chosen model: it records an unramified base change of a twisted Mumford tower together with explicit edge charts. The ambient data are a ring $\mathcal O$ with an element $\pi$, a field $K_0$ that is an $\mathcal O$-algebra, an element $g_1\in GL_2(K_0)$, a subgroup $N\le PGL_2(K_0)$, a Mumford tower $DM$ for these (its schemes written $DM.Z_n$ over $\mathcal O/\pi^{n+1}$, with modular maps $DM.q$), a commutative $\mathcal O$-algebra $O^{\mathrm{nr}}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, schemes $X_n$ over $\operatorname{Spec}(\mathcal O/\pi^{n+1})$ with transition maps $xt_n\colon X_n\to X_{n+1}$ and an action $a$ of a group $G_2$ by automorphisms, projections $pr_1\colon X_n\to DM.Z_n$ and $pr_2\colon X_n\to\operatorname{Spec}$ of the $\mathrm{Fr}^2$-fixed subalgebra (the equaliser of $\mathrm{Fr}\circ\mathrm{Fr}$ and the identity) modulo $\pi^{n+1}$, and a subgroup $E\le G_2$. A term of `NrPresentation` consists of schemes $X'_n$ over $\operatorname{Spec}(O^{\mathrm{nr}}/\pi^{n+1})$, transitions $xt'_n$, a $G_2$-action $a'$ acting over the base, and maps $q^X_n\colon X'_n\to X_n$, subject to: each square $(q^X_n,xb'_n,xb_n)$ is cartesian over $\operatorname{Spec}(O^{\mathrm{nr}}/\pi^{n+1})\to\operatorname{Spec}(\mathcal O/\pi^{n+1})$; each transition square is cartesian over $\operatorname{Spec}(O^{\mathrm{nr}}/\pi^{n+1})\to\operatorname{Spec}(O^{\mathrm{nr}}/\pi^{n+2})$; $q^X$ commutes with transitions and with the two actions; and $a'$ fixes the structure maps. Further fields give, for each $h\in GL_2(K_0)$ and $n$, a map $\kappa'_{h,n}$ from $\operatorname{Spec}$ of the edge chart ring `chartERing` over $O^{\mathrm{nr}}$ (the localisation of $O^{\mathrm{nr}}[\xi,\eta]/(\xi\eta-\pi)$ where $\xi^{r-1}-1$ and $\eta^{r-1}-1$ are units) modulo $\pi^{n+1}$ into $X'_n$, required to satisfy three laws: composed with $q^X_n$ and $pr_1$ it agrees with $DM.q$ evaluated at any Deligne datum $P$ related by `DeligneDatum.IsPullback` at $h^{-1}$ to a datum $d$ whose lines at the standard lattice and at $g_1\cdot$(standard lattice) are the spans prescribed by the images of $\xi$ and $\eta$ and which satisfies `InEdgeChart` for that adjacent pair; composed with $q^X_n$ and $pr_2$ it is the map induced by the inclusion of the $\mathrm{Fr}^2$-fixed subalgebra into $O^{\mathrm{nr}}$ and thence into the chart ring; and composed with $xb'_n$ it is induced by $O^{\mathrm{nr}}\to$ `chartERing`. Finally each $\kappa'_{h,n}$ is an open immersion, the $G_2$-translates of the chart images cover $X'_n$, and two chart images can meet after translation by $g\in G_2$ only if $g\in E$.
--
--   **Relation to Mathlib.** Mathlib has no notion of Mumford or Čerednik–Drinfeld towers; this structure is the project's own, expressed using Mathlib's schemes, `IsPullback` squares of schemes and `IsOpenImmersion`.
--
--   **Where it is used.** The structure is the interface between the construction of the unramified base change of the twisted Mumford tower and the statements about the unramified layer of the descended Čerednik–Drinfeld quotient, which supply the $p$-adic uniformisation of the Shimura curves used on the automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordNrPresentation.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace CerednikDrinfeld
namespace FormalOmega
namespace MumfordTower

structure NrPresentation
    {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G₂ : Type) [Group G₂] (a : ∀ n : ℕ, G₂ →* Aut (X n))
    (pr₁ : ∀ n : ℕ, X n ⟶ DM.Z n) (pr₂ : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (E : Subgroup G₂) : Type 1 where

  X' : ℕ → Scheme.{0}

  xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))

  xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)

  a' : ∀ n : ℕ, G₂ →* Aut (X' n)

  qX : ∀ n : ℕ, X' n ⟶ X n

  hq : ∀ n : ℕ, IsPullback (qX n) (xb' n) (xb n)
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
      (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))

  hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 Onr π) (Nat.le_succ (n + 1)))))))

  hq_xt : ∀ n : ℕ, xt' n ≫ qX (n + 1) = qX n ≫ xt n

  hq_a : ∀ (n : ℕ) (g : G₂), (a' n g).hom ≫ qX n = qX n ≫ (a n g).hom

  ha'_over : ∀ (n : ℕ) (g : G₂), (a' n g).hom ≫ xb' n = xb' n

  κ' : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ X' n

  κ'_pr₁ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
      (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
      (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
      DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
      Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ' h n ≫ qX n ≫ pr₁ n = DM.q n B hB P

  κ'_pr₂ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
      κ' h n ≫ qX n ≫ pr₂ n = Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))

  κ'_xb' : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
      κ' h n ≫ xb' n = Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))

  κ'_isOpenImmersion : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), IsOpenImmersion (κ' h n)

  cover : ∀ (n : ℕ) (x : X' n), ∃ (g : G₂) (h : Matrix.GeneralLinearGroup (Fin 2) K₀), x ∈ Set.range (κ' h n ≫ (a' n g).hom).base

  parity : ∀ (n : ℕ) (g : G₂) (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀),
      (Set.range (κ' h n).base ∩ Set.range (κ' h' n ≫ (a' n g).hom).base).Nonempty → g ∈ E

end MumfordTower
end FormalOmega
end CerednikDrinfeld


