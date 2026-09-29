-- Prove2me | Definitions.Def_CerednikDrinfeld_EquivariantUniformization
-- name    : CerednikDrinfeld_EquivariantUniformization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/08b0aaea-eda1-5254-abe6-b78d8637189c
-- title:
--   Equivariant Mumford uniformisation of a period datum
-- statement:
--   This module defines the structure [`CerednikDrinfeld.Mumford.EquivariantUniformization`](../def/CerednikDrinfeld_EquivariantUniformization.html#L15), parametrised by a prime $r$, a degeneracy datum $D$ on a finite edge set $E$ and a vertex set $V$ (maps $a,b\colon E\to V$ and widths $w\colon E\to\mathbb{N}^{+}$), a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $r$ a nonunit of $A$ (`LiesOverPrime`), an abelian group $T$, a group $S$, and three homomorphisms out of $S$: a scalar part $\mathrm{scalar}\colon S\to D_A$ into the decomposition group of $A$ over $\mathbb{Q}$, an action $\mathrm{actZ}$ of $S$ by $\mathbb{Z}$-linear automorphisms of the ribbon kernel $Z=\mathrm{ribbonKernel}\,D=\ker(\mathrm{pushforward}\,D.a)\cap\ker(\mathrm{pushforward}\,D.b)\subseteq(E\to\mathbb{Z})$, and an action $\mathrm{gal}$ of $S$ on $T$ by additive automorphisms. An instance of the structure consists of: an intermediate field $K$ of $\mathbb{Q}$ inside the completion $C_A$ of $A$'s valuation; an additive map $\mathrm{ord}\colon \mathrm{Additive}\,K^{\times}\to\mathbb{Z}$ with $v(k)=v(r)^{\mathrm{ord}(k)}$ for all $k\in K^{\times}$; the condition that every $\sigma\in D_A$ lying in the inertia subgroup fixes $K$ pointwise, read through any $\mathbb{Q}$-algebra automorphism $s$ of $C_A$ inducing the action of $\sigma$; a Henselian $n$-th root condition, namely that for $n>0$ with $r\nmid n$ every $k\in K^{\times}$ with $\mathrm{ord}(k)=0$ is an $n$-th power in $K^{\times}$; a period datum $P$ over $D$ with values in $K$, i.e. a symmetric $\mathbb{Z}$-bilinear $Q\colon Z\times Z\to \mathrm{Additive}\,K^{\times}$ with $\mathrm{ord}\,Q(x,y)=\sum_{e}w(e)x_ey_e$; and a surjective additive map $\mathrm{eFull}$ from the full torus points $\mathrm{Hom}_{\mathbb{Z}}(Z,\mathrm{Additive}\,C_A^{\times})$ onto $T$ whose kernel is exactly the period lattice, the image of $Q$ after base change to $C_A$.
--
--   Two equivariance fields carry the symmetry. For $\sigma\in S$ and any $\mathbb{Q}$-algebra automorphism $s$ of $C_A$ realising the action of $\mathrm{scalar}(\sigma)$: first $s(Q(x,y))=Q(\mathrm{actZ}(\sigma)x,\mathrm{actZ}(\sigma)y)$ in $C_A$, and second $\mathrm{eFull}\bigl(s\circ u\circ \mathrm{actZ}(\sigma)^{-1}\bigr)=\mathrm{gal}(\sigma)\,\mathrm{eFull}(u)$, where the postcomposition with $s$ on coefficients is `coeffMap` and the precomposition with $\mathrm{actZ}(\sigma)^{-1}$ is `precomp`. Thus the structure asserts an $S$-equivariant presentation of $T$ as the quotient of the full character torus points by the period lattice, rather than the torsion-level, Hecke-compatible statement recorded by `PeriodUniformization` in the companion module; no compatibility with Hecke correspondences is imposed here.
--
--   **Relation to Mathlib.** Mathlib has no notion of Mumford period data or their uniformisations; the degeneracy data, ribbon kernel, period datum and this equivariant uniformisation structure are the project's own, built on Mathlib's valuation subrings, decomposition and inertia subgroups, and valuation completions.
--
--   **Where it is used.** The structure packages the $r$-adic (Čerednik–Drinfel'd/Mumford) uniformisation input used in the level-lowering half of the argument: the period datum records the monodromy pairing of a degenerating curve at $r$, and the equivariance fields transport the action of a chosen symmetry group — inertia, a Frobenius element, or a geometric automorphism of the degeneration — to the group $T$ uniformised by the torus points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_EquivariantUniformization.lean

import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld
namespace Mumford

open ModularCurve

variable {E V : Type} [Fintype E] [DecidableEq V]

structure EquivariantUniformization (r : ℕ) [Fact r.Prime] (D : DegeneracyData E V)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (T : Type) [AddCommGroup T]
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))) (gal : S →* AddAut T) : Type 1 where

  K : IntermediateField ℚ A.valuation.Completion

  ord : Additive (↥K)ˣ →+ ℤ

  ord_spec : ∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
    Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k))

  inertia_K : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion)

  hensel_K : ∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k

  P : PeriodDatum D (↥K) A.valuation.Completion ord

  eFull : P.TorusPoints →+ T

  eFull_surjective : Function.Surjective eFull

  eFull_ker : ∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice

  Q_equiv : ∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ x y : ↥(ribbonKernel D),
      s (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) =
        (((Additive.toMul (P.Q (actZ σ x) (actZ σ y)) : (↥K)ˣ) : ↥K) : A.valuation.Completion)

  eFull_equiv : ∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ u : P.TorusPoints,
      eFull (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
        (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) :
          ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u)) = gal σ (eFull u)

end Mumford
end CerednikDrinfeld

end


