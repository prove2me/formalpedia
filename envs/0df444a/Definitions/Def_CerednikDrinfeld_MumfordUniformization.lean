-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordUniformization
-- name    : CerednikDrinfeld_MumfordUniformization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/72e8f1d7-aae3-5108-8d74-97afe8576316
-- title:
--   Mumford period uniformisation of a Hecke–Galois torsion module
-- statement:
--   Two helper operations on the torus points of a Mumford period datum are defined first. For a period datum $P$ over a degeneracy datum $D$ with period field $K$ inside a field $L$, the torus points are $\mathrm{Hom}_{\mathbb Z}(Z, L^{\times})$ with $Z =$ `ribbonKernel D` written additively; `coeffMap` post-composes a homomorphism $u$ with the map induced on units by a ring endomorphism $s$ of $L$, and `precomp` pre-composes $u$ with a $\mathbb Z$-linear endomorphism $f$ of $Z$; both are $\mathbb Z$-linear in $u$, with the evident pointwise formulas.
--
--   The structure `PeriodUniformization` packages, for a prime $r$, a degeneracy datum $D$ on a finite edge set $E$ and vertex set $V$ with Hecke data $H$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $r$ in its nonunits, an abelian group $T$ carrying a ring map from $\mathrm{HeckeAlg}=\mathbb Z[X_\ell:\ell\ \text{prime}]$ to $\mathrm{End}_{\mathbb Z}T$ and a homomorphism $\mathrm{gal}$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to additive automorphisms of $T$, the following data: an intermediate field $K$ of $\mathbb Q$ in the completion $C$ of $A$'s valuation; a homomorphism $\mathrm{ord}:K^{\times}\to\mathbb Z$ with $v(k)=v(r)^{\mathrm{ord}(k)}$; the requirement that $K$ be fixed pointwise by every $\mathbb Q$-algebra automorphism $s$ of $C$ implementing the action of a decomposition-group element lying in the inertia subgroup; $n$-th roots in $K^{\times}$ for all units of $\mathrm{ord}$ zero and all $n>0$ prime to $r$; a period datum $P$ over $D$ with values in $K^{\times}$ and torus points in $C^{\times}$, i.e. a symmetric bilinear $Q$ on $Z$ with $\mathrm{ord}\,Q(x,y)=\sum_e w(e)x_ey_e$, for which each kernel Hecke map admits a $Q$-adjoint and all values $Q(x,y)$ are fixed by the decomposition group; and a homomorphism $e$ from $U=\{u:\ nu\in Q(Z)\ \text{for some}\ n\neq 0\}$ to $T$ hitting every element of finite order, taking values of finite order, with kernel exactly the period lattice $Q(Z)$, and intertwining, whenever the transformed element again lies in $U$, pre-composition with $T_\ell|_Z$ with the action of $X_\ell$, coefficientwise action of inertia with $\mathrm{gal}$, and the composite of coefficientwise $\varphi$ followed by $T_r|_Z$ with $\mathrm{gal}(\varphi)$ for every $\varphi$ that is Frobenius at $A$ for $r$ (acts as $x\mapsto x^r$ on the residue field).
--
--   **Relation to Mathlib.** Mathlib has no notion of Mumford period uniformisation; the structure is the project's own. It is stated in terms of Mathlib's `ValuationSubring`, the completion of its valuation, and its decomposition and inertia subgroups, with unit groups regarded as $\mathbb Z$-modules via `Additive`.
--
--   **Where it is used.** The structure is the hypothesis package at the prime $r$ from which toric uniformisation presentations of the torsion of a Shimura-curve Jacobian are obtained at each auxiliary prime, by Kummer theory on the torus together with the root-extraction and inertia-invariance clauses on $K$. Its existence for $T$ the torsion of the Jacobian is what the Čerednik–Drinfeld description of the curve at a prime of the discriminant, combined with Mumford's uniformisation, supplies; it feeds the level-lowering step of the Frey–Serre–Ribet argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordUniformization.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
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

namespace PeriodDatum

variable {D : DegeneracyData E V} {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}

def coeffMap (P : PeriodDatum D K L ord) (s : L →+* L) : P.TorusPoints →ₗ[ℤ] P.TorusPoints :=
  LinearMap.llcomp ℤ ↥(ribbonKernel D) (Additive Lˣ) (Additive Lˣ)
    (MonoidHom.toAdditive (Units.map (s : L →* L))).toIntLinearMap

@[simp] theorem coeffMap_apply (P : PeriodDatum D K L ord) (s : L →+* L) (u : P.TorusPoints)
    (z : ↥(ribbonKernel D)) :
    P.coeffMap s u z = Additive.ofMul (Units.map (s : L →* L) (Additive.toMul (u z))) := rfl

def precomp (P : PeriodDatum D K L ord) (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) :
    P.TorusPoints →ₗ[ℤ] P.TorusPoints :=
  LinearMap.lcomp ℤ (Additive Lˣ) f

@[simp] theorem precomp_apply (P : PeriodDatum D K L ord) (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D))
    (u : P.TorusPoints) (z : ↥(ribbonKernel D)) : P.precomp f u z = u (f z) := rfl

end PeriodDatum

structure PeriodUniformization [Fintype V] (r : ℕ) [Fact r.Prime] (D : DegeneracyData E V) (H : HeckeData D)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (T : Type) [AddCommGroup T] (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T) : Type 1 where

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

  heckeAdj : P.HeckeAdjointable H

  decomp_Q : ∀ (σ : ↥(A.decompositionSubgroup ℚ)) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = σ • c) → ∀ x y : ↥(ribbonKernel D),
      s (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) =
        (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion)

  e : ↥P.U →+ T

  e_surj_torsion : ∀ t : T, IsOfFinAddOrder t → t ∈ e.range

  e_torsion : ∀ u : ↥P.U, IsOfFinAddOrder (e u)

  e_ker : ∀ u : ↥P.U, e u = 0 ↔ (u : P.TorusPoints) ∈ P.periodLattice

  e_hecke : ∀ (ℓ : Nat.Primes) (u : ↥P.U) (hu : P.precomp (heckeKernelMap H ℓ) (u : P.TorusPoints) ∈ P.U),
    e ⟨P.precomp (heckeKernelMap H ℓ) (u : P.TorusPoints), hu⟩ = hecke (heckeGen ℓ) (e u)

  e_inertia : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ (u : ↥P.U) (hu : P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : P.TorusPoints) ∈ P.U),
        e ⟨P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : P.TorusPoints), hu⟩ =
          gal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (e u)

  e_frob : ∀ φ : ↥(A.decompositionSubgroup ℚ),
    A.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) r →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = φ • c) →
      ∀ (u : ↥P.U) (hu : P.precomp (heckeKernelMap H ⟨r, Fact.out⟩)
          (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : P.TorusPoints)) ∈ P.U),
        e ⟨P.precomp (heckeKernelMap H ⟨r, Fact.out⟩)
            (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : P.TorusPoints)), hu⟩ =
          gal (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (e u)

end Mumford
end CerednikDrinfeld

end


