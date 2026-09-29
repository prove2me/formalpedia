-- Prove2me | Definitions.Def_FreyPackage_DetCyclotomic
-- name    : FreyPackage_DetCyclotomic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/33ff0cf0-907f-507b-b8af-69cc5d8d9e40
-- title:
--   Determinant of mod-n torsion representation; cyclotomic comparison predicates
-- statement:
--   For a Weierstrass curve `W'` in affine form over a commutative ring $R$, and a tower $R \to S \to K$ with $K$ a field with decidable equality, `galoisRepDet W' n` is the monoid homomorphism $(K \simeq_{\mathrm{alg}[S]} K) \to (\mathbb{Z}/n)^\times$ obtained by composing the project's representation `galoisRep` of the $S$-automorphism group of $K$ on the $n$-torsion of $W'(K)$ with Mathlib's `LinearEquiv.det`; `galoisRepDet_apply` records this pointwise. `GaloisRepDetEqCyclotomic S W' n hn` is a *predicate* (not a proved theorem): given `NeZero n` and a proof `hn` that $K$ contains exactly $n$ $n$-th roots of unity, it asserts that for every $\sigma$ the value of `galoisRepDet` equals $\chi_n(\sigma)$, where $\chi_n$ is Mathlib's `modularCyclotomicCharacter` evaluated at $\sigma$ viewed as a ring equivalence. The only instance proved here is `galoisRepDetEqCyclotomic_two`, the degenerate case $n = 2$, which holds because $(\mathbb{Z}/2)^\times$ is a subsingleton.
--
--   The remaining declarations concern a [`FreyPackage`](../def/FLTPrelim_FreyPackage.html#L17) $P$ with prime exponent $P.p$: `card_rootsOfUnity_algebraicClosure` states that $\overline{\mathbb{Q}}$ has exactly $P.p$ $P.p$-th roots of unity, and a local classical `DecidableEq` instance on $\overline{\mathbb{Q}}$ is supplied. Two further predicates on $P$ are defined, both left unproved here. `MuLineCyclotomicAtP` asserts the existence of a valuation subring $A_0$ of $\overline{\mathbb{Q}}$ lying over the rational prime $P.p$ (in the project's sense `LiesOverPrime`) and of a non-zero $P.p$-torsion point $z$ of the Frey curve over $\overline{\mathbb{Q}}$ such that every $\sigma$ in the project's inertia subgroup `inertiaSubgroupIn` of $A_0$ over $\mathbb{Q}$ satisfies $\sigma \cdot z = \chi_{P.p}(\sigma) z$ and $\sigma \cdot y - y \in \mathbb{Z}/P.p \cdot z$ for all $P.p$-torsion $y$; that is, inertia at $p$ is upper triangular with $\chi_p$ on the line $\langle z\rangle$ and trivial on the quotient. `DetCyclotomicOnInertiaAtP` asserts, for every valuation subring lying over $P.p$ and every element of its inertia subgroup over $\mathbb{Q}$, that `galoisRepDet` of the Frey curve at $P.p$ agrees with $\chi_{P.p}$; this is the restriction to inertia at $p$ only, not the global determinant identity.
--
--   **Relation to Mathlib.** The cyclotomic character `modularCyclotomicCharacter`, the roots-of-unity group and the cardinality input [`IsAlgClosed.card_rootsOfUnity_eq`](../def/ExtCitation_AdmissibleExtension.html#L7), and `LinearEquiv.det` are Mathlib's; the torsion-point representation `galoisRep` and the ramification notions [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16) and [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21) are the project's own, defined in the imported definition modules.
--
--   **Where it is used.** Classically the identity $\det \bar\rho_{E,n} = \chi_n$ comes from the Weil pairing; here it is packaged as a predicate, with only the trivial case $n = 2$ discharged. The at-$p$ forms `MuLineCyclotomicAtP` and `DetCyclotomicOnInertiaAtP` are the curve-side inputs describing the action of inertia at $p$ on the $p$-torsion of the Frey curve, used in the ramification analysis that accompanies level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_DetCyclotomic.lean

import Definitions.Def_FreyPackage_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.LinearAlgebra.Determinant
import Definitions.Def_ExtCitation_AdmissibleExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

noncomputable def galoisRepDet (W' : Affine R) (n : ℕ) : (K ≃ₐ[S] K) →* (ZMod n)ˣ :=
  LinearEquiv.det.comp (galoisRep (S := S) (K := K) W' n)

@[simp]
lemma galoisRepDet_apply (n : ℕ) (σ : K ≃ₐ[S] K) :
    galoisRepDet (S := S) (K := K) W' n σ = LinearEquiv.det (galoisRep (S := S) W' n σ) :=
  rfl

variable (S) in

def GaloisRepDetEqCyclotomic (W' : Affine R) (n : ℕ) [NeZero n]
    (hn : Nat.card (rootsOfUnity n K) = n) : Prop :=
  ∀ σ : K ≃ₐ[S] K, galoisRepDet (S := S) (K := K) W' n σ =
    modularCyclotomicCharacter K hn (σ : K ≃+* K)

theorem galoisRepDetEqCyclotomic_two (hn : Nat.card (rootsOfUnity 2 K) = 2) :
    GaloisRepDetEqCyclotomic S W' 2 hn := fun _ => Subsingleton.elim _ _

end WeierstrassCurve.Affine.Point

section AlgClosed

end AlgClosed

namespace FreyPackage

open WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

noncomputable local instance instDecEqQbarDetCyclotomic : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

theorem card_rootsOfUnity_algebraicClosure (P : FreyPackage) :
    haveI : NeZero P.p := ⟨P.pp.ne_zero⟩
    Nat.card (rootsOfUnity P.p (AlgebraicClosure ℚ)) = P.p :=
  haveI : NeZero P.p := ⟨P.pp.ne_zero⟩
  IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) P.p

variable (P : FreyPackage)

def MuLineCyclotomicAtP : Prop :=
  haveI : NeZero P.p := ⟨P.pp.ne_zero⟩
  ∃ A₀ : ValuationSubring (AlgebraicClosure ℚ), A₀.LiesOverPrime P.p ∧
    ∃ z : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, z ≠ 0 ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A₀.inertiaSubgroupIn ℚ →
        (σ • z = ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
            P.card_rootsOfUnity_algebraicClosure
            (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : (ZMod P.p)ˣ) : ZMod P.p) • z) ∧
        ∀ y : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p,
          σ • y - y ∈ Submodule.span (ZMod P.p) {z}

def DetCyclotomicOnInertiaAtP : Prop :=
  haveI : NeZero P.p := ⟨P.pp.ne_zero⟩
  ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime P.p →
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      galoisRepDet (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p σ =
        modularCyclotomicCharacter (AlgebraicClosure ℚ) P.card_rootsOfUnity_algebraicClosure
          (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)

end FreyPackage


