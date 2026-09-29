-- Prove2me | Definitions.Def_CerednikDrinfeld_ToricUniformization
-- name    : CerednikDrinfeld_ToricUniformization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/5b4fbc55-09d6-5e3b-990a-b2e8cf64df36
-- title:
--   Toric uniformisation data for a Hecke–Galois torsion module
-- statement:
--   Two declarations sit here. First, for a natural number $p$ and a two-level degeneracy datum $D$ on finite index sets $E \rightrightarrows V$, `ribbonGramModP p D x` is the $\mathbb{Z}/p$-valued functional on the ribbon kernel $Y = \mathrm{ribbonKernel}\,D \subseteq \mathbb{Z}^E$ obtained from the width Gram functional $\mathrm{ribbonGram}\,D\,x = \sum_{e} w(e)\,x_e\,(\cdot)_e$ by composing with the reduction $\mathbb{Z} \to \mathbb{Z}/p$; the accompanying lemma records its values.
--
--   Second, `ToricUniformization` is a structure of data and laws attached to: a natural number $p$, a prime $r$, a degeneracy datum $D$ with Hecke data $H$ (so each prime $\ell$ gives $T_\ell|_Y =$ `heckeKernelMap H ℓ` on $Y$), a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $r$ a non-unit of $A$, and an abelian group $T$ with an action of $\mathbb{T} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ by $\mathbb{Z}$-endomorphisms and of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ by additive automorphisms. Its fields are: an abelian group $U$ with a $\mathbb{T}$-action, divisible in the sense that $n U = U$ for every $n > 0$; a $\mathbb{T}$-equivariant $\pi : U \to T$ whose image contains every $t$ with $p\,t = 0$; an isomorphism $\lambda : Y \xrightarrow{\sim} \ker\pi$; an isomorphism $\chi : U[p] \xrightarrow{\sim} \mathrm{Hom}_{\mathbb{Z}}(Y, \mathbb{Z}/p)$ intertwining the action of $X_\ell$ on $U[p]$ (where it preserves $U[p]$) with precomposition by $T_\ell|_Y$; a Gram-adjointness law saying that $X_\ell \lambda(y) = \lambda(y')$ forces $\langle T_\ell|_Y x, y\rangle = \langle x, y'\rangle$ for all $x \in Y$; a surjection $\mathrm{tame}$ from the inertia subgroup of $A$ over $\mathbb{Q}$ onto $\mathbb{Z}/p$ written multiplicatively; a Kummer law, stating for $\sigma$ in that inertia subgroup and $p\,u = \lambda(x)$ that $\sigma(\pi u) = \pi u + \pi v$ for some $v \in U[p]$ with $\chi(v) = \mathrm{tame}(\sigma)\cdot \mathrm{ribbonGramModP}\,p\,D\,x$; and two laws for any $\varphi$ that is a Frobenius at $A$ over $r$ — on $\pi(U[p])$, $\varphi(\pi v) = \pi v'$ with $\chi(v') = r\,(\chi(v) \circ T_r|_Y)$, and for $p\,u = \lambda(x)$, $\varphi(\pi u) = \pi(X_r u) + \pi v$ with $p\,v = 0$.
--
--   Thus $U$ itself carries no Galois action: every Galois assertion is made about $T$ through $\pi$, and the structure is a presentation predicate on a chosen model $(U, \pi, \lambda, \chi, \mathrm{tame})$ rather than a property of $T$ alone. The number $p$ is not assumed prime.
--
--   **Relation to Mathlib.** Mathlib has no notion of rigid-analytic or toric uniformisation data; both declarations are the project's own, built on its ribbon/degeneracy formalism and on Mathlib's `ValuationSubring` inertia and Frobenius vocabulary.
--
--   **Where it is used.** This is the finite-level shadow of the Mumford–Čerednik–Drinfeld uniformisation of the Jacobian of a Shimura curve with purely toric reduction at $r$: the character group is the ribbon kernel, the valuation of the period pairing is the width Gram pairing, and Frobenius acts through $U_r$. Such data is the input from which the $p$-torsion datum with its toric subgroup and specialisation map is extracted, in the level-lowering step at $r$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_ToricUniformization.lean

import Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]

def ribbonGramModP (p : ℕ) (D : DegeneracyData E V) (x : ↥(ribbonKernel D)) :
    ↥(ribbonKernel D) →ₗ[ℤ] ZMod p :=
  (Int.castAddHom (ZMod p)).toIntLinearMap ∘ₗ (ribbonGram D x)

omit [Fintype V] in
@[simp] theorem ribbonGramModP_apply (p : ℕ) (D : DegeneracyData E V) (x y : ↥(ribbonKernel D)) :
    ribbonGramModP p D x y = ((ribbonGram D x y : ℤ) : ZMod p) := rfl

structure ToricUniformization (p r : ℕ) [Fact r.Prime] (D : DegeneracyData E V) (H : HeckeData D)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (T : Type) [AddCommGroup T] (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T) : Type 1 where

  U : Type
  [instAddCommGroupU : AddCommGroup U]

  heckeU : HeckeAlg →+* Module.End ℤ U

  divisible : ∀ u : U, ∀ n : ℕ, 0 < n → ∃ u' : U, n • u' = u

  π : U →+ T

  π_hecke : ∀ (x : HeckeAlg) (u : U), π (heckeU x u) = hecke x (π u)

  π_surj_torsion : ∀ t : T, p • t = 0 → ∃ u : U, π u = t

  periodEquiv : ↥(ribbonKernel D) ≃+ ↥π.ker

  period_adjoint : ∀ (ℓ : Nat.Primes) (x y y' : ↥(ribbonKernel D)),
    heckeU (heckeGen ℓ) (periodEquiv y : U) = (periodEquiv y' : U) →
      ribbonGram D (heckeKernelMap H ℓ x) y = ribbonGram D x y'

  torsionEquiv : ↥(Submodule.torsionBy ℤ U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p)

  torsion_hecke : ∀ (ℓ : Nat.Primes) (v : ↥(Submodule.torsionBy ℤ U (p : ℤ)))
    (hv : heckeU (heckeGen ℓ) (v : U) ∈ Submodule.torsionBy ℤ U (p : ℤ)),
    torsionEquiv ⟨heckeU (heckeGen ℓ) (v : U), hv⟩ = (torsionEquiv v) ∘ₗ heckeKernelMap H ℓ

  tame : ↥(A.inertiaSubgroupIn ℚ) →* Multiplicative (ZMod p)

  tame_surjective : Function.Surjective tame

  kummer : ∀ (σ : ↥(A.inertiaSubgroupIn ℚ)) (u : U) (x : ↥(ribbonKernel D)),
    (p : ℤ) • u = (periodEquiv x : U) →
      ∃ (v : ↥(Submodule.torsionBy ℤ U (p : ℤ))),
        gal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (π u) = π u + π (v : U) ∧
        torsionEquiv v = (Multiplicative.toAdd (tame σ)) • ribbonGramModP p D x

  frob_toric : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
    ∀ v : ↥(Submodule.torsionBy ℤ U (p : ℤ)), ∃ v' : ↥(Submodule.torsionBy ℤ U (p : ℤ)),
      gal φ (π (v : U)) = π (v' : U) ∧
        torsionEquiv v' = (r : ℤ) • ((torsionEquiv v) ∘ₗ heckeKernelMap H ⟨r, Fact.out⟩)

  frob_quot : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
    ∀ (u : U) (x : ↥(ribbonKernel D)), (p : ℤ) • u = (periodEquiv x : U) →
      ∃ v : U, (p : ℤ) • v = 0 ∧ gal φ (π u) = π (heckeU (heckeGen ⟨r, Fact.out⟩) u) + π v

attribute [instance] ToricUniformization.instAddCommGroupU

end CerednikDrinfeld

end


