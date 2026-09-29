-- Prove2me | Definitions.Def_CerednikDrinfeld_QMModuliPropsD
-- name    : CerednikDrinfeld_QMModuliPropsD
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/95ebb56c-b5c3-5269-83b5-35de4920f4a5
-- title:
--   Orientation and good reduction for moduli witnesses over ℤ[1/D]
-- statement:
--   Two predicates are attached to a witness `w : M.ModuliWitnessD Λ N q q' D` for a Shimura curve model $M$ (attached to an order $R_0$ in $\mathbb H[\mathbb Q,a,b]$, a real matrix embedding $\iota$ and a family $\mathcal S$ of adelic Hecke data), a lattice $\Lambda$ and natural numbers $N,q,q',D$; such a witness consists of an integral scheme $X$ proper and smooth over $\mathbb Z[1/D] =$ `Localization.Away (D : ℤ)` together with a bijection `w.pts` between places of $M$'s geometric function field and geometric points of $X$ over the chosen base point `w.sbar`, and a moduli map `w.pt` from false elliptic curves with $\Lambda$-action and level-$N$ structure to points of $X$.
--
--   `IsOriented` asks that the Hecke correspondence `M.corrBar` of the model be described by $\ell$-isogenies also at the primes dividing the level: for every prime $\ell \mid N$ and every pair of places $P, Q$, the point $Q$ lies in the support of `M.corrBar ℓ` applied to the divisor $1\cdot P$ if and only if there are a false elliptic curve $u$ over $\overline{\mathbb Q}$ equipped with an extra level-$\ell$ structure (a closed, $\Lambda$-stable, $\ell$-torsion subgroup scheme, finite flat of rank $\ell^2$ and disjoint from the level-$N$ structure) and a false elliptic curve $d$, with $u$ carried to $P$ and $d$ to $Q$ by `w.pt ... w.sbar`, such that `IsLevelIsogeny ℓ u d` holds: mutually dual $\Lambda$-equivariant homomorphisms $\varphi, \psi$ over the base with $\varphi\psi$ and $\psi\varphi$ the action of $\ell$, whose kernel is exactly the extra level-$\ell$ subgroup, and with $\varphi$ carrying the level-$N$ structure of $u$ into that of $d$. This is the counterpart, at primes dividing $N$, of the witness field `hecke`, which covers primes not dividing $N$ through `HeckeNeighbour`.
--
--   `IsGoodReductionModel` is the conjunction of: $\pi_X$ is smooth of relative dimension $1$; and for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec}\mathbb Z[1/D]$ the fibre product of $\pi_X$ with $s$ is an integral scheme. Both are predicates on the chosen witness, not on $M$ alone; they repeat the predicates defined for `ModuliWitness` with the base ring $\mathbb Z[1/Nqq']$ replaced by $\mathbb Z[1/D]$.
--
--   **Relation to Mathlib.** Shimura curve models, false elliptic curves and their level structures are the project's own notions; the geometric conditions are phrased with Mathlib's morphism properties (`SmoothOfRelativeDimension`, `IsIntegral`) and categorical pullbacks.
--
--   **Where it is used.** These predicates record the input needed at primes dividing the level for the quaternionic (Čerednik–Drinfeld) part of the argument: the orientation condition identifies the support of the model's Hecke correspondence with $\ell$-isogenies of false elliptic curves, and the good-reduction condition provides a smooth proper integral curve over $\mathbb Z[1/D]$ whose Jacobian torsion carries the Galois and Hecke action used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMModuliPropsD.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_CerednikDrinfeld_QMModuliWitnessD
import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}

def ShimuraCurveModel.ModuliWitnessD.IsOriented {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R₀ ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D) : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∣ N → ∀ (P Q : Place (AlgebraicClosure ℚ) M.Fbar),
    Q ∈ (M.corrBar ℓ hℓ (Finsupp.single P 1)).support ↔
      ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) (d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
        w.pt _ w.sbar u.1 = w.pts P ∧ w.pt _ w.sbar d = w.pts Q ∧ FakeEllipticCurve.IsLevelIsogeny ℓ u d

def ShimuraCurveModel.ModuliWitnessD.IsGoodReductionModel {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R₀ ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D) : Prop :=
  SmoothOfRelativeDimension 1 w.πX ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
    IsIntegral (CategoryTheory.Limits.pullback w.πX s)

end CerednikDrinfeld

end


