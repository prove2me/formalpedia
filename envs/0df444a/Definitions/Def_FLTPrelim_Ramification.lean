-- Prove2me | Definitions.Def_FLTPrelim_Ramification
-- name    : FLTPrelim_Ramification
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/2f679d60-0c74-5493-b36f-16da20baed9a
-- title:
--   Unramifiedness at a prime of torsion Galois representations
-- statement:
--   Three auxiliary notions and one instantiation. First, for a valuation subring $A$ of a field $L$ and a natural number $q$, [`ValuationSubring.LiesOverPrime A q`](../def/FLTPrelim_Ramification.html#L16) says simply that the image of $q$ in $L$ lies in `A.nonunits`, i.e. $q$ belongs to the maximal ideal of $A$; no primality of $q$ is required by the definition. Second, for an extension $L/K$, [`ValuationSubring.inertiaSubgroupIn K A`](../def/FLTPrelim_Ramification.html#L21) is the image of Mathlib's inertia subgroup `A.inertiaSubgroup K` (a subgroup of the decomposition subgroup, i.e. of the stabiliser of $A$ in $L \simeq_{\mathrm{alg}[K]} L$) under the inclusion `(A.decompositionSubgroup K).subtype`, so that inertia is presented as a subgroup of the full automorphism group $L \simeq_{\mathrm{alg}[K]} L$ rather than of the decomposition subgroup.
--
--   Third, given a tower $R \to S \to K$ with $S$, $K$ fields and an affine Weierstrass curve $W'$ over $R$, [`WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt S K W' n q`](../def/FLTPrelim_Ramification.html#L35) asserts: for every valuation subring $A$ of $K$ with $q \in A.\mathrm{nonunits}$, every $\sigma$ in the inertia subgroup of $A$ over $S$ (viewed in $K \simeq_{\mathrm{alg}[S]} K$), and every $x$ in the $n$-torsion submodule `Submodule.torsionBy ℤ (W'⁄K).Point n` of the point group of the base change of $W'$ to $K$, one has $\sigma \bullet x = x$. The action $\sigma \bullet x$ of automorphisms on points is the one supplied by the project's Galois-representation module. Thus the predicate is the triviality of inertia on $n$-torsion, stated place by place rather than through a representation object.
--
--   Finally, [`FreyPackage.GaloisRepUnramifiedAt P q`](../def/FLTPrelim_Ramification.html#L46) is this predicate for $R = S = \mathbb{Q}$, $K = \overline{\mathbb{Q}}$, the curve `P.freyCurve` and $n = P.p$: the mod-$p$ representation on $\overline{\mathbb{Q}}$-points of the Frey curve killed by $p$ is unramified at $q$.
--
--   **Relation to Mathlib.** [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16) and [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21) are thin wrappers around Mathlib's valuation-subring API (`nonunits`, `inertiaSubgroup`, `decompositionSubgroup`), the latter only transporting Mathlib's inertia subgroup along the inclusion of the decomposition subgroup. The unramifiedness predicates for torsion points of a Weierstrass curve are the project's own; Mathlib has no such notion.
--
--   **Where it is used.** These predicates express the local conditions on the mod-$p$ representation attached to a Frey package at primes $q$ not dividing the relevant level, which are what the Serre-type level-lowering and irreducibility arguments consume. The Frey-package instance is the form in which the unramifiedness of $E[p]$ outside the primes of bad reduction and $p$ enters the main line of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FLTPrelim_Ramification.lean

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace ValuationSubring

variable {L : Type u} [Field L]

def LiesOverPrime (A : ValuationSubring L) (q : ℕ) : Prop :=
  (q : L) ∈ A.nonunits

variable (K : Type*) [Field K] [Algebra K L]

def inertiaSubgroupIn (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

end ValuationSubring

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [Field S] [Field K]
  [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

variable (S K) in

def GaloisRepUnramifiedAt (W' : Affine R) (n : ℕ) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring K, A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn S,
    ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x = x

end WeierstrassCurve.Affine.Point

namespace FreyPackage

open WeierstrassCurve.Affine.Point

def GaloisRepUnramifiedAt (P : FreyPackage) (q : ℕ) : Prop :=
  WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ
    P.freyCurve P.p q

end FreyPackage

end


