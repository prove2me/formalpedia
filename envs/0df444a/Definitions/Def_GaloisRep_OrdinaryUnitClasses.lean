-- Prove2me | Definitions.Def_GaloisRep_OrdinaryUnitClasses
-- name    : GaloisRep_OrdinaryUnitClasses
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/0134b030-ea56-519c-94f1-f1f0274b17e3
-- title:
--   Ordinary unit cocycles and classes in the adjoint representation
-- statement:
--   Throughout, $k$ is a field, $p$ a prime and $\bar\rho$ a residual representation over $k$ with underlying space $\bar V$; the local group is $G_p = \mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$, mapped to $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ by `primeLocalToGlobal`, and the coefficient module is the full adjoint $\mathrm{End}_k(\bar V)$ with $\sigma$ acting by $f \mapsto \bar\rho(\sigma) f \bar\rho(\sigma^{-1})$ (no trace condition is imposed), restricted to $G_p$. Four items are defined. First, `unitRootInertia` is the subset of $\sigma \in G_p$ lying in the inertia subgroup attached to the valuation subring of $\overline{\mathbb Q}_p$ over $\mathbb Q_p$, fixing every $\zeta$ with $\zeta^p = 1$, and fixing every $\beta$ with $\|\beta\|_+ = 1$ whose $p$-th power is fixed by the whole inertia subgroup; that is, the subgroup of inertia acting trivially on $\mu_p$ and on the $p$-th roots of the units fixed by inertia. Second, for a $k$-submodule $V_1 \subseteq \bar V$, a $1$-cocycle $c$ is *ordinary* when $c(\sigma)V_1 \subseteq V_1$ for all $\sigma \in G_p$, and, for $\sigma$ in inertia, $c(\sigma)\bar V \subseteq V_1$ and $c(\sigma)|_{V_1} = 0$. Third, $c$ is an *ordinary unit cocycle* if it is ordinary, is of finite level — there is an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$, finite over $\mathbb Q$, with $c(gs) = c(g)$ whenever the global image of $s$ fixes $F$ pointwise — and satisfies $c(\sigma) = 0$ for all $\sigma$ in `unitRootInertia`. Fourth, `ordinaryUnitClassesAd` is the $k$-submodule of $H^1(G_p, \mathrm{ad}\,\bar\rho)$ spanned by the classes of ordinary unit cocycles, the classes being taken through the canonical map from cocycles to $H^1$. The predicates are conditions on cocycles, not on cohomology classes, and the subspace is defined as a span rather than as a set of classes, so that closure under addition is not asserted by the definition.
--
--   **Relation to Mathlib.** Group cohomology in degree one (`cocycles₁`, `H1`, `H1π`), restriction of representations along a group homomorphism, and valuation-subring inertia are Mathlib's; the inertia subgroup realised inside the full automorphism group (`inertiaSubgroupIn`) and the ordinary, unit and finite-level conditions on adjoint cocycles are the project's own, Mathlib having no local deformation conditions.
--
--   **Where it is used.** These are the local conditions at $p$ for the adjoint representation used in the Selmer-group bookkeeping of the deformation-theoretic step: the ordinary condition expresses stability of the line $V_1$ in the first-order deformation together with the required inertia behaviour, and the vanishing on the unit-root inertia subgroup is the 'peu ramifié' requirement. The resulting subspace is compared with the finite-flat classes defined alongside it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_OrdinaryUnitClasses.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology ExtCitation

namespace ResidualGaloisRep

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

def unitRootInertia : Set (primeLocalGaloisGroup (pPrime p)) :=
  {σ | localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧
    (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → localAut p σ ζ = ζ) ∧
    ∀ β : PadicAlgCl p, ‖β‖₊ = 1 →
      (∀ τ : primeLocalGaloisGroup (pPrime p),
        localAut p τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → localAut p τ (β ^ p) = β ^ p) →
      localAut p σ β = β}

def IsOrdinaryCocycleAd (V₁ : Submodule k ρbar.V)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) : Prop :=
  (∀ (σ : primeLocalGaloisGroup (pPrime p)), ∀ v ∈ V₁,
    c.val σ v ∈ V₁) ∧
  (∀ (σ : primeLocalGaloisGroup (pPrime p)),
    localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      (∀ v : ρbar.V, c.val σ v ∈ V₁) ∧
      ∀ v ∈ V₁, c.val σ v = 0)

def IsOrdinaryUnitCocycleAd (V₁ : Submodule k ρbar.V)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) : Prop :=
  ρbar.IsOrdinaryCocycleAd p V₁ c ∧
  (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ (g s : primeLocalGaloisGroup (pPrime p)),
      primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
  ∀ σ ∈ unitRootInertia p, c.val σ = 0

noncomputable def ordinaryUnitClassesAd (V₁ : Submodule k ρbar.V) :
    Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :=
  Submodule.span k
    {y | ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)),
      ρbar.IsOrdinaryUnitCocycleAd p V₁ c ∧
        y = (H1π (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))).hom c}

end ResidualGaloisRep


