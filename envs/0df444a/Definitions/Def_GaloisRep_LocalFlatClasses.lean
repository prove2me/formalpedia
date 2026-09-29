-- Prove2me | Definitions.Def_GaloisRep_LocalFlatClasses
-- name    : GaloisRep_LocalFlatClasses
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/539a38b7-1d1c-5c97-a834-693340166d26
-- title:
--   Locally finite flat cocycles and local flat classes at p
-- statement:
--   Fix a field $k$, a prime $p$ and a residual representation $\bar\rho$ over $k$, with underlying space $\bar\rho.V$ and global Galois action $\bar\rho.\rho$ on $\Gamma_{\mathbb Q}=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. Write $G_p$ for `primeLocalGaloisGroup (pPrime p)`, the group of $\mathbb Q_p$-algebra automorphisms of `PadicAlgCl p`, mapped to $\Gamma_{\mathbb Q}$ by `primeLocalToGlobal`; `localAut` is the coercion of an element of this type synonym to an automorphism of `PadicAlgCl p`. Given a $1$-cocycle $c$ of $G_p$ with values in the restriction of $\mathrm{ad}^0\bar\rho$ (trace-zero endomorphisms of $\bar\rho.V$ under conjugation), `dualLiftModuleAct` defines the action of $\sigma\in G_p$ on $\bar\rho.V\times\bar\rho.V$ by $(v,w)\mapsto(\bar\rho(\sigma)v,\;c(\sigma)\bar\rho(\sigma)v+\bar\rho(\sigma)w)$, i.e. the first-order deformation $\sigma\mapsto(1+\varepsilon c(\sigma))\bar\rho(\sigma)$ of $\bar\rho|_{G_p}$ written out on $\bar V\oplus\varepsilon\bar V$, in the same normalisation as the dual-number dictionary of [`groupCohomology.cocycleToDualLift`](../def/GroupCohomology_TangentSpace.html#L144).
--
--   `IsLocallyFlatCocycle` asserts the existence of a commutative ring $H$ with a Hopf algebra structure over $\mathbb Z_p$ that is finite and flat as a $\mathbb Z_p$-module and cocommutative as a coalgebra, together with a bijection $e$ from `WithConv (H →ₐ[ℤ_p] PadicAlgCl p)` — the $\overline{\mathbb Q}_p$-points of $\mathrm{Spec}\,H$ with their convolution product — onto $\bar\rho.V\times\bar\rho.V$, subject to two conditions: $e$ carries convolution to addition, $e(f\ast g)=e(f)+e(g)$; and for all $\sigma$ and all points $f,g$ with $g(h)=\sigma(f(h))$ for every $h\in H$, one has $e(g)=$ `dualLiftModuleAct` $c\,\sigma\,(e(f))$. Thus $e$ is an isomorphism of $G_p$-modules from the points of a finite flat cocommutative Hopf algebra onto the dual-lift module of $c$; no $k$-linearity of $e$ is required. `localFlatClasses` is the $k$-span inside $H^1(G_p,\mathrm{ad}^0\bar\rho)$ of the classes $[c]$, images under `H1π` of cocycles satisfying this predicate; the span is taken rather than proving that the set of such classes is already a subspace. `dualLiftModuleActAd`, `IsLocallyFlatCocycleAd` and `localFlatClassesAd` repeat the three definitions verbatim with $\mathrm{ad}^0$ replaced by the full adjoint representation $\mathrm{ad}\,\bar\rho$ on $\mathrm{End}_k(\bar\rho.V)$.
--
--   **Relation to Mathlib.** The Hopf-algebra, module-finiteness, flatness and cocommutativity predicates, and the convolution monoid `WithConv` on algebra maps out of a Hopf algebra, are Mathlib's; the finite flat local condition on cocycles and the resulting subspace of flat classes are the project's own notions.
--
--   **Where it is used.** These are the local conditions at $p$ used in the flat deformation problem: `localFlatClasses` plays the role of $H^1_f(\mathbb Q_p,\mathrm{ad}^0\bar\rho)$ in the Selmer-group bookkeeping that bounds tangent spaces of deformation rings, and `localFlatClassesAd` the corresponding subspace for $\mathrm{ad}\,\bar\rho$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_LocalFlatClasses.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

namespace ResidualGaloisRep

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

def localAut (σ : primeLocalGaloisGroup (pPrime p)) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p := σ

noncomputable def dualLiftModuleAct
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero))
    (σ : primeLocalGaloisGroup (pPrime p)) (x : ρbar.V × ρbar.V) : ρbar.V × ρbar.V :=
  (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.1,
    ((c : primeLocalGaloisGroup (pPrime p) → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ :
        Module.End k ρbar.V) (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.1)
      + ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.2)

def IsLocallyFlatCocycle
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
    Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
    ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = localAut p σ (f h)) → e g = ρbar.dualLiftModuleAct p c σ (e f)

noncomputable def localFlatClasses :
    Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) :=
  Submodule.span k
    {y | ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero),
      ρbar.IsLocallyFlatCocycle p c ∧
        y = (H1π (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)).hom c}

noncomputable def dualLiftModuleActAd
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (σ : primeLocalGaloisGroup (pPrime p)) (x : ρbar.V × ρbar.V) : ρbar.V × ρbar.V :=
  (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.1,
    ((c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ)
        (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.1)
      + ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.2)

def IsLocallyFlatCocycleAd
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
    Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
    ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = localAut p σ (f h)) → e g = ρbar.dualLiftModuleActAd p c σ (e f)

noncomputable def localFlatClassesAd :
    Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :=
  Submodule.span k
    {y | ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)),
      ρbar.IsLocallyFlatCocycleAd p c ∧
        y = (H1π (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))).hom c}

end ResidualGaloisRep


