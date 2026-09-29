-- Prove2me | Definitions.Def_GroupCohomology_ContinuousDuality
-- name    : GroupCohomology_ContinuousDuality
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/225a642e-e36d-5eec-a5a5-644b76a83e93
-- title:
--   Predicates characterising the three local-duality pairings on level-constant cohomology
-- statement:
--   Fix a commutative ring $k$, a group $G$, a homomorphism $r : G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ recording levels, representations $M, D, N$ of $G$ over $k$, a $k$-bilinear map $\varphi : M \to D \to N$ and a $k$-linear functional $\mathrm{inv}$ on $\mathrm{continuousH2}\ r\ N$. Here $\mathrm{continuousH2}\ r\ X$ is the quotient of the module `levelCocycles₂ r X` of inhomogeneous $2$-cocycles $z : G \times G \to X$ that are level-constant (there is a finite-dimensional intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $z(gs, g's') = z(g,g')$ whenever $r s, r s'$ fix $F$ pointwise) by the image under $d_{12}$ of the level-constant $1$-cochains; `continuousH2π` is the quotient map. Likewise $\mathrm{continuousH1}\ r\ X$ is the submodule of $H^1(G,X)$ spanned by the classes of level-constant $1$-cocycles.
--
--   Three predicates are defined, each a condition on a given linear map specified by its values on cocycle representatives rather than a construction. `IsTheta0` holds for $\theta : M^G \to (\mathrm{continuousH2}\ r\ D)^\vee$ when for all $m \in M^G$, all $z \in$ `levelCocycles₂ r D` and all $e \in$ `levelCocycles₂ r N` with $e(s,t) = \varphi(m, z(s,t))$ for all $(s,t)$, one has $\theta(m)([z]) = \mathrm{inv}([e])$. `IsTheta2` is the mirror condition for $\theta : \mathrm{continuousH2}\ r\ M \to (D^G)^\vee$, with $e(s,t) = \varphi(z(s,t), d)$ for $z$ a level-constant $2$-cocycle of $M$ and $d \in D^G$. `IsTheta1` holds for $\theta : \mathrm{continuousH1}\ r\ M \to (\mathrm{continuousH1}\ r\ D)^\vee$ when for all level-constant $1$-cocycles $f$ of $M$ and $g$ of $D$ and all $e \in$ `levelCocycles₂ r N` agreeing pointwise with the cup cochain $(s,t) \mapsto \varphi(f(s), D.\rho(s)(g(t)))$, the value $\theta([f])([g])$ equals $\mathrm{inv}([e])$. No existence, uniqueness or nondegeneracy is asserted.
--
--   **Relation to Mathlib.** The underlying cochain, cocycle and coboundary modules, $H^1$, $H^2$ and the projections `H1π`, `H2π` are Mathlib's `groupCohomology`; the level-constant variants `continuousH1`, `continuousH2` and these three duality predicates are the project's own.
--
--   **Where it is used.** The three predicates express the pairings $H^i(G,M) \times H^{2-i}(G,D) \to H^2(G,N) \xrightarrow{\mathrm{inv}} k$ of local Tate duality in bidegrees $(0,2)$, $(1,1)$ and $(2,0)$ for level-constant (continuous) cohomology, in the same style as the cup-product pairing predicate used for local Tate data. Characterising them by values on cocycle representatives allows statements about duality, and the local computations feeding the Galois-cohomological deformation-theoretic estimates, to be made independently of any particular construction of the pairings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_ContinuousDuality.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (inv : continuousH2 r N →ₗ[k] k)

def IsTheta0 (θ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D)) : Prop :=
  ∀ (m : M.ρ.invariants) (z : levelCocycles₂ r D) (e : levelCocycles₂ r N),
    (∀ st, (e : G × G → N) st = φ (m : M) ((z : G × G → D) st)) →
      θ m (continuousH2π r D z) = inv (continuousH2π r N e)

def IsTheta1 (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D)) : Prop :=
  ∀ (f : cocycles₁ M) (hf : IsLevelConstant₁ r (⇑f)) (g : cocycles₁ D) (hg : IsLevelConstant₁ r (⇑g))
    (e : levelCocycles₂ r N), (∀ st, (e : G × G → N) st = cupCochain φ (⇑f) (⇑g) st) →
      θ ⟨(H1π M).hom f, H1π_mem_continuousH1 r M hf⟩ ⟨(H1π D).hom g, H1π_mem_continuousH1 r D hg⟩
        = inv (continuousH2π r N e)

def IsTheta2 (θ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants) : Prop :=
  ∀ (z : levelCocycles₂ r M) (d : D.ρ.invariants) (e : levelCocycles₂ r N),
    (∀ st, (e : G × G → N) st = φ ((z : G × G → M) st) (d : D)) →
      θ (continuousH2π r M z) d = inv (continuousH2π r N e)

end groupCohomology


