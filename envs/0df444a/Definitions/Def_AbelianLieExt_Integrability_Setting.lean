-- Prove2me | Definitions.Def_AbelianLieExt_Integrability_Setting
-- name    : AbelianLieExt_Integrability_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:27:35.263292+00:00
-- url     : https://prove2.me/theorems/401389a0-de0e-49b9-a9e5-41579f3826e8
-- title:
--   §0, §I, §II, §III, §IV, §VI, App. B — smooth G-modules with A₀ ≅ 𝔞/Γ_A, Lie algebra cochains, 𝔞 ⊕_ω 𝔤, period group, flux, characteristic homomorphism, Lie group extensions
-- statement:
--   This file sets up the objects of K.-H. Neeb's integrability criterion for abelian extensions of Lie groups.
--
--   Let $G$ be a real Lie group modelled on a Banach space $E$, with Lie algebra $\mathfrak g = T_1(G)$ carrying the bracket of left-invariant vector fields. Let $A$ be an abelian Lie group modelled on a Banach space $\mathfrak a$, on which $G$ acts by group automorphisms.
--
--   1. **Smooth $G$-module with $A_0 \cong \mathfrak a/\Gamma_A$.** The action $G \times A \to A$ is smooth, and there is a smooth homomorphism $q_A\colon \mathfrak a \to A$ which is a local diffeomorphism, has derivative $\mathrm{id}_{\mathfrak a}$ at $0$, has image the identity component $A_0$, and intertwines the actions: $g.q_A(v) = q_A(\rho_{\mathfrak a}(g)v)$. Here $\rho_{\mathfrak a}(g)$ is the derivative at $0$ of $b \mapsto g.b$, and $\Gamma_A := \ker q_A$ is a discrete subgroup with $A_0 \cong \mathfrak a/\Gamma_A$.
--   2. **Derived action and adjoint action.** $x.v := \mathrm d(g \mapsto \rho_{\mathfrak a}(g)v)(1)(x)$ for $x \in \mathfrak g$, $v \in \mathfrak a$, and $\mathrm{Ad}(g)$ is the derivative at $1$ of $h \mapsto ghg^{-1}$.
--   3. **Cochains (Definition B.1).** $\alpha\colon \mathfrak g \to \mathfrak a$ is a 1-cocycle if $x.\alpha(y) - y.\alpha(x) - \alpha([x,y]) = 0$, and a 1-coboundary if $\alpha(x) = x.v$ for some $v \in \mathfrak a$. A continuous bilinear $\omega\colon \mathfrak g \times \mathfrak g \to \mathfrak a$ is a 2-cocycle, $\omega \in Z^2_c(\mathfrak g, \mathfrak a)$, if it is alternating and
--   $$x.\omega(y,z) - y.\omega(x,z) + z.\omega(x,y) - \omega([x,y],z) + \omega([x,z],y) - \omega([y,z],x) = 0.$$
--   4. **The Lie algebra $\mathfrak a \oplus_\omega \mathfrak g$ (Definition I.2)** is $\mathfrak a \times \mathfrak g$ with $[(a,x),(a',x')] = (x.a' - x'.a + \omega(x,x'), [x,x'])$.
--   5. **Flux of a path (Lemma VI.2).** For a smooth curve $\gamma$, $\widetilde F_\omega(\gamma)(x) = \int_0^1 \gamma(t).\omega\big(\gamma(t)^{-1}\gamma'(t), \mathrm{Ad}(\gamma(t))^{-1}.x\big)\,dt$, where $\gamma(t)^{-1}\gamma'(t) \in \mathfrak g$ is the left-trivialised velocity.
--   6. **Period group (§IV).** A smooth sphere is a smooth map $\sigma\colon \mathbb R^2 \to G$ equal to $1$ off the open unit square; $\int_\sigma \omega^{\mathrm{eq}} = \int_0^1\!\int_0^1 \sigma.\omega(\sigma^{-1}\partial_t\sigma, \sigma^{-1}\partial_s\sigma)\,ds\,dt$ is the integral of the equivariant 2-form $\omega^{\mathrm{eq}}$ (Definition B.4), and $\Pi_\omega$ is the set of these integrals.
--   7. **Characteristic homomorphism (Definition III.6).** $\theta_A(b) := \mathrm d(g \mapsto g.b - b)(1) \in Z^1_c(\mathfrak g, \mathfrak a)$; $\overline\theta_A\colon \pi_0(A) \to H^1_c(\mathfrak g, \mathfrak a)$ is induced by it.
--   8. **Flux conditions.** `FluxFactors` is condition (2) of Theorem VI.7: there is a surjective homomorphism $\gamma\colon \pi_1(G) \to \pi_0(A) = A/A_0$ such that for every smooth loop $\ell$ at $1$ representing $c \in \pi_1(G)$ and every $b \in A$ with $[b] = \gamma(c)$, $\widetilde F_\omega(\ell) - \theta_A(b)$ is a coboundary, i.e. $F_\omega = \overline\theta_A \circ \gamma$. `FluxVanishes` says $\widetilde F_\omega(\ell)$ is a coboundary for every such loop, i.e. $F_\omega = 0$.
--   9. **Lie group extensions (Definitions I.1, II.2, II.4).** An extension of $G$ by $A$ integrating $\mathfrak a \oplus_\omega \mathfrak g$ is a Lie group $\widehat G$ with smooth homomorphisms $\iota\colon A \hookrightarrow \widehat G$ (injective) and $q\colon \widehat G \twoheadrightarrow G$ (surjective) with $\ker q = \iota(A)$, a smooth local section of $q$ near $1$ making $\widehat G$ locally $A \times U$ (a principal $A$-bundle), conjugation $\hat g\,\iota(b)\,\hat g^{-1} = \iota(q(\hat g).b)$, and a topological linear isomorphism $\varphi\colon \mathfrak a \times \mathfrak g \to \mathbf L(\widehat G)$ restricting to $\mathrm d\iota(0)$ on $\mathfrak a$, lifting $\mathrm dq(1)$, and carrying the bracket of $\mathfrak a \oplus_\omega \mathfrak g$ to that of $\mathbf L(\widehat G)$. `IntegratesTo` asserts such an extension exists; `IntegratesToConnected` asserts one exists with $\widehat G$ connected.
--
--   These are the objects in which the Integrability Criterion (Theorem VI.7) and its supporting results are stated.
--
--   **Formalization Note** The paper works with Lie groups over $\mathbb K \in \{\mathbb R, \mathbb C\}$ modelled on sequentially complete locally convex spaces; here everything is real and Banach-modelled (a special case, in which Bastiani $C^\infty$ agrees with Fréchet $C^\infty$), smooth means $C^\infty$, and all types live in `Type`. $\widehat G$ is charted on $\mathfrak a \times E$, which is no restriction since $\mathbf L(\widehat G) \cong \mathfrak a \times \mathfrak g$ as topological vector spaces. Tangent spaces at the identity of $A$ are identified with $\mathfrak a$ through $q_A$ (derivative $\mathrm{id}$ at $0$). The bracket on $\mathfrak g$ is Mathlib's `GroupLieAlgebra` bracket, the Lie bracket of left-invariant vector fields at $1$, which agrees with the paper's $[x,y] = b(x,y) - b(y,x)$. The paper's $\pi_0(A)$ is encoded as $A/q_A(\mathfrak a)$, $\pi_1(G)$ as Mathlib's fundamental group at $1$ with smooth loop representatives (every class has one), and $\pi_2(G)$ through smooth spheres constant off the open unit square (every class has one). The equivariance of $q_A$ is implied by the paper's "$A_0 \cong \mathfrak a/\Gamma_A$ as $G$-modules" and is stated explicitly. Piecewise smooth paths are replaced by smooth ones, which loses nothing since $\widetilde F_\omega$ is invariant under monotone reparametrisation.
-- source:
--   Neeb, Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, pp. 5–8, 14–15, 20–23, 60–62: §0, Definitions I.1, I.2, II.2, II.4, III.6, B.1, B.4, §IV (period map), Remark VI.1, Lemma VI.2, Proposition VI.3, Theorem VI.7 (2)

import Mathlib

namespace AbelianLieExt.Integrability

open scoped Manifold

/-! # Abelian extensions of Banach–Lie groups: the objects of Neeb's Integrability Criterion

Everything is over `ℝ`, every model space is a Banach space, "smooth" is `C^∞` (`∞`), and every
type lives in `Type`. -/

section Setting

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {G : Type} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (⊤ : ℕ∞) G]
  {a : Type} [NormedAddCommGroup a] [NormedSpace ℝ a] [CompleteSpace a]
  (A : Type) [TopologicalSpace A] [ChartedSpace a A] [AddCommGroup A]
  [LieAddGroup 𝓘(ℝ, a) (⊤ : ℕ∞) A] [DistribMulAction G A]

/-- The Lie algebra `𝔤 = T_1 G` of `G`, with Mathlib's bracket (the bracket of left-invariant
vector fields at `1`). -/
abbrev LieAlg (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Type) [TopologicalSpace G]
    [ChartedSpace E G] [Group G] : Type :=
  GroupLieAlgebra 𝓘(ℝ, E) G

/-- `ρ_𝔞(g)`: the derivative at `0` of `b ↦ g • b`, a continuous linear map `𝔞 → 𝔞`. -/
noncomputable def rhoA (g : G) : a →L[ℝ] a :=
  mfderiv 𝓘(ℝ, a) 𝓘(ℝ, a) (fun b : A => g • b) (0 : A)

/-- The derived `𝔤`-action on `𝔞`: `x.v := d(g ↦ ρ_𝔞(g) v)(1) x`. -/
noncomputable def dot (x : LieAlg E G) (v : a) : a :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, a) (fun g : G => rhoA A g v) (1 : G) x

/-- `Ad(g)`: the derivative at `1` of conjugation `h ↦ g h g⁻¹`. -/
noncomputable def Ad (g : G) : LieAlg E G →L[ℝ] LieAlg E G :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => g * h * g⁻¹) (1 : G)

/-- §0 (p. 5) and Definition B.2: `A` is a smooth `G`-module whose identity component is
`A₀ ≅ 𝔞/Γ_A`, realised by the smooth homomorphism `qA : 𝔞 → A` (with `Γ_A := ker qA`), a local
diffeomorphism with derivative `id` at `0` and image `A₀`, intertwining the actions. -/
structure IsSmoothModuleCover (qA : a →+ A) : Prop where
  smooth_action : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, a)) 𝓘(ℝ, a) (⊤ : ℕ∞) (fun p : G × A => p.1 • p.2)
  smooth_q : ContMDiff 𝓘(ℝ, a) 𝓘(ℝ, a) (⊤ : ℕ∞) qA
  local_diffeo : IsLocalDiffeomorph 𝓘(ℝ, a) 𝓘(ℝ, a) (⊤ : ℕ∞) qA
  deriv_id : HasMFDerivAt 𝓘(ℝ, a) 𝓘(ℝ, a) qA 0 (ContinuousLinearMap.id ℝ a)
  range_eq : Set.range qA = connectedComponent (0 : A)
  equivariant : ∀ (g : G) (v : a), g • qA v = qA (rhoA A g v)

/-- Continuous 1-cocycles `Z¹_c(𝔤, 𝔞)` (Definition B.1): `x.α(y) − y.α(x) − α([x, y]) = 0`. -/
def IsCocycle1 (α : LieAlg E G → a) : Prop :=
  ∀ x y : LieAlg E G, dot A x (α y) - dot A y (α x) - α ⁅x, y⁆ = 0

/-- 1-coboundaries `B¹_c(𝔤, 𝔞)`: maps of the form `x ↦ x.v`. -/
def IsCoboundary1 (α : LieAlg E G → a) : Prop :=
  ∃ v : a, ∀ x : LieAlg E G, α x = dot A x v

/-- Continuous 2-cocycles `Z²_c(𝔤, 𝔞)` (Definition B.1): alternating continuous bilinear maps with
`x.ω(y,z) − y.ω(x,z) + z.ω(x,y) − ω([x,y],z) + ω([x,z],y) − ω([y,z],x) = 0`. -/
def IsCocycle2 (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) : Prop :=
  (∀ x y : LieAlg E G, ω x y = -ω y x) ∧
  ∀ x y z : LieAlg E G, dot A x (ω y z) - dot A y (ω x z) + dot A z (ω x y)
    - ω ⁅x, y⁆ z + ω ⁅x, z⁆ y - ω ⁅y, z⁆ x = 0

/-- The bracket of `𝔞 ⊕_ω 𝔤` (Definition I.2):
`[(a, x), (a', x')] = (x.a' − x'.a + ω(x, x'), [x, x'])`. -/
noncomputable def bracketOmega (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a)
    (p p' : a × LieAlg E G) : a × LieAlg E G :=
  (dot A p.2 p'.1 - dot A p'.2 p.1 + ω p.2 p'.2, ⁅p.2, p'.2⁆)

/-- Left-trivialised velocity `γ(t)⁻¹ γ'(t) ∈ 𝔤` of a curve `γ : ℝ → G`. -/
noncomputable def leftLog (γ : ℝ → G) (t : ℝ) : LieAlg E G :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => (γ t)⁻¹ * h) (γ t)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))

/-- Left-trivialised partial derivative in the first variable, `σ(t,s)⁻¹ ∂σ/∂t`. -/
noncomputable def leftLog₁ (σ : ℝ × ℝ → G) (p : ℝ × ℝ) : LieAlg E G :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => (σ p)⁻¹ * h) (σ p)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) σ p ((1 : ℝ), (0 : ℝ)))

/-- Left-trivialised partial derivative in the second variable, `σ(t,s)⁻¹ ∂σ/∂s`. -/
noncomputable def leftLog₂ (σ : ℝ × ℝ → G) (p : ℝ × ℝ) : LieAlg E G :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => (σ p)⁻¹ * h) (σ p)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) σ p ((0 : ℝ), (1 : ℝ)))

/-- The path flux `F̃_ω(γ)(x) = ∫₀¹ γ(t).ω(γ(t)⁻¹γ'(t), Ad(γ(t))⁻¹.x) dt` (Lemma VI.2). -/
noncomputable def fluxCocycle (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) (γ : ℝ → G)
    (x : LieAlg E G) : a :=
  ∫ t in (0 : ℝ)..1, rhoA A (γ t) (ω (leftLog γ t) (Ad (γ t)⁻¹ x))

/-- A smooth sphere in `G`: a smooth map `ℝ² → G` equal to `1` off the open unit square, i.e. a
smooth map `[0,1]²/∂[0,1]² ≅ 𝕊² → G` sending the base point to `1`. -/
def IsSphere (σ : ℝ × ℝ → G) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) σ ∧
    ∀ p : ℝ × ℝ, p ∉ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 → σ p = 1

/-- `∫_σ ω^eq = ∫₀¹∫₀¹ σ(t,s).ω(σ⁻¹∂_tσ, σ⁻¹∂_sσ) ds dt`, the integral of the equivariant
2-form `ω^eq` over a smooth sphere. -/
noncomputable def sphereIntegral (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) (σ : ℝ × ℝ → G) : a :=
  ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
    rhoA A (σ (t, s)) (ω (leftLog₁ σ (t, s)) (leftLog₂ σ (t, s)))

/-- The period group `Π_ω = per_ω(π₂(G))`, as the set of integrals of `ω^eq` over smooth
spheres. -/
def periodSet (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) : Set a :=
  {v | ∃ σ : ℝ × ℝ → G, IsSphere (E := E) σ ∧ v = sphereIntegral A ω σ}

/-- `θ_A(b) = D₁(d'_G(b))`: the derivative at `1` of `g ↦ g.b − b` (Definition III.6). -/
noncomputable def charHom (b : A) : LieAlg E G → a :=
  fun x => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, a) (fun g : G => g • b - b) (1 : G) x

/-- `γ` is a smooth loop at `1` representing the class `c ∈ π₁(G, 1)`. -/
def IsSmoothLoopRep (c : FundamentalGroup G 1) (γ : ℝ → G) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) γ ∧
    ∃ p : Path (1 : G) 1, (∀ t : unitInterval, p t = γ (t : ℝ)) ∧
      c = FundamentalGroup.fromPath (⟦p⟧ : Path.Homotopic.Quotient (1 : G) 1)

/-- Condition (2) of Theorem VI.7: a surjective homomorphism `γ : π₁(G) → π₀(A) = A/A₀` with
`F_ω = θ̄_A ∘ γ` in `H¹_c(𝔤, 𝔞)`. -/
def FluxFactors (qA : a →+ A) (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) : Prop :=
  ∃ γ : FundamentalGroup G 1 →* Multiplicative (A ⧸ qA.range), Function.Surjective γ ∧
    ∀ (c : FundamentalGroup G 1) (ℓ : ℝ → G) (b : A), IsSmoothLoopRep (E := E) c ℓ →
      (QuotientAddGroup.mk b : A ⧸ qA.range) = Multiplicative.toAdd (γ c) →
      IsCoboundary1 A (fun x => fluxCocycle A ω ℓ x - charHom A b x)

/-- `F_ω = 0` on `π₁(G)`. -/
def FluxVanishes (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) : Prop :=
  ∀ (c : FundamentalGroup G 1) (ℓ : ℝ → G), IsSmoothLoopRep (E := E) c ℓ →
    IsCoboundary1 A (fluxCocycle A ω ℓ)

/-- A Lie group extension `A ↪ Ĝ ↠ G` of `G` by the smooth `G`-module `A` whose Lie algebra is
equivalent to `𝔞 ⊕_ω 𝔤` (Definitions I.1, I.2, II.2, II.4). `Ĝ` is modelled on `𝔞 × E`. -/
structure Extension (qA : a →+ A) (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) where
  /-- the total group `Ĝ` -/
  H : Type
  [instTop : TopologicalSpace H]
  [instChart : ChartedSpace (a × E) H]
  [instGroup : Group H]
  [instLie : LieGroup 𝓘(ℝ, a × E) (⊤ : ℕ∞) H]
  /-- the inclusion of the kernel `A ↪ Ĝ` -/
  ι : A → H
  /-- the projection `Ĝ ↠ G` -/
  q : H →* G
  ι_add : ∀ b c : A, ι (b + c) = ι b * ι c
  ι_injective : Function.Injective ι
  ι_smooth : ContMDiff 𝓘(ℝ, a) 𝓘(ℝ, a × E) (⊤ : ℕ∞) ι
  q_smooth : ContMDiff 𝓘(ℝ, a × E) 𝓘(ℝ, E) (⊤ : ℕ∞) q
  q_surjective : Function.Surjective q
  /-- exactness: `ker q = ι(A)` -/
  ker_q : ∀ h : H, q h = 1 ↔ ∃ b : A, ι b = h
  /-- a smooth local section `σ` of `q` on an open neighbourhood `U` of `1`, together with a smooth
  "fibre coordinate" `r`, so that `(b, g) ↦ ι b * σ g` is a diffeomorphism `A × U ≅ q⁻¹(U)` -/
  local_trivial : ∃ (U : Set G) (σ : G → H) (r : H → A), IsOpen U ∧ (1 : G) ∈ U ∧
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, a × E) (⊤ : ℕ∞) σ U ∧ (∀ g ∈ U, q (σ g) = g) ∧
    ContMDiffOn 𝓘(ℝ, a × E) 𝓘(ℝ, a) (⊤ : ℕ∞) r (q ⁻¹' U) ∧
    ∀ h ∈ q ⁻¹' U, ι (r h) * σ (q h) = h
  /-- the conjugation action of `Ĝ` on `A` induces the given action of `G` -/
  conj : ∀ (h : H) (b : A), h * ι b * h⁻¹ = ι (q h • b)
  /-- the Lie algebra of `Ĝ` is equivalent to `𝔞 ⊕_ω 𝔤`: an isomorphism of topological vector
  spaces `φ : 𝔞 × 𝔤 → L(Ĝ)` that is `dι` on `𝔞`, is a section-compatible lift of `dq`, and maps the
  bracket of `𝔞 ⊕_ω 𝔤` to the bracket of `L(Ĝ)` -/
  lie_alg : ∃ φ : (a × LieAlg E G) ≃L[ℝ] GroupLieAlgebra 𝓘(ℝ, a × E) H,
    (∀ v : a, (φ (v, 0) : a × E) = mfderiv 𝓘(ℝ, a) 𝓘(ℝ, a × E) ι (0 : A) v) ∧
    (∀ p : a × LieAlg E G,
      (mfderiv 𝓘(ℝ, a × E) 𝓘(ℝ, E) q (1 : H) (φ p) : E) = (p.2 : E)) ∧
    (∀ p p' : a × LieAlg E G,
      φ (bracketOmega A ω p p') = @Bracket.bracket _ _ _ (φ p) (φ p'))

attribute [instance] Extension.instTop Extension.instChart Extension.instGroup Extension.instLie

/-- `𝔞 ⊕_ω 𝔤` integrates to a Lie group extension `A ↪ Ĝ ↠ G`. -/
def IntegratesTo (qA : a →+ A) (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) : Prop :=
  Nonempty (Extension A qA ω)

/-- `𝔞 ⊕_ω 𝔤` integrates to a Lie group extension `A ↪ Ĝ ↠ G` with `Ĝ` connected. -/
def IntegratesToConnected (qA : a →+ A) (ω : LieAlg E G →L[ℝ] LieAlg E G →L[ℝ] a) : Prop :=
  ∃ X : Extension A qA ω, ConnectedSpace X.H

end Setting

end AbelianLieExt.Integrability


