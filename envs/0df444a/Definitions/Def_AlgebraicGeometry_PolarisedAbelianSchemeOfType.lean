-- Prove2me | Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
-- name    : AlgebraicGeometry_PolarisedAbelianSchemeOfType
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/a41c6c51-a5be-5bdf-9f1c-884a1b28cf51
-- title:
--   Polarised abelian schemes of a given theta type
-- statement:
--   Throughout, $f : A \to \operatorname{Spec} S$ is a scheme over an affine base equipped with a relative group law $L$, and for modules the tensor product is that of the monoidal category $X.\mathrm{Modules}$. `Scheme.Modules.tpow M n` is the naive $n$-fold tensor power, with $\mathrm{tpow}\,M\,0$ the unit module and $\mathrm{tpow}\,M\,(n+1) = \mathrm{tpow}\,M\,n \otimes M$. `Polarisation.MemKernel 𝓛 t x` expresses membership of a point in the kernel of an invertible module: for a ring $R$, a morphism $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and a point $x$ of $A$ over $t$, it asserts that the pullback of the Mumford bundle $\Lambda(\mathcal L)$ along the slice $\mathrm{sliceAt}\,f\,x : A \times_S \operatorname{Spec} R \to A \times_S A$ is isomorphic to the unit module locally on the base $\operatorname{Spec} R$, in the sense of `LocIsoOnBase` (each point of the base has an open neighbourhood over whose preimage the two modules become isomorphic).
--
--   `typeGroup δ`, for $\delta : \mathrm{Fin}\,g \to \mathbb N$, is the finite abelian group $\bigl(\prod_i \mathbb Z/\delta_i\bigr) \times \bigl(\prod_i \mathbb Z/\delta_i\bigr)$. `IsOfType δ u`, for a polarised abelian scheme $u$ over $S$, asserts the existence of a faithfully flat étale $S$-algebra $S'$ together with a family $(x_h)_{h \in \mathrm{typeGroup}\,\delta}$ of $S'$-points of $A$ such that: $h \mapsto x_h$ is a homomorphism into the group of points ($x_0$ is the unit, $x_{h+h'} = x_h \cdot x_{h'}$); the $x_h$ remain pairwise distinct after composing with any morphism $\operatorname{Spec} k \to \operatorname{Spec} S'$ coming from a ring homomorphism $S' \to k$ into an algebraically closed field; and for every $S'$-algebra $R$ and every point $y$ of $A$ over $\operatorname{Spec} R \to \operatorname{Spec} S$, the condition `MemKernel` for $u.\mathrm{pol}$ holds at $y$ if and only if there are finitely many elements $r_1,\dots,r_m$ of $R$ generating the unit ideal such that over each $R[1/r_j]$ the point $y$ agrees with the base change of some $x_h$. So the kernel of the polarisation is, after one affine étale faithfully flat cover and Zariski-locally on test rings, the constant group of type $\delta$.
--
--   `HasPrincipalRoot u` asserts the existence of a faithfully flat $S$-algebra $S'$ such that for *every* relative group law $L'$ on the base change $A \times_S \operatorname{Spec} S' \to \operatorname{Spec} S'$ whose multiplication is carried by the first projection to that of $u.L$, there are an invertible module $\mathcal L_0$ on $A \times_S \operatorname{Spec} S'$ with trivial kernel (`Polarisation.KernelTrivial` for $L'$) and natural numbers $a,b$ with $1 \le a+b$ such that the pullback of $u.\mathrm{pol}$ along the first projection is isomorphic, locally on $\operatorname{Spec} S'$, to $\mathcal L_0^{\otimes a} \otimes ([-1]^{*}\mathcal L_0)^{\otimes b}$, where $[-1]$ is the inversion morphism `Polarisation.negMor` of $L'$. Note the universal quantifier over the compatible group law $L'$, rather than a choice of one.
--
--   `Satisfying g d n Q S` packages a polarised abelian scheme together with a proof of a property $Q$ of it; `Satisfying.Iso` and `Satisfying.IsPullback` are the corresponding relations on the underlying polarised abelian schemes, so the property is forgotten by them. `Satisfying.IsFineModuli` is a property, in the shape of a structure with four fields, of a scheme $M$ over $\operatorname{Spec} B$ and an assignment `pt` sending each $B$-algebra point $s$ of the base and each $Q$-satisfying object over $S$ to a point of $M$ over $s$: the assignment is constant on isomorphism classes, is compatible with base change along ring homomorphisms, is surjective on such points, and separates non-isomorphic objects. Finally `RootedSymmetricOfType δ` is the conjunction of `Polarisation.IsSymmetric` for $(u.f, u.L, u.\mathrm{pol})$, `IsOfType δ u` and `HasPrincipalRoot u`.
--
--   **Relation to Mathlib.** Mathlib has no abelian schemes, polarisations, kernels of line bundles or moduli problems for them; these are the project's own notions, built on Mathlib's `Module.FaithfullyFlat` and `Algebra.Etale` for the covers and on the project's monoidal structure on the category of modules over a scheme for tensor products and duals.
--
--   **Where it is used.** These predicates isolate the moduli problem used on the theta-function route to a fine moduli scheme: objects are polarised abelian schemes with level structure whose polarisation is symmetric, has kernel étale-locally constant of type $\delta$, and is a monomial in a bundle with trivial kernel. The resulting moduli scheme is what the quaternionic (Čerednik–Drinfeld) part of the argument consumes, with `IsOfType` verified there for tensor powers of a fixed polarisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace Scheme.Modules

def tpow {X : Scheme.{u}} (M : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tpow M n ⊗ M

end Scheme.Modules

namespace Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

def MemKernel (𝓛 : A.Modules) {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f) : Prop :=
  LocIsoOnBase (pullback.snd f t)
    ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules))

end Polarisation

namespace PolarisedAbelianScheme

abbrev typeGroup {g : ℕ} (δ : Fin g → ℕ) : Type := ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))

variable {g d n : ℕ}

def IsOfType (δ : Fin g → ℕ) {S : Type u} [CommRing S] (u : PolarisedAbelianScheme g d n S) : Prop :=
  ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S') (_ : Module.FaithfullyFlat S S') (_ : Algebra.Etale S S')
    (x : typeGroup δ → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) u.f),
    (x 0 = u.L.one _ ∧ ∀ h h' : typeGroup δ, x (h + h') = u.L.mul _ (x h) (x h')) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S' →+* k) (h h' : typeGroup δ),
      Spec.map (CommRingCat.ofHom sk) ≫ (x h).1 = Spec.map (CommRingCat.ofHom sk) ≫ (x h').1 → h = h') ∧
    (∀ (R : Type u) [CommRing R] [Algebra S' R]
      (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) u.f),
      Polarisation.MemKernel u.f u.L u.pol _ y ↔
        ∃ (m : ℕ) (r : Fin m → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ h : typeGroup δ,
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ y.1 =
            Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away (r j))).comp (algebraMap S' R))) ≫ (x h).1)

def HasPrincipalRoot {S : Type u} [CommRing S] (u : PolarisedAbelianScheme g d n S) : Prop :=
  ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
    Module.FaithfullyFlat S S' ∧
    ∀ (L' : RelativeGroupLaw S' (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'))
          (P Q : SchemeHomOver t' (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
          (L'.mul t' P Q).1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
            (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
              ⟨P.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
      ∃ (𝓛₀ : (pullback u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules) (a b : ℕ),
        1 ≤ a + b ∧ Scheme.Modules.IsInvertible 𝓛₀ ∧
        Polarisation.KernelTrivial (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L' 𝓛₀ ∧
        Polarisation.LocIsoOnBase (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
          ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj u.pol)
          (Scheme.Modules.tpow 𝓛₀ a ⊗
            Scheme.Modules.tpow ((Scheme.Modules.pullback
              (Polarisation.negMor (pullback.snd u.f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₀) b)

structure Satisfying (g d n : ℕ) (Q : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    (S : Type u) [CommRing S] where

  val : PolarisedAbelianScheme g d n S

  prop : Q S val

namespace Satisfying

variable {Q : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop}

def Iso {S : Type u} [CommRing S] (X X' : Satisfying g d n Q S) : Prop :=
  PolarisedAbelianScheme.Iso X.val X'.val

def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : Satisfying g d n Q S) (X' : Satisfying g d n Q S') : Prop :=
  PolarisedAbelianScheme.IsPullback φ X.val X'.val

structure IsFineModuli (g d n : ℕ) (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    {B : Type} [CommRing B] (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      Satisfying g d n Q S → SchemeHomOver s πM) : Prop where

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : Satisfying g d n Q S), Iso X X' → pt S s X = pt S s X'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (X : Satisfying g d n Q S) (X' : Satisfying g d n Q S'),
    IsPullback φ X X' → (pt S' s' X').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s X).1

  pt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πM),
    ∃ X : Satisfying g d n Q S, pt S s X = x

  pt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : Satisfying g d n Q S), pt S s X = pt S s X' → Iso X X'

end Satisfying

abbrev RootedSymmetricOfType (δ : Fin g → ℕ) : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop :=
  fun _ _ u => Polarisation.IsSymmetric u.f u.L u.pol ∧ IsOfType δ u ∧ HasPrincipalRoot u

end PolarisedAbelianScheme

end AlgebraicGeometry

end


