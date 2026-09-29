-- Prove2me | Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
-- name    : AlgebraicGeometry_PolarisedAbelianScheme
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/c707a4eb-0236-58e6-be8f-5750c5c38979
-- title:
--   Polarised abelian schemes with level structure; fine moduli
-- statement:
--   Throughout, $S$ is a commutative ring and schemes are over $\operatorname{Spec} S$. Two helpers come first. [`GoodReductionJacobian.RelativeGroupLaw.finComb`](../def/AlgebraicGeometry_PolarisedAbelianScheme.html#L17) takes a relative group law $L$ on $f : A \to \operatorname{Spec} S$ (a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of $T$-points over a base morphism $t$), a family $x : \mathrm{Fin}\,m \to A(T)$ and exponents $c : \mathrm{Fin}\,m \to \mathbb{N}$, and returns the product $\prod_i x_i^{c_i}$ formed in the group of $T$-points. [`AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank`](../def/AlgebraicGeometry_PolarisedAbelianScheme.html#L27) assigns to $f$, a sheaf of modules $M$ on $A$, a field $k$ and a ring homomorphism $sk : S \to k$ the $k$-dimension $\dim_k \Gamma(A \times_S \operatorname{Spec} k,\ M_k)$, the $k$-structure coming from the projection to $\operatorname{Spec} k$.
--
--   The structure `PolarisedAbelianScheme g d n S` bundles: a scheme $A$ with $f : A \to \operatorname{Spec} S$; a relative group law $L$ on $f$ together with its commutativity; the bundle `AbelianSchemePropertyBundle` ($f$ smooth, proper, with connected fibres, and admitting a relative group law); the requirement that each fibre $f^{-1}(s)$ have topological Krull dimension $g$; sections $P_1,\dots,P_{2g} \in A(S)$ with $n \cdot P_i$ equal to the identity point, where $n\cdot$ means the $n$-fold iterate of the group law; and, for every algebraically closed field $k$ and every $sk : S \to k$, the injectivity on tuples $c \in (\mathrm{Fin}\,n)^{2g}$ and the surjectivity onto the $n$-torsion of $A_k$ of $c \mapsto \prod_i P_{i,k}^{c_i}$ — a full level-$n$ structure stated geometric-fibrewise. Finally a module $\mathcal{L}$ on $A$ which is invertible (locally isomorphic to the unit sheaf of modules), which admits a presentation by $N+1$ global sections framing $\mathcal{L}$ over the standard charts and matching under the coordinate ratios, whose associated morphism $A \to \mathbb{P}^N_S$ over $\operatorname{Spec} S$ is a closed immersion, and whose geometric-fibre $h^0$ equals $d$.
--
--   `Iso` is the predicate that there is an isomorphism $e : A \cong A'$ over $\operatorname{Spec} S$, a homomorphism on $T$-points for all $T$, carrying $P_i$ to $P'_i$, and identifying $e^*\mathcal{L}'$ with $\mathcal{L}$ only locally on the base: each point of $\operatorname{Spec} S$ has a neighbourhood $U$ over which the restrictions to $f^{-1}U$ are isomorphic. `IsPullback φ u u'`, for $\varphi : S \to S'$, asserts a morphism $A' \to A$ making a pullback square over $\operatorname{Spec}\varphi$, compatible with the group laws, carrying $P'_i$ to the base change of $P_i$, and with an isomorphism of the pulled-back polarisation with $\mathcal{L}'$ (here a genuine isomorphism, not a local one). `IsFineModuli g d n M πM pt` is a Prop-valued structure recording that an assignment $pt$, sending a polarised abelian scheme over $S$ with $s : \operatorname{Spec} S \to \operatorname{Spec} B$ to an $S$-point of $M$ over $s$, is constant on `Iso`-classes, compatible with base change, surjective onto such points, and injective up to `Iso`: representability of the moduli problem tested on affine schemes, with no sheafification step.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — sheaves of modules on a scheme and their pullbacks, smoothness, properness, closed immersions, `Proj` of a graded ring and `topologicalKrullDim` — but has no abelian schemes, polarisations, level structures or moduli spaces; the structures and predicates of this module, together with invertibility and presentation by sections from the imported modules, are the project's own. The polarisation is an invertible sheaf taken modulo the base rather than an isogeny to a dual abelian scheme, so no dual abelian scheme is needed.
--
--   **Where it is used.** These definitions supply the moduli-theoretic input for the representability statement for polarised abelian schemes with full level structure, and hence for the treatment of fake elliptic curves and the Shimura-curve models entering the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_PolarisedAbelianScheme.lean

import Mathlib.Topology.KrullDimension
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GoodReductionJacobian.RelativeGroupLaw

def finComb {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) {m : ℕ}
    (x : Fin m → SchemeHomOver t f) (c : Fin m → ℕ) : SchemeHomOver t f :=
  letI := L.pointGroup t
  (List.ofFn fun i => x i ^ c i).prod

end GoodReductionJacobian.RelativeGroupLaw

namespace AlgebraicGeometry

def Scheme.Modules.geomFibreH0Finrank {S : Type u} [CommRing S] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (M : A.Modules) (k : Type u) [Field k] (sk : S →+* k) : ℕ :=
  letI : Algebra k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤) :=
    Module.compHom _ (algebraMap k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤))
  Module.finrank k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤)

structure PolarisedAbelianScheme (g d n : ℕ) (S : Type u) [CommRing S] : Type (u + 1) where

  A : Scheme.{u}

  f : A ⟶ Spec (CommRingCat.of S)

  L : RelativeGroupLaw S f

  comm : L.IsCommutative

  bundle : AbelianSchemePropertyBundle S f

  dim_fibre : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g

  P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f

  P_torsion : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of S)))

  P_indep : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c c' : Fin (2 * g) → Fin n),
    L.finComb (Spec.map (CommRingCat.ofHom sk))
        (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) =
      L.finComb (Spec.map (CommRingCat.ofHom sk))
        (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c' i : ℕ)) →
      c = c'

  P_span : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f),
    L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
      ∃ c : Fin (2 * g) → Fin n,
        L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q

  pol : A.Modules

  pol_isInvertible : Scheme.Modules.IsInvertible pol

  pol_veryAmple : Scheme.Modules.ClosedImmersionBySections pol f

  pol_finrank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), Scheme.Modules.geomFibreH0Finrank f pol k sk = d

namespace PolarisedAbelianScheme

variable {g d n : ℕ}

def Iso {S : Type u} [CommRing S] (u u' : PolarisedAbelianScheme g d n S) : Prop :=
  ∃ (e : u.A ≅ u'.A) (he : e.hom ≫ u'.f = u.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.f),
      (u.L.mul t x y).1 ≫ e.hom =
        (u'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ i, (u.P i).1 ≫ e.hom = (u'.P i).1) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj u'.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol))

def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S') : Prop :=
  ∃ (gA : u'.A ⟶ u.A) (hg : CategoryTheory.IsPullback gA u'.f u.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
    (∀ i, (u'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj u.pol ≅ u'.pol)

structure IsFineModuli (g d n : ℕ) {B : Type} [CommRing B]
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      PolarisedAbelianScheme g d n S → SchemeHomOver s πM) : Prop where

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : PolarisedAbelianScheme g d n S), Iso u u' → pt S s u = pt S s u'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
    IsPullback φ u u' → (pt S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s u).1

  pt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πM),
    ∃ u : PolarisedAbelianScheme g d n S, pt S s u = x

  pt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : PolarisedAbelianScheme g d n S), pt S s u = pt S s u' → Iso u u'

end PolarisedAbelianScheme

end AlgebraicGeometry

end


