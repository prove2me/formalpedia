-- Prove2me | Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
-- name    : AlgebraicGeometry_FramedPolarisedAbelianScheme
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f19a8e5e-0460-5d0f-b3da-ef4239724df4
-- title:
--   Framed polarised abelian schemes and their fine moduli
-- statement:
--   Over a commutative ring $S$, the auxiliary predicate `IsSectionBasisOn` says, for a morphism $f : X \to \operatorname{Spec} S$, a sheaf of modules $M$ on $X$, an open $V \subseteq X$ and sections $\sigma_0,\dots,\sigma_{m-1} \in \Gamma(M,V)$, that the map $S^{m} \to \Gamma(M,V)$, $c \mapsto \sum_i f^{\#}(c_i)\,\sigma_i$ (scalars transported along $S \cong \Gamma(\operatorname{Spec} S,\top)$ and then restricted to $V$ by $f$) is bijective; `IsSectionBasis` is the case $V = \top$.
--
--   The structure `FramedPolarisedAbelianScheme g N n S` extends `PolarisedAbelianScheme g (N+1) n S` — an $S$-scheme $A$ with relative group law, commutativity, the abelian-scheme property bundle, fibres of topological Krull dimension $g$, $2g$ sections $P_i$ of $n$-torsion which are independent of order $n$ and span the $n$-torsion on geometric fibres, and an invertible $\mathcal L =$ `pol` giving a closed immersion by sections with geometric fibrewise $h^0 = N+1$ — by three further fields: a `ProjPresentation` of $\mathcal L$ relative to $f$ of size $N$ (sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal L,\top)$, a morphism $\iota : A \to \mathbb P^N_S$ over $\operatorname{Spec} S$ such that $\sigma_i$ frames $\mathcal L$ over $\iota^{-1}D_+(x_i)$ and $x_j/x_i$ pulls back to the ratio $\sigma_j/\sigma_i$), the requirement that $\iota$ be a closed immersion, and the requirement that $\sigma_0,\dots,\sigma_N$ be an $S$-basis of $\Gamma(\mathcal L,\top)$ in the above sense.
--
--   `Iso X X'` asks for an isomorphism $e : A \cong A'$ over $S$ with $\iota = e$ followed by $\iota'$, compatible with the group laws on $T$-points, carrying each $P_i$ to $P_i'$, and such that $e^{*}\mathcal L'$ and $\mathcal L$ become isomorphic after restriction to $f^{-1}U$ for some open $U$ around each point of the base — a local-on-the-base condition, not a global isomorphism of line bundles. `IsPullback φ X X'`, for $\varphi : S \to S'$, asks for $g_A : A' \to A$ making a cartesian square over $\operatorname{Spec}\varphi$, compatible with the group laws, with $(P_i')$ the base change of $(P_i)$, with $g_A^{*}\mathcal L \cong \mathcal L'$ (globally), and with $\iota'$ followed by $\mathbb P^N_{S'} \to \mathbb P^N_S$ equal to $g_A$ followed by $\iota$. Finally `IsFineModuli g N n H πH pt`, for a scheme $H$ over $\operatorname{Spec} B$ and an assignment `pt` sending each framed object over $S$ and each $s : \operatorname{Spec} S \to \operatorname{Spec} B$ to a morphism $\operatorname{Spec} S \to H$ over $s$, records four properties: `pt` is constant on isomorphism classes, turns pullbacks along $\varphi$ into precomposition with $\operatorname{Spec}\varphi$, is surjective onto such morphisms, and is injective up to `Iso`. It is thus phrased as the bijectivity, for each $S$ and each $s$, between isomorphism classes of framed objects and $S$-points of $H$ over $s$, with the same field layout as `PolarisedAbelianScheme.IsFineModuli`.
--
--   **Relation to Mathlib.** Mathlib has no notion of abelian scheme, polarisation, projective-space presentation of a sheaf of modules, or fine moduli space; these are the project's own definitions, layered on Mathlib's `Proj` of a graded ring, sheaves of modules on schemes, and the morphism classes `Smooth`, `IsProper`, `IsClosedImmersion`.
--
--   **Where it is used.** The framed objects are the rigidified version of the polarised abelian schemes of the companion definition module: adding a basis of $\Gamma(A,\mathcal L)$ presenting the embedding $A \hookrightarrow \mathbb P^N_S$ makes the moduli problem rigid, and a fine moduli space $H$ for it is the input from which a moduli space for unframed polarised abelian schemes is obtained by passing to a quotient. This sits in the geometric infrastructure for Jacobians of modular curves and their reduction used on the modularity side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FramedPolarisedAbelianScheme.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

namespace Scheme.Modules

def IsSectionBasisOn {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    (V : X.Opens) {m : ℕ} (σ : Fin m → Γ(M, V)) : Prop :=
  Function.Bijective fun c : Fin m → S =>
    ∑ i, ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c i))) • σ i

abbrev IsSectionBasis {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    {m : ℕ} (σ : Fin m → Γ(M, ⊤)) : Prop :=
  IsSectionBasisOn f M ⊤ σ

end Scheme.Modules

structure FramedPolarisedAbelianScheme (g N n : ℕ) (S : Type u) [CommRing S]
    extends PolarisedAbelianScheme g (N + 1) n S where

  frame : Scheme.Modules.ProjPresentation pol f N

  frame_isClosedImmersion : IsClosedImmersion frame.toProj

  frame_basis : Scheme.Modules.IsSectionBasis f pol frame.σ

namespace FramedPolarisedAbelianScheme

variable {g N n : ℕ}

def Iso {S : Type u} [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S) : Prop :=
  ∃ (e : X.A ≅ X'.A) (he : e.hom ≫ X'.f = X.f),
    e.hom ≫ X'.frame.toProj = X.frame.toProj ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t X.f),
      (X.L.mul t x y).1 ≫ e.hom =
        (X'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ i, (X.P i).1 ≫ e.hom = (X'.P i).1) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj X'.pol) ≅
        (Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj X.pol))

def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S') : Prop :=
  letI : Algebra S S' := φ.toAlgebra
  ∃ (gA : X'.A ⟶ X.A) (hg : CategoryTheory.IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' X'.f),
      (X'.L.mul t' x y).1 ≫ gA =
        (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
    (∀ i, (X'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj X.pol ≅ X'.pol) ∧
    X'.frame.toProj ≫ ProjSpace.map S S' N = gA ≫ X.frame.toProj

structure IsFineModuli (g N n : ℕ) {B : Type} [CommRing B]
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FramedPolarisedAbelianScheme g N n S → SchemeHomOver s πH) : Prop where

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : FramedPolarisedAbelianScheme g N n S), Iso X X' → pt S s X = pt S s X'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
    IsPullback φ X X' → (pt S' s' X').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s X).1

  pt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πH),
    ∃ X : FramedPolarisedAbelianScheme g N n S, pt S s X = x

  pt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : FramedPolarisedAbelianScheme g N n S), pt S s X = pt S s X' → Iso X X'

end FramedPolarisedAbelianScheme

end AlgebraicGeometry

end


