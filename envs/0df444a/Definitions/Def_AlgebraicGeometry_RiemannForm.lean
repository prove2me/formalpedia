-- Prove2me | Definitions.Def_AlgebraicGeometry_RiemannForm
-- name    : AlgebraicGeometry_RiemannForm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a433af35-927f-5c6f-9ef8-4bf128b7731c
-- title:
--   Riemann forms on Tate modules of relative group laws
-- statement:
--   Throughout, $k$ is a field, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} k$, $L$ a `RelativeGroupLaw` on $f$ and, for the last definition, $hc$ a witness that $L$ is commutative. A point of $A$ is taken in the spelling used for `AlgPoints`: `Pt f` is the type of morphisms $A$-wards over $\operatorname{Spec}$ of the structure map $k \to k$; since that map induces the identity of $\operatorname{Spec} k$ (`specMap_algebraMap_self`), `toUnitPt` and `ofUnitPt` exchange this spelling with sections over $\mathbb{1}_{\operatorname{Spec} k}$, mutually inversely and without changing the underlying morphism. For $x \in$ `Pt f`, `constPt` is the constant $A$-valued point $x \circ f$, and `translation f L x` is the first component of the $L$-product of the identity point of $A$ with that constant point; `translation_over` records that it is a morphism over $f$. For $T$ with $T \circ g = g$ and an $\mathcal{O}_A$-module $M$, `transportIso` is the resulting isomorphism $T^{*}g^{*}M \cong g^{*}M$. Next, `IsConstScalar` says of an endomorphism $\sigma$ of an $\mathcal{O}_A$-module $M$ and of $c \in k$ that on every open $U$ and every $s \in \Gamma(M,U)$ one has $\sigma_U(s) = (f^{\sharp}c)|_U \cdot s$. The level pairing is then a predicate rather than a function: `IsLevelPairingValue 𝓛 n x y c` asserts the existence of a proof that $T_x$ followed by $[n]$ equals $[n]$ and of an isomorphism $\beta : [n]^{*}T_y^{*}\mathcal{L} \cong [n]^{*}\mathcal{L}$ such that the automorphism of $[n]^{*}\mathcal{L}$ obtained from $\beta^{-1}$, $T_x^{*}\beta$ and the two transport isomorphisms is multiplication by the constant $c$. Finally, for a prime $\ell$, a sequence $\zeta : \mathbb{N} \to k$ and a $\mathbb{Z}_\ell$-bilinear $e$ on the Tate module of $L.\mathrm{AlgPoints}\,hc\,k$, `IsRiemannForm` asserts that for all $n$ and all $a,b$ the level-$\ell^n$ pairing of the $n$-th components of $a$ and $b$ takes the value $\zeta_n$ raised to the $n$-th $\ell$-adic approximant of $e(a,b)$. No existence, uniqueness, root-of-unity or alternating property is asserted here.
--
--   **Relation to Mathlib.** Mathlib has no notion of a Riemann form or Weil pairing on a group scheme; these predicates are the project's own, phrased for its `RelativeGroupLaw` group laws, its [`TateModule`](../def/EllipticCurve_TateModule.html#L15), and pullback of sheaves of modules along morphisms of schemes.
--
--   **Where it is used.** The Tate module used here is the one that, for Weierstrass curves over $\mathbb{Q}$, carries the $\ell$-adic Galois representation attached to an elliptic curve; this module supplies the scheme-theoretic pairing on such Tate modules, formulated without tensor products of sheaves or a dual abelian variety.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RiemannForm.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RiemannForm

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

theorem specMap_algebraMap_self :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) :=
  Spec.map_id _

abbrev Pt : Type := SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) f

def toUnitPt (x : Pt f) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
  ⟨x.1, by rw [x.2, specMap_algebraMap_self]⟩

def ofUnitPt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : Pt f :=
  ⟨x.1, by rw [x.2, specMap_algebraMap_self]⟩

@[simp] theorem toUnitPt_coe (x : Pt f) : (toUnitPt f x).1 = x.1 := rfl
@[simp] theorem ofUnitPt_coe (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : (ofUnitPt f x).1 = x.1 := rfl
@[simp] theorem ofUnitPt_toUnitPt (x : Pt f) : ofUnitPt f (toUnitPt f x) = x := Subtype.ext rfl
@[simp] theorem toUnitPt_ofUnitPt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    toUnitPt f (ofUnitPt f x) = x := Subtype.ext rfl

def constPt (x : Pt f) : SchemeHomOver f f :=
  ⟨f ≫ x.1, by rw [Category.assoc, x.2, specMap_algebraMap_self, Category.comp_id]⟩

variable (L : RelativeGroupLaw k f)

def translation (x : Pt f) : A ⟶ A :=
  (L.mul f RelativeGroupLaw.idPoint (constPt f x)).1

theorem translation_over (x : Pt f) : translation f L x ≫ f = f :=
  (L.mul f RelativeGroupLaw.idPoint (constPt f x)).2

def transportIso {T g : A ⟶ A} (h : T ≫ g = g) (M : A.Modules) :
    (Scheme.Modules.pullback T).obj ((Scheme.Modules.pullback g).obj M) ≅ (Scheme.Modules.pullback g).obj M :=
  (Scheme.Modules.pullbackComp T g).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

def IsConstScalar {M : A.Modules} (σ : M ⟶ M) (c : k) : Prop :=
  ∀ (U : A.Opens) (s : Γ(M, U)),
    σ.app U s = (A.presheaf.map (homOfLE (le_top (a := U))).op (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) • s

def IsLevelPairingValue (𝓛 : A.Modules) (n : ℕ) (x y : Pt f) (c : k) : Prop :=
  ∃ (hx : translation f L x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (β : (Scheme.Modules.pullback (L.schemeNsmul n)).obj ((Scheme.Modules.pullback (translation f L y)).obj 𝓛) ≅
      (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
    IsConstScalar f
      (β.symm ≪≫ (transportIso hx ((Scheme.Modules.pullback (translation f L y)).obj 𝓛)).symm ≪≫
        (Scheme.Modules.pullback (translation f L x)).mapIso β ≪≫ transportIso hx 𝓛).hom c

variable (hc : L.IsCommutative)

def IsRiemannForm (𝓛 : A.Modules) (ℓ : ℕ) [Fact ℓ.Prime] (ζ : ℕ → k)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) : Prop :=
  ∀ (n : ℕ) (a b : TateModule ℓ (L.AlgPoints hc k)),
    IsLevelPairingValue f L 𝓛 (ℓ ^ n)
      (RelativeGroupLaw.AlgPoints.toPoint ((a : ℕ → L.AlgPoints hc k) n))
      (RelativeGroupLaw.AlgPoints.toPoint ((b : ℕ → L.AlgPoints hc k) n))
      (ζ n ^ (e a b).appr n)

end AlgebraicGeometry.RiemannForm

end


