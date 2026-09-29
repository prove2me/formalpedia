-- Prove2me | Definitions.Def_CerednikDrinfeld_QMRigidification
-- name    : CerednikDrinfeld_QMRigidification
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/8b143093-2a17-56f6-bcbf-90252940e4e4
-- title:
--   Rigidifications of fake elliptic curves and named-witness moduli predicates
-- statement:
--   Throughout, $\Lambda$ is a $\mathbb Z$-submodule of a rational quaternion algebra $\mathbb H[\mathbb Q,a,b]$ and $N$ a level; a `FakeEllipticCurve Λ N S` is the project's relative abelian surface over $S$ with commutative relative group law, two-dimensional fibres, a $\Lambda$-action by endomorphisms satisfying additivity, multiplicativity and the trace condition, and a finite flat level subscheme `lev` of rank $N^2$. The first group of declarations records the witnesses of three existential predicates: `IsoVia E E' i hi` says of an isomorphism $i$ of the underlying schemes over $S$ that it is additive on $T$-points, commutes with the $\Lambda$-action and matches the level subschemes in both directions, and `iso_iff_exists_via` states that `Iso` is exactly the existence of such a pair; similarly `IsAtkinLehnerQuotientVia` (a dual pair $\varphi,\psi$ with $\varphi\psi=\psi\varphi=[r]$, $\varphi$ level-preserving, and kernel of $\varphi$ described by annihilation under all $m\in\Lambda$ with $m\bar m\in r\mathbb Z$) and `IsLevelIsogenyVia` (the same shape, with $[\ell]$ and kernel exactly the extra level subgroup `levK`) together with the corresponding `iff` statements.
--
--   The main structure `Rigidification r π A₀ ψ E`, for $\pi\in\mathcal O$, an $\mathcal O$-algebra $O^{nr}$, a fake elliptic curve $A_0$ over $O^{nr}/(\pi)$, and $\psi:O^{nr}\to B$ of $\mathcal O$-algebras with $E$ over $B$, carries as data: a curve $E_b$ over $B/(\pi)$ together with a map $g_b$ certifying it as a pull-back of $E$ along $B\to B/(\pi)$; a curve $A_b$ over $B/(\pi)$ with $g_A$ certifying it as a pull-back of $A_0$ along the induced map $O^{nr}/(\pi)\to B/(\pi)$ (named `residueLeg`); an exponent $d$; and maps $\varphi:E_b\to A_b$, $\varphi'$ back, forming an isogeny pair of degree $r^d$ with $\varphi$ level-preserving. Since the reductions are data rather than chosen limits, `IsComparison` pins an identification of two presentations (pull-back along the identity ring map, compatible with $g_b$ and $g_A$), `Equiv` asks in addition for $u\varphi_1[r^i]=\varphi_2 u_A[r^j]$ for some $i,j$, and `IsTranslateBy eγ` inserts a lift $e\gamma_b$ of an endomorphism $e\gamma$ of $A_0$ into that equality; both take as argument a witness that every integer lies in $\Lambda$, used to form the scalars $[r^i]$. `Rigidification.IsPullbackVia` expresses functoriality in $B$: comparison maps of both reductions over $B/(\pi)\to B'/(\pi)$, compatibility with $g_b,g_A$, equality of exponents and commutation with $\varphi$. `IsRigTransport` relates a rigidification to the formal side: for $r$ prime it asserts the existence of a reduction map $\kappa_B:B/(\pi)\to B/\mathfrak p_r$ compatible with $\kappa$ and `residueLeg`, and of a two-variable power-series system $\sigma$ over $B/(\pi)$ which transports the formal coordinates $\theta_0$ of $A_0$ to those $\theta$ of $E$ through $\varphi'$ on nilpotent points, and whose reduction composed with $\beta_0$ and with $X_i\mapsto X_i^{r^j}$ is the given rigidification datum $t.\rho$ of the special formal module. Finally `RigidifiedCurve` is the type of pairs consisting of a fake elliptic curve over $B$ and a rigidification of it.
--
--   **Relation to Mathlib.** Mathlib has no fake elliptic curves, rigidifications or Čerednik–Drinfeld moduli predicates; these are the project's own notions, phrased on top of Mathlib's schemes, `CategoryTheory.IsPullback`, quotient rings and multivariate power series. Pull-backs appear as data with a certificate rather than through Mathlib's chosen limits.
--
--   **Where it is used.** These definitions belong to the Čerednik–Drinfeld description of the Shimura curve attached to an indefinite quaternion algebra near a prime of bad reduction: a rigidification compares the reduction of a fake elliptic curve with the fixed base curve $A_0$ up to an $r$-power isogeny, and `IsRigTransport` links this comparison with the rigidified special formal modules used for the $p$-adic uniformisation. The named-witness forms of `Iso`, `IsAtkinLehnerQuotient` and `IsLevelIsogeny` are the working shapes of those moduli relations in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMRigidification.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def IsoVia {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt i.hom hi (E.L.mul t P Q) = E'.L.mul t (mapPt i.hom hi P) (mapPt i.hom hi Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ i.hom = i.hom ≫ E'.act x) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt i.hom hi P))

theorem iso_iff_exists_via {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S) :
    Iso E E' ↔ ∃ (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f), IsoVia E E' i hi := Iff.rfl

def IsAtkinLehnerQuotientVia {S : Type} [CommRing S] (r : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧ (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧ ψ ≫ φ = E'.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E'.L.one t ↔
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (E.act m) (E.act_over m) P = E.L.one t) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P))

theorem isAtkinLehnerQuotient_iff_exists_via {S : Type} [CommRing S] (r : ℕ) (E E' : FakeEllipticCurve Λ N S) :
    IsAtkinLehnerQuotient r E E' ↔ ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f),
      IsAtkinLehnerQuotientVia r E E' φ hφ ψ hψ := Iff.rfl

def IsLevelIsogenyVia {S : Type} [CommRing S] (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S)
    (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = d.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t d.f),
      mapPt ψ hψ (d.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ d.act x) ∧ (∀ x : ↥Λ, d.act x ≫ ψ = ψ ≫ u.1.act x) ∧
    (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = u.1.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = d.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = d.L.one t ↔ FactorsThrough u.2.levK P) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough d.lev (mapPt φ hφ P))

theorem isLevelIsogeny_iff_exists_via {S : Type} [CommRing S] (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S) :
    IsLevelIsogeny ℓ u d ↔ ∃ (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = d.f),
      IsLevelIsogenyVia ℓ u d φ hφ ψ hψ := Iff.rfl

structure Rigidification (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B) : Type 1 where

  Eb : FakeEllipticCurve Λ N (B ⧸ Ideal.span {algebraMap 𝒪 B π})

  gb : Eb.A ⟶ E.A

  isPullback_Eb : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E Eb gb

  Ab : FakeEllipticCurve Λ N (B ⧸ Ideal.span {algebraMap 𝒪 B π})

  gA : Ab.A ⟶ A₀.A

  isPullback_Ab : FakeEllipticCurve.IsPullbackVia
    (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B π}) (ψ : Onr →+* B)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (ψ : Onr →+* B) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 B π from ψ.commutes π]
            exact Ideal.subset_span rfl)))))
    A₀ Ab gA

  d : ℕ

  φ : Eb.A ⟶ Ab.A

  φ' : Ab.A ⟶ Eb.A

  φ_over : φ ≫ Ab.f = Eb.f

  isIsogenyPair : FakeEllipticCurve.IsIsogenyPair (r ^ d) Eb Ab φ φ'

  preservesLevel : FakeEllipticCurve.PreservesLevel Eb Ab φ φ_over

namespace Rigidification

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

def IsComparison (ρ₁ ρ₂ : Rigidification r π A₀ ψ E) (u : ρ₂.Eb.A ⟶ ρ₁.Eb.A) (uA : ρ₂.Ab.A ⟶ ρ₁.Ab.A) : Prop :=
  FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₁.Eb ρ₂.Eb u ∧ u ≫ ρ₁.gb = ρ₂.gb ∧
  FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₁.Ab ρ₂.Ab uA ∧ uA ≫ ρ₁.gA = ρ₂.gA

def Equiv (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (ρ₁ ρ₂ : Rigidification r π A₀ ψ E) : Prop :=
  ∃ (u : ρ₂.Eb.A ⟶ ρ₁.Eb.A) (uA : ρ₂.Ab.A ⟶ ρ₁.Ab.A), IsComparison ρ₁ ρ₂ u uA ∧
    ∃ i j : ℕ, u ≫ ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩

def IsTranslateBy (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (eγ : A₀.A ⟶ A₀.A) (ρ₁ ρ₂ : Rigidification r π A₀ ψ E) : Prop :=
  ∃ (u : ρ₂.Eb.A ⟶ ρ₁.Eb.A) (uA : ρ₂.Ab.A ⟶ ρ₁.Ab.A), IsComparison ρ₁ ρ₂ u uA ∧
    ∃ (eγb : ρ₁.Ab.A ⟶ ρ₁.Ab.A), eγb ≫ ρ₁.gA = ρ₁.gA ≫ eγ ∧ eγb ≫ ρ₁.Ab.f = ρ₁.Ab.f ∧
      ∃ i j : ℕ, u ≫ ρ₁.φ ≫ eγb ≫ ρ₁.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩

def IsPullbackVia {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {E' : FakeEllipticCurve Λ N B'} (g : E'.A ⟶ E.A) (_hE' : FakeEllipticCurve.IsPullbackVia (f : B →+* B') E E' g)
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ (f.comp ψ) E') : Prop :=
  ∃ (ub : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A),
    FakeEllipticCurve.IsPullbackVia
        (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (f : B →+* B')
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (f : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from f.commutes π]
                exact Ideal.subset_span rfl)))))
        ρ.Eb ρ'.Eb ub ∧
      ub ≫ ρ.gb = ρ'.gb ≫ g ∧
    FakeEllipticCurve.IsPullbackVia
        (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (f : B →+* B')
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (f : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from f.commutes π]
                exact Ideal.subset_span rfl)))))
        ρ.Ab ρ'.Ab uA ∧
      uA ≫ ρ.gA = ρ'.gA ∧
    ρ'.d = ρ.d ∧ ub ≫ ρ.φ = ρ'.φ ≫ uA

abbrev residueLeg {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) :
    (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (B ⧸ Ideal.span {algebraMap 𝒪 B π}) :=
  Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B π}) (ψ : Onr →+* B)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
      (by rw [show (ψ : Onr →+* B) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 B π from ψ.commutes π]
          exact Ideal.subset_span rfl))))

def IsRigTransport {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    (θ₀ : GoodReductionJacobian.RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r Onr))
    (β₀ : CerednikDrinfeld.SpecialFormal.Series (Onr ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r Onr))
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ρ : Rigidification r π A₀ ψ E) (θ : GoodReductionJacobian.RelativeGroupLaw.FormalCoordinates E.f 2) (j : ℕ)
    {Φ : CerednikDrinfeld.FormalODModule r (Onr ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r Onr)}
    (t : CerednikDrinfeld.SpecialFormal.Rigidified r Φ B) : Prop :=
  ∃ (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B))
    (σ : CerednikDrinfeld.SpecialFormal.Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})),

    κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal r B) ∧
    κB.comp (residueLeg π ψ) = (CerednikDrinfeld.SpecialFormal.residueMap (ψ : Onr →+* B)).comp κ ∧

    (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1) ∧

    t.ρ = (CerednikDrinfeld.SpecialFormal.Series.map κB σ).comp
      ((CerednikDrinfeld.SpecialFormal.Series.map (CerednikDrinfeld.SpecialFormal.residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B)) ^ (r ^ j)))

end Rigidification

abbrev RigidifiedCurve (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : Type 1 :=
  Σ E : FakeEllipticCurve Λ N B, Rigidification r π A₀ ψ E

end CerednikDrinfeld.QM.FakeEllipticCurve


