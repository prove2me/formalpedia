-- Prove2me | Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
-- name    : CerednikDrinfeld_RigidifiedPairClassModel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/af711087-03f7-5261-807b-d83b29b60fdb
-- title:
--   Presented points and the rigidified pair class functor
-- statement:
--   Over a commutative ring $C$ with a distinguished element $\pi_C$, a morphism $g : M_C \to \operatorname{Spec} C$ and a family of schemes $\xi_d : X_d \to M_C$ indexed by $d \in \mathbb{N}$, the structure `Pt` packages, for a $C$-algebra $T$, a triple: a morphism $t : \operatorname{Spec} T \to M_C$ with $t$ followed by $g$ equal to $\operatorname{Spec}$ of the structure map $C \to T$; a natural number $d$; and a morphism $x : \operatorname{Spec}(T/\pi_C T) \to X_d$ whose composite with $\xi_d$ is the reduction of $t$ along $T \to T/\pi_C T$. The helper declarations `span_le_comap`, `qmap`, `qmap_comp_mk`, `qmap_id`, `qmap_comp` record the induced ring map $T/\pi_C T \to T'/\pi_C T'$ attached to a $C$-algebra map $\varphi : T \to T'$ and its functoriality; `Pt.map` transports a presented point along $\varphi$ by precomposition, with `Pt.ext'`, `Pt.map_id`, `Pt.map_comp` as the corresponding extensionality and functoriality statements, and `quotEquiv_comp_mk` identifies $T \to T/(0) \cong T$ with the identity when $\pi_C = 0$ in $T$.
--
--   The second section specialises $\pi_C$ to $\pi$ pushed from an $\mathcal{O}$-algebra structure on $C$, in a Čerednik–Drinfeld frame: $r, N \in \mathbb{N}$, an $\mathcal{O}$-algebra $O^{nr}$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ containing all integers (hypothesis `hΛℤ`), a fake elliptic curve $A_0$ of level $N$ over $O^{nr}/\pi$, a level $n$, a leg $\psi : O^{nr} \to C$, the family $(X_d, \xi_d)$ over $M_C$, a rule `tM` sending a full-level-$n$ fake elliptic curve $u$ over a $C$-algebra $T$ to a $T$-point of $M_C$ over $\operatorname{Spec} C$, and a rule `xOf` sending such a $u$ together with a rigidification $\rho$ of $u.1$ (relative to $r$, $\pi$, $A_0$ and the leg induced on $T$) to a point of $X_{\rho.d}$ over $T/\pi T$ lying above $\operatorname{tM} T u$. Here `xOf` is required to be given for $\mathcal{O}$-algebras $T$ whose $\mathcal{O}$-structure factors through $C$ and whose leg is the composite of $\psi$ with $C \to T$. For $d$ with $\rho.d = d$ and $\pi = 0$ in $T$, `ptX` transports `xOf` along $T/(0) \cong T$ into a $T$-point of $X_d$ over $\operatorname{Spec} C$ relative to $\xi_d$ followed by $g$.
--
--   `RelLoc T p q` asserts the existence of finitely many elements $f_1,\dots,f_m$ of $T/\pi T$ generating the unit ideal such that, for each $k$, there is a localisation $L$ of $T/\pi T$ away from $f_k$, carrying compatible $C$- and $\mathcal{O}$-algebra structures (scalar towers) with $\pi = 0$ in $L$, and over $L$ there are full-level-$n$ fake elliptic curves $u, u'$ with rigidifications $\rho, \rho'$ whose exponents satisfy $\rho.d = p.d$ and $\rho'.d = q.d$, an isomorphism $i_0 : u.1.A \cong u'.1.A$ over $L$ compatible with the group law, the $\Lambda$-action, the level and the marked point (`WithFullLevel.IsoVia`), a comparison of the rigidifications consisting of $i_b : \rho.E_b.A \to \rho'.E_b.A$ compatible with the maps $g_b$ and the structure morphisms, a map $u_A : \rho'.A_b.A \to \rho.A_b.A$ that is a pullback along the identity and satisfies $u_A$ followed by $\rho.g_A$ equals $\rho'.g_A$, and exponents $i_1, j_1$ with $i_b$ followed by $\rho'.\varphi$, $u_A$ and the action of $r^{i_1}$ equal to $\rho.\varphi$ followed by the action of $r^{j_1}$; and finally the points $\operatorname{ptX}$ of $(u,\rho)$ and $(u',\rho')$ coincide with the base changes to $L$ of $p.x$ and $q.x$. `Rel` adds the condition $p.t = q.t$. `MapCompat` is the Prop asserting that `Rel` is preserved by `Pt.map` for every $C$-algebra map, and under it `PR` is the functor on $C$-algebras (a [`CerednikDrinfeld.FormalOmega.AlgFunctor C`](../def/CerednikDrinfeld_FormalUpperHalfPlaneCharts.html#L10), the project's notion of a functor from universe-zero $C$-algebras to types with identity and composition laws as fields) sending $T$ to the quotient `Quot (Rel … T)`; note that `Rel` itself is not asserted to be an equivalence relation, the quotient being taken by the generated one. Finally `toM` extracts the underlying $M_C$-point of a class, `pt` gives the class of a $T$-point of $X_d$ over $\operatorname{Spec} C$ (its $M_C$-point being the composite with $\xi_d$, and its stratum component the reduction modulo $\pi_C$), and `ptR` gives the class attached to a pair $(u, \rho)$ through `tM` and `xOf`.
--
--   **Relation to Mathlib.** Fake elliptic curves with level and rigidification data, and the functors `AlgFunctor` on $C$-algebras, are the project's own notions; Mathlib has no counterpart. The quotient uses Mathlib's `Quot` applied to the relation `Rel`, which is not asserted to be reflexive, symmetric or transitive.
--
--   **Where it is used.** This model is the witness for the relative representability of the functor of rigidified fake elliptic curves with full level structure, presented through the strata $X_d$ of level-preserving isogeny pairs of exponent $d$, in the Čerednik–Drinfeld uniformisation of the quaternionic (Shimura) curves. The locality built into `RelLoc` — a covering of $\operatorname{Spec}(T/\pi T)$ by basic opens on each of which a pair of rigidified curves is exhibited — is what makes the quotient functor behave as a Zariski sheaf on affine bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_RigidifiedPairClassModel.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace CerednikDrinfeld.QM.RigidifiedPairClass

structure Pt {C : Type} [CommRing C] (πC : C) {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C))
    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC) (T : Type) [CommRing T] [Algebra C T] where

  t : Spec (CommRingCat.of T) ⟶ MC
  ht : t ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C T))

  d : ℕ

  x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T πC})) ⟶ X d
  hx : x ≫ ξ d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T πC}))) ≫ t

theorem Pt.ext' {C : Type} [CommRing C] {πC : C} {MC : Scheme.{0}} {g : MC ⟶ Spec (CommRingCat.of C)}
    {X : ℕ → Scheme.{0}} {ξ : ∀ d, X d ⟶ MC} {T : Type} [CommRing T] [Algebra C T]
    (p q : Pt πC g X ξ T) (ht : p.t = q.t) (hd : p.d = q.d) (hx : p.x ≫ eqToHom (congrArg X hd) = q.x) : p = q := by
  obtain ⟨pt, pht, pd, px, phx⟩ := p
  obtain ⟨qt, qht, qd, qx, qhx⟩ := q
  cases ht; cases hd
  simp only [eqToHom_refl, Category.comp_id] at hx
  cases hx
  rfl

theorem span_le_comap {C : Type} [CommRing C] (πC : C) {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T']
    (φ : T →ₐ[C] T') :
    Ideal.span {algebraMap C T πC} ≤ (Ideal.span {algebraMap C T' πC}).comap (φ : T →+* T') := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
  have : (φ : T →+* T') (algebraMap C T πC) = algebraMap C T' πC := φ.commutes πC
  rw [this]
  exact Ideal.subset_span rfl

def qmap {C : Type} [CommRing C] (πC : C) {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T']
    (φ : T →ₐ[C] T') : (T ⧸ Ideal.span {algebraMap C T πC}) →+* (T' ⧸ Ideal.span {algebraMap C T' πC}) :=
  Ideal.quotientMap _ (φ : T →+* T') (span_le_comap πC φ)

theorem qmap_comp_mk {C : Type} [CommRing C] (πC : C) {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T']
    (φ : T →ₐ[C] T') :
    (qmap πC φ).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (φ : T →+* T') := by
  ext x; rfl

theorem qmap_id {C : Type} [CommRing C] (πC : C) {T : Type} [CommRing T] [Algebra C T] :
    qmap πC (AlgHom.id C T) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  ext x; rfl

theorem qmap_comp {C : Type} [CommRing C] (πC : C) {T₁ T₂ T₃ : Type} [CommRing T₁] [Algebra C T₁] [CommRing T₂] [Algebra C T₂]
    [CommRing T₃] [Algebra C T₃] (φ : T₁ →ₐ[C] T₂) (φ' : T₂ →ₐ[C] T₃) :
    qmap πC (φ'.comp φ) = (qmap πC φ').comp (qmap πC φ) := by
  apply Ideal.Quotient.ringHom_ext
  ext x; rfl

noncomputable def Pt.map {C : Type} [CommRing C] {πC : C} {MC : Scheme.{0}} {g : MC ⟶ Spec (CommRingCat.of C)}
    {X : ℕ → Scheme.{0}} {ξ : ∀ d, X d ⟶ MC} {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T']
    (φ : T →ₐ[C] T') (p : Pt πC g X ξ T) : Pt πC g X ξ T' where
  t := Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ p.t
  ht := by
    rw [Category.assoc, p.ht, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap
  d := p.d
  x := Spec.map (CommRingCat.ofHom (qmap πC φ)) ≫ p.x
  hx := by
    rw [Category.assoc, p.hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, qmap_comp_mk]

theorem Pt.map_id {C : Type} [CommRing C] {πC : C} {MC : Scheme.{0}} {g : MC ⟶ Spec (CommRingCat.of C)}
    {X : ℕ → Scheme.{0}} {ξ : ∀ d, X d ⟶ MC} {T : Type} [CommRing T] [Algebra C T] (p : Pt πC g X ξ T) :
    p.map (AlgHom.id C T) = p := by
  refine Pt.ext' (p.map (AlgHom.id C T)) p ?_ rfl ?_
  · show Spec.map (CommRingCat.ofHom (RingHom.id T)) ≫ p.t = p.t
    rw [CommRingCat.ofHom_id]; erw [Spec.map_id]; exact Category.id_comp _
  · show (Spec.map (CommRingCat.ofHom (qmap πC (AlgHom.id C T))) ≫ p.x) ≫ eqToHom rfl = p.x
    rw [qmap_id, CommRingCat.ofHom_id]; erw [Spec.map_id]; simp

theorem Pt.map_comp {C : Type} [CommRing C] {πC : C} {MC : Scheme.{0}} {g : MC ⟶ Spec (CommRingCat.of C)}
    {X : ℕ → Scheme.{0}} {ξ : ∀ d, X d ⟶ MC} {T₁ T₂ T₃ : Type} [CommRing T₁] [Algebra C T₁] [CommRing T₂] [Algebra C T₂]
    [CommRing T₃] [Algebra C T₃] (φ : T₁ →ₐ[C] T₂) (φ' : T₂ →ₐ[C] T₃) (p : Pt πC g X ξ T₁) :
    p.map (φ'.comp φ) = (p.map φ).map φ' := by
  refine Pt.ext' (p.map (φ'.comp φ)) ((p.map φ).map φ') ?_ rfl ?_
  · show Spec.map (CommRingCat.ofHom ((φ'.comp φ : T₁ →ₐ[C] T₃) : T₁ →+* T₃)) ≫ p.t =
      Spec.map (CommRingCat.ofHom (φ' : T₂ →+* T₃)) ≫ (Spec.map (CommRingCat.ofHom (φ : T₁ →+* T₂)) ≫ p.t)
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  · show (Spec.map (CommRingCat.ofHom (qmap πC (φ'.comp φ))) ≫ p.x) ≫ eqToHom rfl =
      Spec.map (CommRingCat.ofHom (qmap πC φ')) ≫ (Spec.map (CommRingCat.ofHom (qmap πC φ)) ≫ p.x)
    rw [eqToHom_refl, Category.comp_id, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, qmap_comp]

section Model

variable {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
  (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
  {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)

  (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
    FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) g)

  (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
    { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
      x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

theorem quotEquiv_comp_mk {C : Type} [CommRing C] (πC : C) (T : Type) [CommRing T] [Algebra C T]
    (h0 : algebraMap C T πC = 0) :
    (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom).comp
      (Ideal.Quotient.mk (Ideal.span {algebraMap C T πC})) = RingHom.id T := by
  ext t
  rfl

noncomputable def ptX (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
    (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ g) :=
  ⟨Spec.map (CommRingCat.ofHom
      (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom)) ≫
      (xOf T ψT hψT u ρ).1 ≫ eqToHom (congrArg X hd), by
    subst hd
    simp only [eqToHom_refl, Category.comp_id, Category.assoc]
    rw [reassoc_of% (xOf T ψT hψT u ρ).2, (tM T u).2]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0,
      CommRingCat.ofHom_id]
    erw [Spec.map_id]
    exact Category.id_comp _⟩

def RelLoc (T : Type) [CommRing T] [Algebra C T]
    (p q : Pt (algebraMap 𝒪 C π) g X ξ T) : Prop :=
  ∃ (m : ℕ) (f : Fin m → (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})),
    Ideal.span (Set.range f) = ⊤ ∧
    ∀ k : Fin m,
      ∃ (L : Type) (_ : CommRing L) (_ : Algebra (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)
        (_ : IsLocalization.Away (f k) L) (_ : Algebra C L)
        (_ : IsScalarTower C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)
        (_ : Algebra 𝒪 L) (_ : IsScalarTower 𝒪 C L)
        (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0)
        (u u' : FakeEllipticCurve.WithFullLevel Λ N n L)
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u'.1)
        (hd : ρ.d = p.d) (hd' : ρ'.d = q.d)
        (i₀ : u.1.A ≅ u'.1.A) (hi : i₀.hom ≫ u'.1.f = u.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia u u' i₀ hi)
        (_ : (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i₀.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
            (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
            (i₁ j₁ : ℕ),
            ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)),
        (ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf p.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl u ρ hd h0).1 =
            Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)) ≫ p.x ∧
          (ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf q.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl u' ρ' hd' h0).1 =
            Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)) ≫ q.x

def Rel (T : Type) [CommRing T] [Algebra C T] (p q : Pt (algebraMap 𝒪 C π) g X ξ T) : Prop :=
  p.t = q.t ∧ RelLoc 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf T p q

def MapCompat : Prop :=
  ∀ (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
    (p q : Pt (algebraMap 𝒪 C π) g X ξ T),
    Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf T p q → Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf T' (p.map φ) (q.map φ)

noncomputable def PR (hmap : MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf) : CerednikDrinfeld.FormalOmega.AlgFunctor C where
  obj T _ _ := Quot (Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf T)
  map {T} _ _ {T'} _ _ φ := Quot.map (Pt.map φ) (fun p q h => hmap T T' φ p q h)
  map_id {T} _ _ z := by
    induction z using Quot.ind with
    | mk p => exact congrArg (Quot.mk _) (Pt.map_id p)
  map_comp {T₁} _ _ {T₂} _ _ {T₃} _ _ φ φ' z := by
    induction z using Quot.ind with
    | mk p => exact congrArg (Quot.mk _) (Pt.map_comp φ φ' p)

noncomputable def toM (hmap : MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf) (S : Type) [CommRing S] [Algebra C S]
    (z : (PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap).obj S) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) g :=
  Quot.lift (fun p : Pt (algebraMap 𝒪 C π) g X ξ S =>
      (⟨p.t, p.ht⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) g))
    (fun _ _ h => Subtype.ext h.1) z

noncomputable def pt (hmap : MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf) (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ g)) :
    (PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap).obj T :=
  Quot.mk _
    { t := x.1 ≫ ξ d, ht := by rw [Category.assoc]; exact x.2, d := d,
      x := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ x.1, hx := by rw [Category.assoc] }

noncomputable def ptR (hmap : MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf)
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) :
    (PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap).obj S :=
  Quot.mk _
    { t := (tM S u).1, ht := (tM S u).2, d := ρ.d, x := (xOf S ψS hψS u ρ).1, hx := (xOf S ψS hψS u ρ).2 }

end Model

end CerednikDrinfeld.QM.RigidifiedPairClass


