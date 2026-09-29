-- Prove2me | Definitions.Def_AlgebraicGeometry_SchemeFrobenius
-- name    : AlgebraicGeometry_SchemeFrobenius
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/dbb85030-eb4d-500d-9447-ac0feaa66fba
-- title:
--   Absolute and relative Frobenius morphisms of schemes
-- statement:
--   Throughout, $p$ is a prime, $n\ge 0$, and $q=p^n$. For a commutative ring $R$ with $(p:R)=0$, `powCharRingHom R p n hp h` is the ring endomorphism $x\mapsto x^{q}$; additivity comes from the prime-power binomial expansion, and no characteristic or exponential-characteristic instance is required, only the equation $p=0$ in $R$, so that the construction applies to every ring of sections of a scheme killed by $p$ (including the zero ring). It is bijective when $R$ has characteristic $p$ and is a perfect ring, and it commutes with arbitrary ring homomorphisms between rings killed by $p$.
--
--   For a scheme $X$ with $(p:\Gamma(X,\top))=0$, the hypothesis propagates to every $\Gamma(X,U)$ and to every stalk. `frobeniusSheafHom` is the endomorphism of $\mathcal O_X$ given on each open by $s\mapsto s^{q}$, and `Scheme.frobenius` is the morphism $X\to X$ which is the identity on the underlying space with this map on structure sheaves; the locality condition on stalk maps holds because $g^{q}$ is a unit exactly when $g$ is. The interface lemmas record that on sections, on global sections and on stalks the morphism is $g\mapsto g^{q}$, that $\Phi_{p^0}=\mathrm{id}$, that $\Phi_{p^m}$ preceded by $\Phi_{p^n}$ is $\Phi_{p^{m+n}}$, that for $f:X\to Y$ one has $\Phi_X$ followed by $f$ equal to $f$ followed by $\Phi_Y$, and that on $\operatorname{Spec} R$ it is $\operatorname{Spec}$ of `powCharRingHom`, hence an isomorphism whenever that power map is bijective, in particular for a perfect ring of characteristic $p$.
--
--   For $f:X\to S$ with $S$ also killed by $p$, `frobeniusTwist` is the fibre product $X\times_{S,\Phi_q}S$ and `relFrobenius` is the morphism $X\to X\times_{S,\Phi_q}S$ whose composites with the two projections are the absolute Frobenius of $X$ and $f$. When the Frobenius of $S$ is an isomorphism, so is the first projection, and the relative Frobenius is the absolute one followed by its inverse.
--
--   **Relation to Mathlib.** Mathlib has no Frobenius morphism of schemes; this is the project's own construction. The ring-level map `powCharRingHom` is a variant of Mathlib's `iterateFrobenius` assuming only $(p:R)=0$ rather than a characteristic instance, and is identified with `iterateFrobenius R p n` when `CharP R p` holds.
--
--   **Where it is used.** These morphisms provide the language in which an endomorphism of a group scheme in characteristic $p$ can be said to be a Frobenius up to isomorphism, and hence to have vanishing differential; this is what makes certain endomorphisms of Jacobians of curves over finite fields, and the kernels of polynomials in them, étale.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SchemeFrobenius.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

def powCharRingHom (R : Type*) [CommRing R] (p n : ℕ) (hp : p.Prime) (h : (p : R) = 0) :
    R →+* R where
  toFun x := x ^ p ^ n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero n hp.ne_zero)
  map_add' x y := by
    obtain ⟨r, hr⟩ := (Commute.all x y).exists_add_pow_prime_pow_eq hp n
    rw [hr, h, zero_mul, zero_mul, zero_mul, add_zero]

@[simp]
theorem powCharRingHom_apply {R : Type*} [CommRing R] (p n : ℕ) (hp : p.Prime) (h : (p : R) = 0)
    (x : R) : powCharRingHom R p n hp h x = x ^ p ^ n := rfl

theorem RingHom.map_powCharRingHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p n : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0) (x : R) :
    f (powCharRingHom R p n hp hR x) = powCharRingHom S p n hp hS (f x) := by
  simp [map_pow]

theorem bijective_powCharRingHom_of_perfectRing {R : Type*} [CommRing R] (p n : ℕ)
    [hp : Fact p.Prime] [CharP R p] [PerfectRing R p] :
    Function.Bijective (powCharRingHom R p n hp.out (CharP.cast_eq_zero R p)) := by
  have : ⇑(powCharRingHom R p n hp.out (CharP.cast_eq_zero R p)) = ⇑(iterateFrobenius R p n) := by
    ext x; simp [iterateFrobenius_def]
  rw [this]
  exact bijective_iterateFrobenius R p n

namespace Scheme

variable (X : Scheme.{u}) (p n : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)

theorem natCast_eq_zero_sections {X : Scheme.{u}} {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  have := congrArg (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) hX
  simpa using this

theorem natCast_eq_zero_stalk {X : Scheme.{u}} {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (x : X) : (p : X.presheaf.stalk x) = 0 := by
  have := congrArg (X.presheaf.germ ⊤ x trivial) hX
  simpa using this

def frobeniusSheafHom : X.presheaf ⟶ X.presheaf where
  app U := CommRingCat.ofHom (powCharRingHom Γ(X, U.unop) p n hp (natCast_eq_zero_sections hX _))
  naturality U V i := by
    ext s
    simp [map_pow]

def frobenius : X ⟶ X where
  base := 𝟙 _
  c := X.frobeniusSheafHom p n hp hX
  prop x := by

    constructor
    intro g hg
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq g
    have key : (PresheafedSpace.Hom.stalkMap
        ⟨𝟙 _, X.frobeniusSheafHom p n hp hX⟩ x).hom (X.presheaf.germ U x hxU s) =
        X.presheaf.germ U x hxU s ^ p ^ n := by
      have h1 := PresheafedSpace.stalkMap_germ_apply
        (C := CommRingCat) (X := X.toPresheafedSpace) (Y := X.toPresheafedSpace)
        ⟨𝟙 _, X.frobeniusSheafHom p n hp hX⟩ U x hxU s
      refine h1.trans ?_
      change (X.presheaf.germ U x hxU) (s ^ p ^ n) = _
      rw [map_pow]
    erw [key] at hg
    exact (isUnit_pow_iff (pow_ne_zero n hp.ne_zero)).1 hg

@[simp]
theorem frobenius_base : (X.frobenius p n hp hX).base = 𝟙 _ := rfl

theorem frobenius_apply (x : X) : (X.frobenius p n hp hX) x = x := rfl

@[simp]
theorem frobenius_preimage (U : X.Opens) : (X.frobenius p n hp hX) ⁻¹ᵁ U = U := rfl

theorem frobenius_app_apply (U : X.Opens) (s : Γ(X, U)) :
    (X.frobenius p n hp hX).app U s = s ^ p ^ n := rfl

theorem frobenius_appTop_apply (s : Γ(X, ⊤)) :
    (X.frobenius p n hp hX).appTop s = s ^ p ^ n := rfl

theorem frobenius_stalkMap_apply (x : X) (g : X.presheaf.stalk x) :
    (X.frobenius p n hp hX).stalkMap x g = g ^ p ^ n := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.frobenius p n hp hX) U x hxU s
  refine h1.trans ?_
  change (X.presheaf.germ U x hxU) (s ^ p ^ n) = _
  rw [map_pow]

theorem presheaf_map_eqToHom_op_apply {X : Scheme.{u}} {U V : X.Opens} (h : U = V)
    (t : Γ(X, V)) : X.presheaf.map (eqToHom h).op t = cast (by rw [h]) t := by
  subst h; simp

@[reassoc]
theorem frobenius_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (p n : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) :
    X.frobenius p n hp hX ≫ f = f ≫ Y.frobenius p n hp hY := by
  refine Scheme.Hom.ext rfl (fun U => ?_)
  ext s
  simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [presheaf_map_eqToHom_op_apply]
  refine (cast_eq _ _).trans ?_
  change (X.frobenius p n hp hX).app _ (f.app U s) = f.app _ ((Y.frobenius p n hp hY).app U s)
  rw [frobenius_app_apply, frobenius_app_apply]
  change f.app U s ^ p ^ n = f.app U (s ^ p ^ n)
  rw [map_pow]

theorem frobenius_zero : X.frobenius p 0 hp hX = 𝟙 X := by
  refine Scheme.Hom.ext rfl (fun U => ?_)
  ext s
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [presheaf_map_eqToHom_op_apply]
  refine (cast_eq _ _).trans ?_
  change (X.frobenius p 0 hp hX).app U s = (𝟙 X : X ⟶ X).app U s
  rw [frobenius_app_apply, pow_zero, pow_one]
  rfl

@[reassoc]
theorem frobenius_comp_frobenius (m : ℕ) :
    X.frobenius p m hp hX ≫ X.frobenius p n hp hX = X.frobenius p (m + n) hp hX := by
  refine Scheme.Hom.ext rfl (fun U => ?_)
  ext s
  simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [presheaf_map_eqToHom_op_apply]
  refine (cast_eq _ _).trans ?_
  change (X.frobenius p m hp hX).app _ ((X.frobenius p n hp hX).app U s) =
    (X.frobenius p (m + n) hp hX).app U s
  rw [frobenius_app_apply, frobenius_app_apply, frobenius_app_apply]
  change (s ^ p ^ n) ^ p ^ m = s ^ p ^ (m + n)
  rw [← pow_mul, ← pow_add, Nat.add_comm n m]

theorem natCast_eq_zero_ΓSpec {R : Type u} [CommRing R] {p : ℕ} (hR : (p : R) = 0) :
    (p : Γ(Spec (.of R), ⊤)) = 0 := by
  have := congrArg (Scheme.ΓSpecIso (.of R)).inv hR
  simpa using this

theorem frobenius_Spec {R : Type u} [CommRing R] (p n : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    (Spec (.of R)).frobenius p n hp (natCast_eq_zero_ΓSpec hR) =
      Spec.map (CommRingCat.ofHom (powCharRingHom R p n hp hR)) := by
  refine ext_of_isAffine ?_
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of R)).hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1
  ext s
  apply hinj
  have h2 := congrArg (fun φ => φ.hom s)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (powCharRingHom R p n hp hR)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, powCharRingHom_apply] at h2
  refine Eq.trans ?_ h2.symm
  change (Scheme.ΓSpecIso (.of R)).hom
      (((Spec (.of R)).frobenius p n hp (natCast_eq_zero_ΓSpec hR)).appTop s) = _
  rw [frobenius_appTop_apply, map_pow]

theorem isIso_frobenius_Spec_of_bijective {R : Type u} [CommRing R] (p n : ℕ) (hp : p.Prime)
    (hR : (p : R) = 0) (hbij : Function.Bijective (powCharRingHom R p n hp hR)) :
    IsIso ((Spec (.of R)).frobenius p n hp (natCast_eq_zero_ΓSpec hR)) := by
  rw [frobenius_Spec p n hp hR]
  have : IsIso (CommRingCat.ofHom (powCharRingHom R p n hp hR)) :=
    (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom (powCharRingHom R p n hp hR))).2 hbij
  infer_instance

theorem isIso_frobenius_Spec_of_perfectRing {R : Type u} [CommRing R] (p n : ℕ)
    [hp : Fact p.Prime] [CharP R p] [PerfectRing R p] (h : (p : Γ(Spec (.of R), ⊤)) = 0) :
    IsIso ((Spec (.of R)).frobenius p n hp.out h) :=
  isIso_frobenius_Spec_of_bijective p n hp.out (CharP.cast_eq_zero R p)
    (bijective_powCharRingHom_of_perfectRing p n)

section Relative

variable {X} {S : Scheme.{u}} (f : X ⟶ S) (hS : (p : Γ(S, ⊤)) = 0)

noncomputable abbrev frobeniusTwist : Scheme.{u} :=
  Limits.pullback f (S.frobenius p n hp hS)

noncomputable def relFrobenius : X ⟶ frobeniusTwist p n hp f hS :=
  Limits.pullback.lift (X.frobenius p n hp hX) f (frobenius_comp f p n hp hX hS)

@[reassoc (attr := simp)]
theorem relFrobenius_fst :
    relFrobenius p n hp hX f hS ≫ Limits.pullback.fst _ _ = X.frobenius p n hp hX :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relFrobenius_snd : relFrobenius p n hp hX f hS ≫ Limits.pullback.snd _ _ = f :=
  Limits.pullback.lift_snd _ _ _

theorem isIso_fst_frobeniusTwist [IsIso (S.frobenius p n hp hS)] :
    IsIso (Limits.pullback.fst f (S.frobenius p n hp hS)) := inferInstance

theorem relFrobenius_eq_frobenius_comp_inv [IsIso (S.frobenius p n hp hS)] :
    relFrobenius p n hp hX f hS =
      X.frobenius p n hp hX ≫ inv (Limits.pullback.fst f (S.frobenius p n hp hS)) := by
  rw [← relFrobenius_fst p n hp hX f hS, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Relative

end Scheme

end AlgebraicGeometry


