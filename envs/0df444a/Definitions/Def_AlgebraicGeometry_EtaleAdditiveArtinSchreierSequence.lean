-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAdditiveArtinSchreierSequence
-- name    : AlgebraicGeometry_EtaleAdditiveArtinSchreierSequence
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T10:27:58.908153+00:00
-- url     : https://prove2.me/theorems/48ce85d0-671b-55bc-b2b9-15c489190f5c
-- title:
--   Artin–Schreier sequence and its natural constant inclusion
-- statement:
--   The kernel of Frobenius minus identity is the constant prime-field sheaf, and Frobenius minus identity is étale locally surjective.
-- source:
--   Stacks Project, Lemma 59.63.6, https://stacks.math.columbia.edu/tag/0A3P.

import Definitions.Def_AlgebraicGeometry_EtaleAdditiveStructureSheaf
import Mathlib
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

noncomputable section

section

section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace PhilipponArtinSchreierLocalRing

/-- A solution of the homogeneous Artin–Schreier equation in a local
algebra is a prime-field scalar, including when the algebra has nilpotents. -/
theorem exists_scalar {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ}
    (hp : p.Prime) (f : ZMod p →+* R) (x : R) (hx : x ^ p = x) :
    ∃ a : ZMod p, f a = x := by
  letI : Fact p.Prime := ⟨hp⟩
  let k := IsLocalRing.ResidueField R
  let g := IsLocalRing.residue R
  letI : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    simpa only [map_natCast, map_zero] using congrArg f (CharP.cast_eq_zero (ZMod p) p))
  letI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    simpa only [map_natCast, map_zero] using congrArg g (CharP.cast_eq_zero R p))
  have hres : (g x) ^ p = g x := by rw [← map_pow, hx]
  have hmem : g x ∈ (⊥ : Subfield k) := (Subfield.mem_bot_iff_pow_eq_self k p).mpr hres
  have hbot : (g.comp f).fieldRange = (⊥ : Subfield k) := by
    rw [RingHom.ext_zmod (g.comp f) (ZMod.castHom (m := p) dvd_rfl k),
      ZMod.fieldRange_castHom_eq_bot]
  rw [← hbot, RingHom.mem_fieldRange] at hmem
  obtain ⟨a, ha⟩ := hmem
  let w := x - f a
  have hw : g w = 0 := by
    change g (x - f a) = 0
    rw [map_sub, sub_eq_zero]
    exact ha.symm
  have hwp : w ^ p = w := by
    change (x - f a) ^ p = x - f a
    rw [sub_pow_char, hx, ← map_pow, ZMod.pow_card]
  have hu : IsUnit (1 - w ^ (p - 1)) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_sub, map_one, map_pow, hw, zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt), sub_zero]
    exact one_ne_zero
  have hprod : (1 - w ^ (p - 1)) * w = 0 := by
    rw [sub_mul, one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hwp, sub_self]
  have : w = 0 := hu.mul_right_inj.mp (hprod.trans (mul_zero _).symm)
  exact ⟨a, (sub_eq_zero.mp this).symm⟩

end PhilipponArtinSchreierLocalRing

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponArtinSchreierKernel

open PhilipponEtaleAdditiveStructureSheaf

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
variable {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0)

/-- The canonical map from the prime field. -/
def primeScalar : ZMod p →+* K := by
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hK
  exact ZMod.castHom (m := p) dvd_rfl K

private abbrev coeff (p : ℕ) : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} (ZMod p))

private abbrev difference : sheaf X ⟶ sheaf X := frobenius π hp hK - 𝟙 (sheaf X)

private def constantToAdditive : (Functor.const X.Etaleᵒᵖ).obj (coeff p) ⟶ (sheaf X).obj where
  app U := AddCommGrpCat.ofHom
    (((scalar π U.unop).hom.comp (primeScalar hp hK)).toAddMonoidHom.comp
      (AddEquiv.ulift : ULift.{u} (ZMod p) ≃+ ZMod p).toAddMonoidHom)
  naturality := by
    intro U V f
    apply AddCommGrpCat.ext
    intro a
    change ULift (ZMod p) at a
    change scalar π V.unop (primeScalar hp hK a.down) =
      f.unop.left.appTop (scalar π U.unop (primeScalar hp hK a.down))
    have h : scalar π U.unop ≫ f.unop.left.appTop = scalar π V.unop := by
      rw [scalar, scalar, Category.assoc, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, MorphismProperty.Over.w f.unop]
    exact (ConcreteCategory.congr_hom h _).symm

private theorem constantToAdditive_zero :
    constantToAdditive π hp hK ≫ (difference π hp hK).hom = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  change ULift (ZMod p) at a
  let s := (scalar π U.unop).hom.comp (primeScalar hp hK)
  change (s a.down) ^ p - s a.down = 0
  letI : Fact p.Prime := ⟨hp⟩
  rw [← map_pow, ZMod.pow_card, sub_self]

private def constantToKernel :
    (Functor.const X.Etaleᵒᵖ).obj (coeff p) ⟶ (kernel (difference π hp hK)).obj :=
  kernel.lift (difference π hp hK).hom (constantToAdditive π hp hK)
    (constantToAdditive_zero π hp hK) ≫
      (PreservesKernel.iso (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (difference π hp hK)).inv

private theorem constantToKernel_ι (U : X.Etale) (a : ULift.{u} (ZMod p)) :
    (kernel.ι (difference π hp hK)).hom.app (op U)
      ((constantToKernel π hp hK).app (op U) a) = scalar π U (primeScalar hp hK a.down) := by
  have h : constantToKernel π hp hK ≫ (kernel.ι (difference π hp hK)).hom =
      constantToAdditive π hp hK := by
    let F := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}
    change (_ ≫ (PreservesKernel.iso F (difference π hp hK)).inv) ≫
      F.map (kernel.ι (difference π hp hK)) = _
    rw [Category.assoc, PreservesKernel.iso_inv_ι]
    exact kernel.lift_ι _ _ _
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op U)) a

private theorem kernel_ι_injective (U : X.Etale) :
    Function.Injective ((kernel.ι (difference π hp hK)).hom.app (op U)) := by
  let : Mono (kernel.ι (difference π hp hK)).hom := inferInstanceAs
    (Mono ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).map (kernel.ι (difference π hp hK))))
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

private theorem locally_injective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantToKernel π hp hK) := by
  constructor
  intro U a b hab
  let W : U.unop.left → X.Etale := fun _ => U.unop
  let f (x : U.unop.left) : W x ⟶ U.unop := 𝟙 _
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W f) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    have h := congrArg ((kernel.ι (difference π hp hK)).hom.app (op U.unop)) hab
    change (kernel.ι (difference π hp hK)).hom.app (op U.unop)
        ((constantToKernel π hp hK).app (op U.unop) a) =
      (kernel.ι (difference π hp hK)).hom.app (op U.unop)
        ((constantToKernel π hp hK).app (op U.unop) b) at h
    rw [constantToKernel_ι, constantToKernel_ι] at h
    let g := (U.unop.left.presheaf.germ ⊤ x trivial).hom.comp
      ((scalar π U.unop).hom.comp (primeScalar hp hK))
    letI : Fact p.Prime := ⟨hp⟩
    have h' : g a.down = g b.down := congrArg (U.unop.left.presheaf.germ ⊤ x trivial).hom h
    have : a = b := ULift.ext a b (g.injective h')
    exact congrArg _ this
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, x, rfl⟩

private theorem exists_open_of_fixed (U : X.Etale) (a : Γ(U.left, ⊤)) (ha : a ^ p = a) (x : U.left) :
    ∃ (V : U.left.Opens), x ∈ V ∧ ∃ r : ZMod p,
      V.ι.appTop a = V.ι.appTop (scalar π U (primeScalar hp hK r)) := by
  let g := (U.left.presheaf.germ ⊤ x trivial).hom
  have hfixed : (g a) ^ p = g a := by rw [← map_pow, ha]
  obtain ⟨r, hr⟩ := PhilipponArtinSchreierLocalRing.exists_scalar hp
    (g.comp ((scalar π U).hom.comp (primeScalar hp hK))) (g a) hfixed
  change g (scalar π U (primeScalar hp hK r)) = g a at hr
  obtain ⟨V, hxV, i, j, h⟩ := U.left.presheaf.germ_eq x
    (show x ∈ (⊤ : U.left.Opens) from trivial) (show x ∈ (⊤ : U.left.Opens) from trivial)
    a (scalar π U (primeScalar hp hK r)) hr.symm
  change U.left.Opens at V
  refine ⟨V, hxV, r, ?_⟩
  let k : V.ι ''ᵁ ⊤ ⟶ V := eqToHom V.ι_image_top
  have h' := congrArg (U.left.presheaf.map k.op).hom h
  change U.left.presheaf.map k.op (U.left.presheaf.map i.op a) =
    U.left.presheaf.map k.op (U.left.presheaf.map j.op (scalar π U (primeScalar hp hK r))) at h'
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp] at h'
  rw [Scheme.Opens.ι_appTop]
  exact (Subsingleton.elim (k ≫ i) (homOfLE le_top)) ▸
    (Subsingleton.elim (k ≫ j) (homOfLE le_top)) ▸ h'

private theorem locally_surjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantToKernel π hp hK) := by
  constructor
  intro U a
  let α : Γ(U.left, ⊤) := (kernel.ι (difference π hp hK)).hom.app (op U) a
  have hα : α ^ p = α := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f => f.hom) (kernel.condition (difference π hp hK))) (op U)) a
    change α ^ p - α = 0 at h
    exact sub_eq_zero.mp h
  choose V hx r hr using fun x : U.left => exists_open_of_fixed π hp hK U α hα x
  let W (x : U.left) : X.Etale := Scheme.Etale.mk ((V x).ι ≫ U.hom)
  let f (x : U.left) : W x ⟶ U := MorphismProperty.Over.homMk (V x).ι rfl trivial
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W f) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    refine ⟨ULift.up (r x), kernel_ι_injective π hp hK (W x) ?_⟩
    rw [constantToKernel_ι, NatTrans.naturality_apply (kernel.ι (difference π hp hK)).hom (f x).op]
    change scalar π (W x) (primeScalar hp hK (r x)) = (V x).ι.appTop α
    rw [hr x]
    have h : scalar π U ≫ (V x).ι.appTop = scalar π (W x) := by
      change scalar π U ≫ (f x).left.appTop = scalar π (W x)
      rw [scalar, scalar, Category.assoc, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, MorphismProperty.Over.w (f x)]
    exact (ConcreteCategory.congr_hom h _).symm
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, ⟨x, hx x⟩, rfl⟩

/-- The kernel of Frobenius minus identity is the constant prime-field sheaf. -/
def constantIsoKernel :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (coeff p) ≅
      kernel (difference π hp hK) := by
  letI := locally_injective π hp hK
  letI := locally_surjective π hp hK
  have h := X.smallEtaleTopology.W_of_isLocallyBijective (constantToKernel π hp hK)
  letI := (X.smallEtaleTopology.W_iff (constantToKernel π hp hK)).mp h
  exact asIso ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map (constantToKernel π hp hK)) ≪≫
    asIso ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).counit.app
      (kernel (difference π hp hK)))

/-- The inclusion of constant prime-field coefficients in the additive sheaf. -/
def inclusion : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (coeff p) ⟶
    sheaf X :=
  (constantIsoKernel π hp hK).hom ≫ kernel.ι (difference π hp hK)

/-- The adjunct of the inclusion evaluates a constant as that element of the
prime field in the section ring of the terminal chart. -/
theorem homEquiv_inclusion_apply {T : X.Etale} (hT : IsTerminal T) (a : ULift.{u} (ZMod p)) :
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv
      (coeff p) (sheaf X) (inclusion π hp hK)) a = scalar π T (primeScalar hp hK a.down) := by
  let J := X.smallEtaleTopology
  let P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const X.Etaleᵒᵖ).obj (coeff p)
  let B := kernel (difference π hp hK)
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  have e : adj.unit.app P ≫ (constantIsoKernel π hp hK).hom.hom =
      constantToKernel π hp hK := by
    let L := presheafToSheaf J AddCommGrpCat.{u}
    let R := sheafToPresheaf J AddCommGrpCat.{u}
    let f : P ⟶ R.obj B := constantToKernel π hp hK
    have hu : f ≫ adj.unit.app (R.obj B) = adj.unit.app P ≫ R.map (L.map f) :=
      adj.unit.naturality f
    have ht : adj.unit.app (R.obj B) ≫ R.map (adj.counit.app B) = 𝟙 (R.obj B) :=
      adj.right_triangle_components B
    change adj.unit.app P ≫ R.map (L.map f ≫ adj.counit.app B) = f
    rw [R.map_comp, ← Category.assoc, ← hu, Category.assoc, ht, Category.comp_id]
  rw [Adjunction.homEquiv_unit, constantSheafAdj, Adjunction.comp_unit_app]
  change ((𝟙 (coeff p) ≫ (adj.unit.app P).app (op T)) ≫
    ((constantIsoKernel π hp hK).hom.hom.app (op T) ≫
      (kernel.ι (difference π hp hK)).hom.app (op T))) a = _
  rw [Category.id_comp, ← Category.assoc]
  have he : (adj.unit.app P).app (op T) ≫ (constantIsoKernel π hp hK).hom.hom.app (op T) =
      (constantToKernel π hp hK).app (op T) := NatTrans.congr_app e (op T)
  rw [he]
  exact constantToKernel_ι π hp hK T a

end PhilipponArtinSchreierKernel

end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite Polynomial


namespace PhilipponArtinSchreierEtaleCover

universe u
variable {R : Type u} [CommRing R]

private def equation (p : ℕ) (a : R) : R[X] := X ^ p - (X + C a)

private theorem monic_equation (p : ℕ) (hp : 1 < p) (a : R) : (equation p a).Monic := by
  apply monic_X_pow_sub
  exact (degree_add_le _ _).trans_lt
    ((max_le degree_X_le (degree_C_le.trans zero_le_one)).trans_lt (by exact_mod_cast hp))

private theorem degree_equation [Nontrivial R] (p : ℕ) (hp : 1 < p) (a : R) :
    (equation p a).degree = p := by
  unfold equation
  rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact (degree_add_le _ _).trans_lt
    ((max_le degree_X_le (degree_C_le.trans zero_le_one)).trans_lt (by exact_mod_cast hp))

private theorem root_equation (p : ℕ) (a : R) :
    (AdjoinRoot.root (equation p a)) ^ p - AdjoinRoot.root (equation p a) =
      algebraMap R (AdjoinRoot (equation p a)) a := by
  have h := AdjoinRoot.eval₂_root (equation p a)
  simp only [equation, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_iff_eq_add.mpr ((sub_eq_zero.mp h).trans (add_comm _ _))

private theorem etale (p : ℕ) (hp : 1 < p) (hR : (p : R) = 0) (a : R) :
    Algebra.Etale R (AdjoinRoot (equation p a)) := by
  let f := equation p a
  let A := AdjoinRoot f
  have hd : f.derivative = -1 := by
    simp [f, equation, derivative_X_pow, hR]
  have hder : IsUnit (AdjoinRoot.mk f f.derivative) := by rw [hd, map_neg, map_one]; exact isUnit_one.neg
  let P : StandardEtalePair R := ⟨f, monic_equation p hp a, f.derivative, 1, 0, 1, by simp⟩
  let away : A ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit A (Localization.Away (AdjoinRoot.mk f f.derivative))
      (AdjoinRoot.mk f f.derivative) hder).restrictScalars R
  letI : Algebra.IsStandardEtale R A := Algebra.IsStandardEtale.of_equiv
    (P.equivAwayAdjoinRoot.trans away.symm)
  infer_instance

private theorem algebraMap_injective [Nontrivial R] (p : ℕ) (hp : 1 < p) (a : R) :
    Function.Injective (algebraMap R (AdjoinRoot (equation p a))) := by
  let f := equation p a
  have hm : f.Monic := monic_equation p hp a
  have hleft : Function.LeftInverse (fun x => (AdjoinRoot.modByMonicHom hm x).coeff 0)
      (algebraMap R (AdjoinRoot f)) := by
    intro r
    change (AdjoinRoot.modByMonicHom hm (AdjoinRoot.mk f (C r))).coeff 0 = r
    have hdeg : (C r).degree < f.degree := by
      rw [degree_equation p hp a]
      exact degree_C_le.trans_lt (by exact_mod_cast hp.pos)
    rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hm).mpr hdeg, coeff_C_zero]
  exact hleft.injective

/-- A finite étale surjection where a given affine section has an Artin–Schreier preimage. -/
theorem exists_root_spec (R : CommRingCat.{u}) (p : ℕ) (hp : 1 < p)
    (hR : (p : Γ(Spec R, ⊤)) = 0) (a : Γ(Spec R, ⊤)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec R) (b : Γ(Y, ⊤)),
      IsFinite f ∧ Etale f ∧ Surjective f ∧ b ^ p - b = f.appTop a := by
  let e := Scheme.ΓSpecIso R
  rcases subsingleton_or_nontrivial R with h | h
  · letI : Subsingleton Γ(Spec R, ⊤) := e.commRingCatIsoToRingEquiv.injective.subsingleton
    exact ⟨_, 𝟙 _, 0, inferInstance, inferInstance, inferInstance, Subsingleton.elim _ _⟩
  · letI : Nontrivial R := h
    have hR' : (p : R) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (fun r : Γ(Spec R, ⊤) => e.hom r) hR
    let b := e.hom a
    let f := equation p b
    let A := AdjoinRoot f
    let g : R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A)
    letI : Module.Finite R A := (monic_equation p hp b).finite_adjoinRoot
    letI : Algebra.Etale R A := etale p hp hR' b
    have hfinite : (algebraMap R A).Finite := RingHom.finite_algebraMap.mpr inferInstance
    have hetale : (algebraMap R A).Etale := RingHom.etale_algebraMap.mpr inferInstance
    refine ⟨_, Spec.map g, (Scheme.ΓSpecIso _).inv (AdjoinRoot.root f),
      (IsFinite.SpecMap_iff g).mpr hfinite, (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hetale,
      ⟨hfinite.to_isIntegral.comap_surjective (algebraMap_injective p hp b)⟩, ?_⟩
    rw [← map_pow, ← map_sub, root_equation p b]
    change (e.hom ≫ g ≫ (Scheme.ΓSpecIso _).inv) a = _
    rw [Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem exists_root_affine (X : Scheme.{u}) [IsAffine X] (p : ℕ) (hp : 1 < p)
    (hX : (p : Γ(X, ⊤)) = 0) (a : Γ(X, ⊤)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (b : Γ(Y, ⊤)),
      IsFinite f ∧ Etale f ∧ Surjective f ∧ b ^ p - b = f.appTop a := by
  let e := X.isoSpec
  have hX' : (p : Γ(Spec Γ(X, ⊤), ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (fun r : Γ(X, ⊤) => e.inv.appTop r) hX
  obtain ⟨Y, f, b, hf, he, hs, hb⟩ := exists_root_spec _ p hp hX' (e.inv.appTop a)
  letI := hf
  letI := he
  letI := hs
  refine ⟨Y, f ≫ e.inv, b, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_appTop]
  exact hb

private theorem exists_root_near (X : Scheme.{u}) (p : ℕ) (hp : 1 < p)
    (hX : (p : Γ(X, ⊤)) = 0) (a : Γ(X, ⊤)) (x : X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (y : Y) (b : Γ(Y, ⊤)),
      Etale f ∧ f y = x ∧ b ^ p - b = f.appTop a := by
  obtain ⟨i, z, rfl⟩ := X.affineCover.exists_eq x
  let g := X.affineCover.f i
  have hg : (p : Γ(X.affineCover.X i, ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (fun r : Γ(X, ⊤) => g.appTop r) hX
  obtain ⟨Y, f, b, _, he, hs, hb⟩ := exists_root_affine _ p hp hg (g.appTop a)
  obtain ⟨y, rfl⟩ := hs.surj z
  letI := he
  refine ⟨Y, f ≫ g, y, b, inferInstance, rfl, ?_⟩
  rw [Scheme.Hom.comp_appTop]
  exact hb

open PhilipponEtaleAdditiveStructureSheaf

/-- The Artin–Schreier map is locally onto on the actual small étale site. -/
theorem locally_surjective {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
    {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) :
    Sheaf.IsLocallySurjective (frobenius π hp hK - 𝟙 (sheaf X)) := by
  classical
  constructor
  intro U a
  let a₀ : Γ(U.left, ⊤) := a
  choose Y f y b he hx hr using fun x : U.left =>
    exists_root_near U.left p hp.one_lt (cast_eq_zero π hK U) a₀ x
  let W (x : U.left) : X.Etale := by
    letI := he x
    exact Scheme.Etale.mk (f x ≫ U.hom)
  let g (x : U.left) : W x ⟶ U := MorphismProperty.Over.homMk (f x) rfl trivial
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W g) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    exact ⟨b x, hr x⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, y x, hx x⟩

end PhilipponArtinSchreierEtaleCover

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

namespace PhilipponEtaleAdditiveStructureSheaf

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
variable {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0)

private theorem frobenius_mulScalar (a : K) :
    mulScalar π a ≫ frobenius π hp hK = frobenius π hp hK ≫ mulScalar π (a ^ p) := by
  ext U x
  change Γ(U.unop.left, ⊤) at x
  change (scalar π U.unop a * x) ^ p = scalar π U.unop (a ^ p) * x ^ p
  rw [map_pow, mul_pow]

/-- Frobenius acts semilinearly on sheaf cohomology for the scalar action
defined by multiplication on the actual étale structure sheaf. -/
theorem frobenius_cohomology_smul (n : ℕ) (a : K) (x : (sheaf X).H n) :
    Sheaf.H.map (frobenius π hp hK) n ((cohomologyModule π n).smul a x) =
      (cohomologyModule π n).smul (a ^ p) (Sheaf.H.map (frobenius π hp hK) n x) := by
  change Sheaf.H.map (frobenius π hp hK) n (Sheaf.H.map (mulScalar π a) n x) =
    Sheaf.H.map (mulScalar π (a ^ p)) n (Sheaf.H.map (frobenius π hp hK) n x)
  rw [← Sheaf.H.map_comp_apply, frobenius_mulScalar, Sheaf.H.map_comp_apply]

end PhilipponEtaleAdditiveStructureSheaf

end

end


