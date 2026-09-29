-- Prove2me | Definitions.Def_NumberField_LevelArithmeticModP
-- name    : NumberField_LevelArithmeticModP
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/3d59c15a-6a75-5d58-a0ee-d8ab998b7a62
-- title:
--   Level arithmetic mod p: units, class groups, places
-- statement:
--   For intermediate fields $K \le L$ of $\bar{\mathbb{Q}}/\mathbb{Q}$ this module builds the mod-$p$ arithmetic data of the pair. The bridge part views $L$ as an intermediate field $L'$ of $\bar{\mathbb{Q}}$ over $K$ (`levelField`, via extension of scalars, with `levelFieldEquiv` the evident identification $L \cong L'$ and instances making $L'$ a number field when $L/\mathbb{Q}$ is finite), sets `LevelGal` $= \mathrm{Aut}_K(L')$, and, when $L'/K$ is normal, defines `levelGal`, the homomorphism from the subgroup of $\mathrm{Aut}_\mathbb{Q}(\bar{\mathbb{Q}})$ fixing $K$ pointwise to $\mathrm{Aut}_K(L')$ given by restriction; elements fixing $L$ pointwise map to $1$. `inflLevel` is inflation of representations along `levelGal`.
--
--   The mod-$p$ part works with a commutative ring $k$ and a group $G$: for $\rho$ a $k$-representation on $V$, the submodules $(p)V$ (the pointwise $p$-multiple of $\top$) and $V[p]$ are $\rho$-stable, $p$ annihilates both $V/(p)V$ and $V[p]$, and `modP`, `torsionP` are the resulting $\mathbb{Z}/p$-representations; `repModP`, `repTorsionP` give functors $\mathrm{Rep}_k(G) \to \mathrm{Rep}_{\mathbb{Z}/p}(G)$, with `repModPMap`, `repTorsionPMap` on morphisms.
--
--   For a number field $F$ over $E$, `classGroupAut` makes $\mathrm{Aut}_E(F)$ act on $\mathrm{Cl}(\mathcal{O}_F)$ through the functoriality of class groups, giving `classGroupRep` on $\mathrm{Cl}(\mathcal{O}_F)$ written additively. `placesOverPrimes` collects the height-one primes of $\mathcal{O}_F$ containing a rational prime from a set $S$ (finite when $S$ is), `primeClass` their classes, and `sPrimeClasses` is the largest Galois-stable subgroup inside the subgroup they generate, i.e. the $c$ with $\sigma \cdot c$ in that subgroup for every $\sigma$; `sClassGroupRep` is the quotient representation by it, with the quotient morphism `toSClassGroupRep`.
--
--   The quartet `unitsModP`, `sClassTorsionP`, `sClassModP` inflate to the fixing subgroup of $K$ the mod-$p$ reduction of the $S$-unit representation of $L'$ (for the places above the primes of $\mathcal{O}_K$ over $S$) and the $p$-torsion and mod-$p$ reduction of the $S$-class group representation. Finally, `IsNormalLevel` asserts that the fixing subgroup of $K$ normalises that of $L$; under it the fixing subgroup of $K$ acts on the set of orbits of the fixing subgroup of $L$ on any $\mathrm{Aut}_\mathbb{Q}(\bar{\mathbb{Q}})$-set, elements fixing $L$ acting trivially. Applied to $\mathrm{Aut}_\mathbb{Q}(\bar{\mathbb{Q}})$ modulo the image of the local group at an index $v$ of $\mathrm{Unit} \sqcup S$, this yields `placesAbove`, the permutation representation `placesRep` on $\mathbb{Z}/p$-valued finitely supported functions, and the augmentation `placesAug` to the trivial representation.
--
--   **Relation to Mathlib.** Mathlib supplies the functoriality of class groups under ring isomorphisms and $S$-unit subgroups, but not the Galois action on class groups, the Galois-stable subgroup of $S$-prime classes, or the mod-$p$ and $p$-torsion functors on `Rep`; these are the project's own. The permutation representation is built from a vendored copy of a Mathlib definition of the finitely-supported permutation representation, kept under the name [`Representation.ofMulActionFinsupp`](../def/Compat_Mathlib430.html#L28).
--
--   **Where it is used.** These representations are the global input to the Greenberg–Wiles style counting of Selmer groups over a number field: units and class groups modulo $p$, together with the permutation modules on places above the archimedean place and the primes of a fixed finite set, are the objects whose invariants and local conditions enter the Euler-characteristic comparison used in the cyclotomic endgame of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_LevelArithmeticModP.lean

import Mathlib
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_ClassGroup_GaloisAction
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped Pointwise NumberField nonZeroDivisors

namespace NumberField.LevelArith

section Bridge

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)

abbrev levelField : IntermediateField ↥K (AlgebraicClosure ℚ) := IntermediateField.extendScalars hKL

abbrev LevelGal : Type := ↥(levelField K L hKL) ≃ₐ[↥K] ↥(levelField K L hKL)

def levelFieldEquiv : ↥L ≃+* ↥(levelField K L hKL) where
  toFun x := ⟨(x : AlgebraicClosure ℚ), (IntermediateField.mem_extendScalars hKL).2 x.2⟩
  invFun y := ⟨(y : AlgebraicClosure ℚ), (IntermediateField.mem_extendScalars hKL).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] lemma coe_levelFieldEquiv (x : ↥L) : ((levelFieldEquiv K L hKL x : ↥(levelField K L hKL)) : AlgebraicClosure ℚ) = x := rfl

@[simp] lemma coe_levelFieldEquiv_symm (y : ↥(levelField K L hKL)) :
    (((levelFieldEquiv K L hKL).symm y : ↥L) : AlgebraicClosure ℚ) = y := rfl

scoped instance instFiniteDimensionalLevelField [FiniteDimensional ℚ ↥L] : FiniteDimensional ℚ ↥(levelField K L hKL) :=
  LinearEquiv.finiteDimensional ((levelFieldEquiv K L hKL).toAddEquiv.toLinearEquiv fun c x => map_rat_smul _ c x)

scoped instance instNumberFieldLevelField [FiniteDimensional ℚ ↥L] : NumberField ↥(levelField K L hKL) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

scoped instance instNumberFieldBase [FiniteDimensional ℚ ↥K] : NumberField ↥K where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

def levelGal [Normal ↥K ↥(levelField K L hKL)] : ↥K.fixingSubgroup →* LevelGal K L hKL :=
  (AlgEquiv.restrictNormalHom ↥(levelField K L hKL)).comp (IntermediateField.fixingSubgroupEquiv K).toMonoidHom

lemma levelGal_apply_coe [Normal ↥K ↥(levelField K L hKL)] (γ : ↥K.fixingSubgroup) (x : ↥(levelField K L hKL)) :
    ((levelGal K L hKL γ x : ↥(levelField K L hKL)) : AlgebraicClosure ℚ) =
      (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ) :=
  AlgEquiv.restrictNormal_commutes (IntermediateField.fixingSubgroupEquiv K γ) ↥(levelField K L hKL) x

lemma levelGal_eq_one_of_mem [Normal ↥K ↥(levelField K L hKL)] (γ : ↥K.fixingSubgroup)
    (hγ : (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup) : levelGal K L hKL γ = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (by
    rw [levelGal_apply_coe]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ _ ((IntermediateField.mem_extendScalars hKL).1 x.2))

abbrev inflLevel [Normal ↥K ↥(levelField K L hKL)] {k : Type} [CommRing k] (M : Rep k (LevelGal K L hKL)) : Rep k ↥K.fixingSubgroup :=
  Rep.res (levelGal K L hKL) M

lemma inflLevel_ρ_apply [Normal ↥K ↥(levelField K L hKL)] {k : Type} [CommRing k] (M : Rep k (LevelGal K L hKL))
    (γ : ↥K.fixingSubgroup) : (inflLevel K L hKL M).ρ γ = M.ρ (levelGal K L hKL γ) := rfl

end Bridge

section ModP

variable {k : Type} [CommRing k] {G : Type} [Group G]

theorem torsionBy_le_comap {M : Type} [AddCommGroup M] {iM : Module k M} (ρ : Representation k G M) (a : k)
    (g : G) : Submodule.torsionBy k M a ≤ (Submodule.torsionBy k M a).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap, Submodule.mem_torsionBy_iff, ← map_smul]
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [hx, map_zero]

theorem smul_top_le_comap {M : Type} [AddCommGroup M] {iM : Module k M} (ρ : Representation k G M) (a : k)
    (g : G) : (a • (⊤ : Submodule k M)) ≤ (a • (⊤ : Submodule k M)).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap]
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

theorem nsmul_quot_eq_zero {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) (x : V ⧸ ((p : k) • (⊤ : Submodule k V))) :
    p • x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul k]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

theorem nsmul_torsionBy_eq_zero {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) (x : ↥(Submodule.torsionBy k V (p : k))) :
    p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul k]
  exact Subtype.ext ((Submodule.mem_torsionBy_iff (p : k) (x : V)).1 x.2)

scoped instance instModuleZModQuot {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) :
    Module (ZMod p) (V ⧸ ((p : k) • (⊤ : Submodule k V))) :=
  AddCommGroup.zmodModule (nsmul_quot_eq_zero p)

scoped instance instModuleZModTorsion {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) :
    Module (ZMod p) ↥(Submodule.torsionBy k V (p : k)) :=
  AddCommGroup.zmodModule (nsmul_torsionBy_eq_zero p)

def toZMod (p : ℕ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] {inst : Module k M} (σ : Representation k G M) :
    Representation (ZMod p) G M where
  toFun g := (σ g).toAddMonoidHom.toZModLinearMap p
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp] theorem toZMod_apply (p : ℕ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] {inst : Module k M}
    (σ : Representation k G M) (g : G) (m : M) : toZMod p σ g m = σ g m := rfl

def modP (p : ℕ) {V : Type} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) :
    Representation (ZMod p) G (V ⧸ ((p : k) • (⊤ : Submodule k V))) :=
  toZMod p (ρ.quotient _ (smul_top_le_comap ρ (p : k)))

def torsionP (p : ℕ) {V : Type} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) :
    Representation (ZMod p) G ↥(Submodule.torsionBy k V (p : k)) :=
  toZMod p (ρ.subrepresentation _ (torsionBy_le_comap ρ (p : k)))

@[simp] theorem modP_apply_mk (p : ℕ) {V : Type} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) (g : G) (v : V) :
    modP p ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) := rfl

@[simp] theorem torsionP_apply_coe (p : ℕ) {V : Type} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) (g : G)
    (v : ↥(Submodule.torsionBy k V (p : k))) : ((torsionP p ρ g v : ↥(Submodule.torsionBy k V (p : k))) : V) = ρ g v := rfl

abbrev repModP (p : ℕ) (A : Rep k G) : Rep (ZMod p) G := Rep.of (modP p A.ρ)

abbrev repTorsionP (p : ℕ) (A : Rep k G) : Rep (ZMod p) G := Rep.of (torsionP p A.ρ)

def repModPMap (p : ℕ) {A B : Rep k G} (f : A ⟶ B) : repModP p A ⟶ repModP p B :=
  Rep.ofHom ⟨(Submodule.mapQ ((p : k) • (⊤ : Submodule k A)) ((p : k) • (⊤ : Submodule k B)) f.hom.toLinearMap (fun x hx => by
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)).toAddMonoidHom.toZModLinearMap p,
    fun g => LinearMap.ext fun x => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (f.hom (A.ρ g a)) = Submodule.Quotient.mk (B.ρ g (f.hom a))
      rw [Rep.hom_comm_apply]⟩

@[simp] theorem repModPMap_hom_mk (p : ℕ) {A B : Rep k G} (f : A ⟶ B) (a : A) :
    (repModPMap p f).hom (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f.hom a) := rfl

def repTorsionPMap (p : ℕ) {A B : Rep k G} (f : A ⟶ B) : repTorsionP p A ⟶ repTorsionP p B :=
  Rep.ofHom ⟨(f.hom.toLinearMap.restrict (p := Submodule.torsionBy k A (p : k)) (q := Submodule.torsionBy k B (p : k)) (fun x hx => by
      rw [Submodule.mem_torsionBy_iff] at hx ⊢
      rw [← map_smul, hx, map_zero])).toAddMonoidHom.toZModLinearMap p,
    fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply f g (x : A))⟩

@[simp] theorem repTorsionPMap_hom_apply_coe (p : ℕ) {A B : Rep k G} (f : A ⟶ B) (a : ↥(Submodule.torsionBy k A (p : k))) :
    (((repTorsionPMap p f).hom a : ↥(Submodule.torsionBy k B (p : k))) : B) = f.hom a := rfl

end ModP

section ClassGroups

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]

abbrev ringOfIntegersAut (σ : F ≃ₐ[E] F) : 𝓞 F ≃+* 𝓞 F := NumberField.RingOfIntegers.mapRingEquiv (σ : F ≃+* F)

def classGroupAut : (F ≃ₐ[E] F) →* MulAut (ClassGroup (𝓞 F)) where
  toFun σ := ClassGroup.mulEquiv (ringOfIntegersAut E F σ)
  map_one' := MulEquiv.ext fun C => by
    change ClassGroup.mulEquiv (ringOfIntegersAut E F 1) C = C
    have : ringOfIntegersAut E F 1 = RingEquiv.refl _ := RingEquiv.ext fun _ => rfl
    rw [this, ClassGroup.mulEquiv_refl_apply]
  map_mul' σ τ := MulEquiv.ext fun C => by
    change ClassGroup.mulEquiv (ringOfIntegersAut E F (σ * τ)) C =
      ClassGroup.mulEquiv (ringOfIntegersAut E F σ) (ClassGroup.mulEquiv (ringOfIntegersAut E F τ) C)
    have : ringOfIntegersAut E F (σ * τ) = (ringOfIntegersAut E F τ).trans (ringOfIntegersAut E F σ) := RingEquiv.ext fun _ => rfl
    rw [this, ClassGroup.mulEquiv_trans_apply]

scoped instance instMulDistribMulActionClassGroup : MulDistribMulAction (F ≃ₐ[E] F) (ClassGroup (𝓞 F)) :=
  MulDistribMulAction.compHom _ (classGroupAut E F)

lemma smul_classGroup_def (σ : F ≃ₐ[E] F) (C : ClassGroup (𝓞 F)) : σ • C = ClassGroup.mulEquiv (ringOfIntegersAut E F σ) C := rfl

lemma smul_mk0 (σ : F ≃ₐ[E] F) (P : (Ideal (𝓞 F))⁰) : σ • ClassGroup.mk0 P = ClassGroup.mk0 (Ideal.mapNonZero (ringOfIntegersAut E F σ) P) :=
  ClassGroup.mulEquiv_mk0 _ P

abbrev classGroupRep : Rep ℤ (F ≃ₐ[E] F) := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (ClassGroup (𝓞 F))

def placesOverPrimes (S : Set Nat.Primes) : Set (HeightOneSpectrum (𝓞 F)) := {w | ∃ p ∈ S, ((p : ℕ) : 𝓞 F) ∈ w.asIdeal}

omit [NumberField F] in
lemma mem_placesOverPrimes_iff (S : Set Nat.Primes) (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ placesOverPrimes F S ↔ ∃ p ∈ S, ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := Iff.rfl

theorem placesOverPrimes_finite (S : Finset Nat.Primes) : (placesOverPrimes F (S : Set Nat.Primes)).Finite := by
  refine (S.finite_toSet.biUnion fun p _ => (Ideal.finite_factors (I := Ideal.span {((p : ℕ) : 𝓞 F)}) ?_)).subset ?_
  · rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  · rintro w ⟨p, hp, hw⟩
    exact Set.mem_biUnion hp ((Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem _).2 hw))

def placesOverPrimesFinset (S : Finset Nat.Primes) : Finset (HeightOneSpectrum (𝓞 F)) := (placesOverPrimes_finite F S).toFinset

lemma mem_placesOverPrimesFinset (S : Finset Nat.Primes) (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ placesOverPrimesFinset F S ↔ w ∈ placesOverPrimes F (S : Set Nat.Primes) := Set.Finite.mem_toFinset _

def primeClass (w : HeightOneSpectrum (𝓞 F)) : ClassGroup (𝓞 F) :=
  ClassGroup.mk0 ⟨w.asIdeal, mem_nonZeroDivisors_iff_ne_zero.2 (by simpa using w.ne_bot)⟩

def sPrimeClasses (S : Set Nat.Primes) : Subgroup (ClassGroup (𝓞 F)) :=
  ⨅ σ : F ≃ₐ[E] F, (Subgroup.closure (primeClass F '' placesOverPrimes F S)).comap (MulDistribMulAction.toMonoidHom (ClassGroup (𝓞 F)) σ)

lemma mem_sPrimeClasses_iff (S : Set Nat.Primes) (c : ClassGroup (𝓞 F)) :
    c ∈ sPrimeClasses E F S ↔ ∀ σ : F ≃ₐ[E] F, σ • c ∈ Subgroup.closure (primeClass F '' placesOverPrimes F S) := by
  simp only [sPrimeClasses, Subgroup.mem_iInf, Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply]

lemma smul_mem_sPrimeClasses (S : Set Nat.Primes) (τ : F ≃ₐ[E] F) {c : ClassGroup (𝓞 F)} (hc : c ∈ sPrimeClasses E F S) :
    τ • c ∈ sPrimeClasses E F S := by
  rw [mem_sPrimeClasses_iff] at hc ⊢
  intro σ
  rw [← mul_smul]
  exact hc (σ * τ)

def sPrimeClassesSubmodule (S : Set Nat.Primes) : Submodule ℤ (Additive (ClassGroup (𝓞 F))) :=
  (Subgroup.toAddSubgroup (sPrimeClasses E F S)).toIntSubmodule

lemma mem_sPrimeClassesSubmodule (S : Set Nat.Primes) (x : Additive (ClassGroup (𝓞 F))) :
    x ∈ sPrimeClassesSubmodule E F S ↔ Additive.toMul x ∈ sPrimeClasses E F S := Iff.rfl

abbrev sClassGroupRep (S : Set Nat.Primes) : Rep ℤ (F ≃ₐ[E] F) :=
  Rep.of ((classGroupRep E F).ρ.quotient (sPrimeClassesSubmodule E F S) fun σ _ hx => smul_mem_sPrimeClasses E F S σ hx)

def toSClassGroupRep (S : Set Nat.Primes) : classGroupRep E F ⟶ sClassGroupRep E F S :=
  Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩

lemma toSClassGroupRep_hom_apply (S : Set Nat.Primes) (x : classGroupRep E F) :
    (toSClassGroupRep E F S).hom x = Submodule.Quotient.mk x := rfl

lemma toSClassGroupRep_hom_surjective (S : Set Nat.Primes) : Function.Surjective (toSClassGroupRep E F S).hom :=
  Submodule.mkQ_surjective _

end ClassGroups

section Quartet

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (S : Finset Nat.Primes) (p : ℕ)

abbrev unitsModP : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (repModP p (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S)))

abbrev sClassTorsionP : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (repTorsionP p (sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes)))

abbrev sClassModP : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (repModP p (sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes)))

end Quartet

section Places

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ))

abbrev IsNormalLevel : Prop := ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup

@[reducible] def orbitQuotientAction (hnorm : IsNormalLevel K L) (X : Type) [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X] :
    MulAction ↥K.fixingSubgroup (MulAction.orbitRel.Quotient ↥L.fixingSubgroup X) where
  smul γ := Quotient.map' (fun x : X => (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x) (fun a b hab => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
    obtain ⟨s, rfl⟩ := hab
    refine ⟨⟨(γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * s * (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹, hnorm _ γ.2 _ s.2⟩, ?_⟩
    show ((γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * s * (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹) • ((γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • b) = (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • ((s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • b)
    rw [← mul_smul, ← mul_smul, inv_mul_cancel_right])
  one_smul q := Quotient.inductionOn' q fun x => congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel ↥L.fixingSubgroup X))
    (one_smul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x)
  mul_smul γ δ q := Quotient.inductionOn' q fun x => congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel ↥L.fixingSubgroup X))
    (mul_smul (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) x)

lemma orbitQuotientAction_smul_mk (hnorm : IsNormalLevel K L) (X : Type) [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X] (γ : ↥K.fixingSubgroup) (x : X) :
    (letI := orbitQuotientAction K L hnorm X
     γ • (Quotient.mk'' x : MulAction.orbitRel.Quotient ↥L.fixingSubgroup X)) = Quotient.mk'' ((γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x) := rfl

lemma orbitQuotientAction_smul_eq_of_mem (hnorm : IsNormalLevel K L) (X : Type) [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X] (γ : ↥K.fixingSubgroup)
    (hγ : (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup) (q : MulAction.orbitRel.Quotient ↥L.fixingSubgroup X) :
    (letI := orbitQuotientAction K L hnorm X; γ • q) = q := by
  induction q using Quotient.inductionOn' with
  | h x => exact Quotient.sound' ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit_iff.2 ⟨⟨_, hγ⟩, rfl⟩))

abbrev placesAbove (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) : Type :=
  MulAction.orbitRel.Quotient ↥L.fixingSubgroup ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (ExtCitation.extArithLoc S v).range)

def placesRep (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) (p : ℕ) :
    Rep (ZMod p) ↥K.fixingSubgroup :=
  Rep.of (@Representation.ofMulActionFinsupp (ZMod p) _ ↥K.fixingSubgroup _ (placesAbove L S v) (orbitQuotientAction K L hnorm _))

lemma placesRep_ρ_single (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) (p : ℕ)
    (γ : ↥K.fixingSubgroup) (x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (ExtCitation.extArithLoc S v).range) (c : ZMod p) :
    (placesRep K L hnorm S v p).ρ γ (Finsupp.single (Quotient.mk'' x) c) = Finsupp.single (Quotient.mk'' ((γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x)) c :=
  Finsupp.mapDomain_single

def placesAug (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) (p : ℕ) :
    placesRep K L hnorm S v p ⟶ Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p) :=
  Rep.ofHom ⟨Finsupp.linearCombination (ZMod p) (fun _ => (1 : ZMod p)), fun γ => Finsupp.lhom_ext fun q c => by
    change Finsupp.linearCombination (ZMod p) (fun _ => (1 : ZMod p)) (Finsupp.mapDomain _ (Finsupp.single q c)) =
      Finsupp.linearCombination (ZMod p) (fun _ => (1 : ZMod p)) (Finsupp.single q c)
    rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single]⟩

lemma placesAug_hom_single (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) (p : ℕ)
    (q : placesAbove L S v) (c : ZMod p) : (placesAug K L hnorm S v p).hom (Finsupp.single q c) = c := by
  change Finsupp.linearCombination (ZMod p) (fun _ => (1 : ZMod p)) (Finsupp.single q c) = c
  rw [Finsupp.linearCombination_single, smul_eq_mul, mul_one]

end Places

end NumberField.LevelArith

end


