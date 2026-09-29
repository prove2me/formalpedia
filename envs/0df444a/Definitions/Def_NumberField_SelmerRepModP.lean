-- Prove2me | Definitions.Def_NumberField_SelmerRepModP
-- name    : NumberField_SelmerRepModP
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/ac124a27-44a9-59cf-a2b4-f9bfc7cae412
-- title:
--   Mod-p Selmer representations of F×/(F×)p
-- statement:
--   Fix number fields $E \subseteq F$ with $F$ an $E$-algebra, a finite set $S$ of height-one primes of $\mathcal{O}_E$ and a natural number $p$. The module defines `unitsModPow F p` as the quotient group $F^\times / (F^\times)^p$, i.e. $F^\times$ modulo the image of the $p$-th power endomorphism, and equips it with the action of $F \simeq_{\mathrm{alg}[E]} F$ induced by the action on units (`unitsModPowMap`, recorded as a scoped `MulDistribMulAction`); every element of the quotient is $p$-torsion. `selmer` is Mathlib's Selmer group `selmerGroup` for $\mathcal{O}_F \subseteq F$ with exponent $p$ and with the set of places taken to be those $w$ of $F$ whose restriction to $\mathcal{O}_E$ lies in $S$: the classes whose valuation modulo $p$-th powers is trivial at every $w$ not of that form. Since that subgroup need not be Galois-stable as defined, `selmerStable` is the intersection over all $\sigma \in \mathrm{Gal}$ of the pullbacks $\sigma^{-1}(\mathrm{selmer})$, which is stable by construction; `selmerSubmodule` is the corresponding $\mathbb{Z}$-submodule of the additive group, `selmerRepInt` the resulting subrepresentation of $\mathrm{Gal}$ on it over $\mathbb{Z}$, and `selmerRepField` the same module viewed as a representation over $\mathbb{Z}/p$, using that $p$ annihilates it.
--
--   The comparison with $S$-units is provided by `mk_mem_selmerStable`: the class of a unit all of whose Galois conjugates have trivial valuation outside the places above $S$ lies in `selmerStable`. This gives the $\mathbb{Z}$-linear map `fromSUnitsLinear` from the $S$-unit representation and, after reduction, the morphism of $\mathbb{Z}/p$-representations `fromSUnitsModP` from `repModP p` of the $S$-unit representation to `selmerRepField`; an auxiliary lemma `smul_top_le_ker` supplies the factorisation through the quotient by $p$.
--
--   Finally, for intermediate fields $K \le L$ of $\overline{\mathbb{Q}}$ with $L$ normal over $K$ and a finite set $S$ of rational primes, `selmerRep` is `selmerRepField` for $K \subseteq L$ at the places of $K$ above $S$, inflated along `levelGal` to a representation of the fixing subgroup of $K$, and `unitsModPToSelmerRep` is the image of `fromSUnitsModP` under that restriction functor.
--
--   **Relation to Mathlib.** `selmer` is Mathlib's `IsDedekindDomain.selmerGroup`, instantiated at $\mathcal{O}_F \subseteq F$ with exponent $p$; the Galois action on $F^\times/(F^\times)^p$, the stable subgroup, the associated $\mathbb{Z}$- and $\mathbb{Z}/p$-representations (built on Mathlib's `Rep.ofMulDistribMulAction`) and the map from $S$-units are the project's own.
--
--   **Where it is used.** These representations are the Selmer-group side of the level arithmetic: they receive the mod-$p$ Kummer map from the $S$-units of the level field and feed the class-group and Selmer-group counting arguments used in the Greenberg–Wiles style bookkeeping.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_SelmerRepModP.lean

import Mathlib
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped NumberField NumberField.LevelArith Pointwise

namespace NumberField.LevelArith

section Selmer

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ)

def unitsModPow : Type := Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range

instance instCommGroupUnitsModPow : CommGroup (unitsModPow F p) :=
  inferInstanceAs (CommGroup (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

abbrev unitsModPow.mk (x : Fˣ) : unitsModPow F p := (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range)

omit [NumberField E] [NumberField F] in
theorem unitsModPow.mk_surjective : Function.Surjective (unitsModPow.mk F p) := QuotientGroup.mk_surjective

omit [NumberField E] [NumberField F] in
theorem unitsModPow.mk_pow (x : Fˣ) : unitsModPow.mk F p (x ^ p) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩

omit [NumberField E] [NumberField F] in
theorem unitsModPow.pow_eq_one (q : unitsModPow F p) : q ^ p = 1 := by
  obtain ⟨x, rfl⟩ := unitsModPow.mk_surjective F p q
  show (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) ^ p = 1
  rw [← QuotientGroup.mk_pow]
  exact unitsModPow.mk_pow F p x

omit [NumberField E] [NumberField F] in
theorem nsmul_additive_unitsModPow (a : Additive (unitsModPow F p)) : p • a = 0 :=
  Additive.toMul.injective (by rw [toMul_nsmul, toMul_zero]; exact unitsModPow.pow_eq_one F p _)

omit [NumberField E] [NumberField F] in
theorem range_powMonoidHom_le_comap (σ : F ≃ₐ[E] F) :
    (powMonoidHom p : Fˣ →* Fˣ).range ≤ ((powMonoidHom p : Fˣ →* Fˣ).range).comap (MulDistribMulAction.toMonoidHom Fˣ σ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨σ • x, by rw [MulDistribMulAction.toMonoidHom_apply, powMonoidHom_apply, powMonoidHom_apply, smul_pow']⟩

def unitsModPowMap (σ : F ≃ₐ[E] F) : unitsModPow F p →* unitsModPow F p :=
  (QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom Fˣ σ) (range_powMonoidHom_le_comap E F p σ) :
    (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) →* (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

omit [NumberField E] [NumberField F] in
@[simp] theorem unitsModPowMap_mk (σ : F ≃ₐ[E] F) (x : Fˣ) : unitsModPowMap E F p σ (unitsModPow.mk F p x) = unitsModPow.mk F p (σ • x) := rfl

scoped instance instMulDistribMulActionUnitsModPow : MulDistribMulAction (F ≃ₐ[E] F) (unitsModPow F p) where
  smul σ := unitsModPowMap E F p σ
  one_smul q := by
    obtain ⟨x, rfl⟩ := unitsModPow.mk_surjective F p q
    exact congrArg (unitsModPow.mk F p) (one_smul (F ≃ₐ[E] F) x)
  mul_smul σ τ q := by
    obtain ⟨x, rfl⟩ := unitsModPow.mk_surjective F p q
    exact congrArg (unitsModPow.mk F p) (mul_smul σ τ x)
  smul_mul σ a b := map_mul (unitsModPowMap E F p σ) a b
  smul_one σ := map_one (unitsModPowMap E F p σ)

omit [NumberField E] [NumberField F] in
@[simp] theorem smul_mk (σ : F ≃ₐ[E] F) (x : Fˣ) : σ • unitsModPow.mk F p x = unitsModPow.mk F p (σ • x) := rfl

def selmer : Subgroup (unitsModPow F p) :=
  (selmerGroup (R := 𝓞 F) (K := F) (S := NumberField.SUnits.placesAbove E F S) (n := p) : Subgroup (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

omit [NumberField E] in
theorem mem_selmer_iff (x : Fˣ) : unitsModPow.mk F p x ∈ selmer E F S p ↔
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ NumberField.SUnits.placesAbove E F S →
      v.valuationOfNeZeroMod p (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) = 1 := Iff.rfl

def selmerStable : Subgroup (unitsModPow F p) :=
  ⨅ σ : F ≃ₐ[E] F, (selmer E F S p).comap (MulDistribMulAction.toMonoidHom (unitsModPow F p) σ)

omit [NumberField E] in
theorem mem_selmerStable_iff (x : unitsModPow F p) : x ∈ selmerStable E F S p ↔ ∀ σ : F ≃ₐ[E] F, σ • x ∈ selmer E F S p := by
  simp only [selmerStable, Subgroup.mem_iInf, Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply]

omit [NumberField E] in
theorem smul_mem_selmerStable (τ : F ≃ₐ[E] F) {x : unitsModPow F p} (hx : x ∈ selmerStable E F S p) : τ • x ∈ selmerStable E F S p := by
  rw [mem_selmerStable_iff] at hx ⊢
  intro σ
  rw [← mul_smul]
  exact hx (σ * τ)

def selmerSubmodule : Submodule ℤ (Additive (unitsModPow F p)) := (Subgroup.toAddSubgroup (selmerStable E F S p)).toIntSubmodule

omit [NumberField E] in
theorem mem_selmerSubmodule (x : Additive (unitsModPow F p)) : x ∈ selmerSubmodule E F S p ↔ Additive.toMul x ∈ selmerStable E F S p := Iff.rfl

abbrev selmerRepInt : Rep ℤ (F ≃ₐ[E] F) :=
  Rep.of ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitsModPow F p)).ρ.subrepresentation (selmerSubmodule E F S p)
    fun σ _ hx => smul_mem_selmerStable E F S p σ hx)

omit [NumberField E] in
theorem nsmul_selmer_eq_zero (x : selmerRepInt E F S p) : p • x = 0 :=
  Subtype.ext (nsmul_additive_unitsModPow F p _)

scoped instance instModuleZModSelmer : Module (ZMod p) (selmerRepInt E F S p) := AddCommGroup.zmodModule (nsmul_selmer_eq_zero E F S p)

omit [NumberField E] in

@[simp] theorem selmerRepInt_ρ_apply (σ : F ≃ₐ[E] F) (x : selmerRepInt E F S p) :
    (Subtype.val ((selmerRepInt E F S p).ρ σ x) : Additive (unitsModPow F p)) =
      Additive.ofMul (σ • Additive.toMul (Subtype.val x : Additive (unitsModPow F p))) := rfl

abbrev selmerRepField : Rep (ZMod p) (F ≃ₐ[E] F) := Rep.of (toZMod p (selmerRepInt E F S p).ρ)

omit [NumberField E] in

@[simp] theorem selmerRepField_ρ_apply (σ : F ≃ₐ[E] F) (x : selmerRepField E F S p) :
    (Subtype.val ((selmerRepField E F S p).ρ σ x) : Additive (unitsModPow F p)) =
      Additive.ofMul (σ • Additive.toMul (Subtype.val x : Additive (unitsModPow F p))) := rfl

omit [NumberField E] in

theorem mk_mem_selmerStable (u : NumberField.SUnits.sUnitsRep E F S) :
    unitsModPow.mk F p (NumberField.SUnits.val E F S u) ∈ selmerStable E F S p := by
  rw [mem_selmerStable_iff]
  intro σ
  rw [smul_mk, mem_selmer_iff]
  intro v hv
  have hval : v.valuation F ((σ • NumberField.SUnits.val E F S u : Fˣ) : F) = 1 :=
    (NumberField.SUnits.mem_sUnits_iff E F S _).1 (NumberField.SUnits.val_mem E F S u) σ v hv
  have h1 : v.valuationOfNeZero (σ • NumberField.SUnits.val E F S u) = 1 := by
    apply WithZero.coe_injective
    rw [HeightOneSpectrum.valuationOfNeZero_eq]
    exact hval
  simp only [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.coe_comp, Function.comp_apply]
  erw [QuotientGroup.map_mk, h1, QuotientGroup.mk_one, map_one]

omit [NumberField E] [NumberField F] in

theorem smul_top_le_ker {k : Type} [CommRing k] {V W : Type} [AddCommGroup V] [AddCommGroup W] {iV : Module k V} {iW : Module k W}
    (f : V →ₗ[k] W) (hW : ∀ w : W, p • w = 0) : (p : k) • (⊤ : Submodule k V) ≤ LinearMap.ker f := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [LinearMap.mem_ker, map_smul, Nat.cast_smul_eq_nsmul]
  exact hW _

def fromSUnitsLinear : NumberField.SUnits.sUnitsRep E F S →ₗ[ℤ] selmerRepInt E F S p where
  toFun u := ⟨Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u)), mk_mem_selmerStable E F S p u⟩
  map_add' _ _ := rfl
  map_smul' n u := Subtype.ext (by
    change Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S (n • u))) =
      n • Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u))
    rw [NumberField.SUnits.val_zsmul]
    exact (QuotientGroup.mk_zpow ((powMonoidHom p : Fˣ →* Fˣ).range) (NumberField.SUnits.val E F S u) n :))

def fromSUnitsModP : repModP p (NumberField.SUnits.sUnitsRep E F S) ⟶ selmerRepField E F S p :=
  Rep.ofHom ⟨(Submodule.liftQ _ (fromSUnitsLinear E F S p) (smul_top_le_ker p _ (nsmul_selmer_eq_zero E F S p))).toAddMonoidHom.toZModLinearMap p,
    fun σ => LinearMap.ext fun x => by
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl⟩

omit [NumberField E] in
theorem fromSUnitsModP_hom_mk (u : NumberField.SUnits.sUnitsRep E F S) :
    (((fromSUnitsModP E F S p).hom (Submodule.Quotient.mk u)).1 : Additive (unitsModPow F p)) =
      Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u)) := rfl

end Selmer

section Level

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (S : Finset Nat.Primes) (p : ℕ)

abbrev selmerRep : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (selmerRepField ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p)

abbrev unitsModPToSelmerRep : unitsModP K L hKL S p ⟶ selmerRep K L hKL S p :=
  (Rep.resFunctor (levelGal K L hKL)).map (fromSUnitsModP ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p)

end Level

end NumberField.LevelArith

end


