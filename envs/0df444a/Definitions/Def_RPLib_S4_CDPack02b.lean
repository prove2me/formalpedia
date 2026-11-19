-- Prove2me | Definitions.Def_RPLib_S4_CDPack02b
-- name    : RPLib_S4_CDPack02b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:14:53.578894+00:00
-- url     : https://prove2.me/theorems/d6f88032-06ad-49e3-a28b-e271b27cfaba
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 2b of 71
-- statement:
--   Part 2b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_LocKumJ`: S4-PD (4), E4L part 2: tame inertia for a subgroup of finite exponent-index in `I(Q)`
--   * `Def_RP_Cone_LocRam`: S4-PD (4), E4L part 3: the ramification converse at a finite level
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_TameInertiaMain
import Definitions.Def_RPLib_S4_CDPack02
import Definitions.Def_RPLib_S4_TameInertiaLift
import Definitions.Def_RPLib_S4_KummerRam

/-!
# Curve-duality library package, part 2b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_LocKumJ`: S4-PD (4), E4L part 2: tame inertia for a subgroup of finite exponent-index in `I(Q)`
* `Def_RP_Cone_LocRam`: S4-PD (4), E4L part 3: the ramification converse at a finite level
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_LocKumJ =====
section

/-!
# S4-PD (4), E4L part 2: tame inertia for a subgroup of finite exponent-index in `I(Q)`

* `exists_div_char`: an additive character `r : G → ℤ/(N d)` whose image contains `p^k d` (`p` prime to `N d`) yields,
  by dividing by the generator `e ∣ d` of its image, an additive character `f ∘ r : G → ℤ/N` taking the value `1`.
* `tame_inertia_le`: for `J ≤ I(Q)` with `σ ^ (p^k d) ∈ J` for all `σ ∈ I(Q)` (e.g. `J = I(Q) ⊓ ker π` for a finite
  quotient `π` of order `p^k d`), there are a locally constant character `θ_J : J → ℤ/N` and `τ₀ ∈ J` with
  `θ_J τ₀ = 1`, `θ_J` invariant under conjugation by `I(Q)`, and every locally constant character `J → ℤ/N` a multiple
  of `θ_J` (so `Hom_cont(J, ℤ/N) ≅ ℤ/N` by evaluation at `τ₀`). Uses `tame_inertia` at level `N d` and the pigeonhole
  bound `exists_ne_eq_of_family_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

section Div

/-- Dividing an additive character `r : G → ℤ/(N d)` by the generator of its image. -/
theorem exists_div_char {G : Type} [Group G] {N d p k : ℕ} [NeZero N] [NeZero d] (hp0 : 0 < p)
    (hp : Nat.Coprime p (N * d)) (r : G → ZMod (N * d)) (hr : ∀ σ τ, r (σ * τ) = r σ + r τ) {g : G}
    (hg : r g = ((p ^ k * d : ℕ) : ZMod (N * d))) :
    ∃ f : ZMod (N * d) → ZMod N, (∀ σ τ, f (r (σ * τ)) = f (r σ) + f (r τ)) ∧ ∃ τ, f (r τ) = 1 := by
  classical
  have : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne d)⟩
  have h1 : r 1 = 0 := by
    have h := hr 1 1
    rw [mul_one] at h
    linear_combination -h
  have hinv : ∀ σ, r σ⁻¹ = -r σ := fun σ => by
    have h := hr σ⁻¹ σ
    rw [inv_mul_cancel, h1] at h
    linear_combination -h
  have hpow : ∀ σ (n : ℕ), r (σ ^ n) = (n : ZMod (N * d)) * r σ := by
    intro σ n
    induction n with
    | zero => rw [pow_zero, h1, Nat.cast_zero, zero_mul]
    | succ n ih => rw [pow_succ, hr, ih, Nat.cast_succ]; ring
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ σ, r σ = (n : ZMod (N * d)) :=
    ⟨p ^ k * d, Nat.mul_pos (pow_pos hp0 k) (NeZero.pos d), g, hg⟩
  obtain ⟨he0, τ₀, hτ₀⟩ := Nat.find_spec hex
  have hdvd : ∀ n : ℕ, (∃ σ, r σ = (n : ZMod (N * d))) → Nat.find hex ∣ n := by
    rintro n ⟨σ, hσ⟩
    have hlt : n % Nat.find hex < Nat.find hex := Nat.mod_lt _ he0
    by_contra hne
    have hpos : 0 < n % Nat.find hex := Nat.pos_of_ne_zero fun h => hne (Nat.dvd_of_mod_eq_zero h)
    refine Nat.find_min hex hlt ⟨hpos, σ * (τ₀ ^ (n / Nat.find hex))⁻¹, ?_⟩
    have key : (n : ZMod (N * d)) = ((n % Nat.find hex : ℕ) : ZMod (N * d)) +
        ((Nat.find hex : ℕ) : ZMod (N * d)) * ((n / Nat.find hex : ℕ) : ZMod (N * d)) := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    rw [hr, hinv, hpow, hσ, hτ₀, key]
    ring
  set e := Nat.find hex with he_def
  have he_Nd : e ∣ N * d := hdvd (N * d) ⟨1, by rw [h1, ZMod.natCast_self]⟩
  have he_D : e ∣ p ^ k * d := hdvd _ ⟨g, hg⟩
  have hcop : Nat.Coprime e (p ^ k) := Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left he_Nd hp.symm)
  obtain ⟨c, hc⟩ : e ∣ d := hcop.dvd_of_dvd_mul_left he_D
  refine ⟨fun y => ((y.val / e : ℕ) : ZMod N), fun σ τ => ?_, τ₀, ?_⟩
  · obtain ⟨a, ha⟩ := hdvd (r σ).val ⟨σ, (ZMod.natCast_zmod_val _).symm⟩
    obtain ⟨b, hb⟩ := hdvd (r τ).val ⟨τ, (ZMod.natCast_zmod_val _).symm⟩
    have hNd : N * d = e * (N * c) := by rw [hc]; ring
    show (((r (σ * τ)).val / e : ℕ) : ZMod N) = (((r σ).val / e : ℕ) : ZMod N) + (((r τ).val / e : ℕ) : ZMod N)
    rw [hr, ZMod.val_add, ha, hb, ← mul_add, hNd, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ he0,
      Nat.mul_div_cancel_left _ he0, Nat.mul_div_cancel_left _ he0]
    conv_rhs => rw [← Nat.cast_add, ← Nat.mod_add_div (a + b) (N * c)]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul, add_zero]
  · show (((r τ₀).val / e : ℕ) : ZMod N) = 1
    by_cases hN1 : N = 1
    · subst hN1
      have h := (ZMod.natCast_eq_natCast_iff' ((r τ₀).val / e) 1 1).2 (by simp [Nat.mod_one])
      rwa [Nat.cast_one] at h
    · have hdlt : d < N * d := by
        have h2 : 2 ≤ N := by have := NeZero.pos N; omega
        have := NeZero.pos d
        nlinarith
      have hlt : e < N * d := lt_of_le_of_lt (Nat.le_of_dvd (NeZero.pos d) ⟨c, hc⟩) hdlt
      rw [hτ₀, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.div_self he0, Nat.cast_one]

end Div

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

omit [IsDomain A] [IsFractionRing A K] in
/-- A unit `n` of `A` (`K` of characteristic `p`) is prime to `p`. -/
theorem coprime_of_isUnit {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (hn : IsUnit (n : A)) : Nat.Coprime p n := by
  refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h => ?_
  have h1 : IsUnit (n : K) := by simpa using hn.map (algebraMap A K)
  rw [(CharP.cast_eq_zero_iff K p n).2 h] at h1
  exact not_isUnit_zero h1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Tame inertia for `J ≤ I(Q)`** with `σ ^ (p^k d) ∈ J` for `σ ∈ I(Q)`: `Hom_cont(J, ℤ/N)` is cyclic of order `N`,
generated by an `I(Q)`-conjugation invariant `θ_J` with `θ_J τ₀ = 1`. -/
theorem tame_inertia_le {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ} [NeZero N] [NeZero d]
    (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0)) {ζ : maxUnram A K}
    (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a))
    {J : Subgroup (Pi1 A K)} (hJ : J ≤ Q.inertia (Pi1 A K)) (k : ℕ)
    (hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ J) :
    ∃ θ : J → ZMod N, ∃ τ₀ : J, IsLocallyConstant θ ∧ (∀ σ τ, θ (σ * τ) = θ σ + θ τ) ∧ θ τ₀ = 1 ∧
      (∀ g ∈ Q.inertia (Pi1 A K), ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J),
        θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩) ∧
      ∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ τ, χ (σ * τ) = χ σ + χ τ) →
        ∃ c : ZMod N, ∀ σ, χ σ = c * θ σ := by
  have : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne d)⟩
  obtain ⟨θ', hθc, hθm, ⟨σ₀, hθ1⟩, -, -⟩ := exists_tame_char (p := p) hQ hNA hNR hζ hζI x hx ha
  let ι : J → Q.inertia (Pi1 A K) := fun σ => ⟨σ, hJ σ.2⟩
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  let r : J → ZMod (N * d) := fun σ => θ' (ι σ)
  have hr : ∀ σ τ, r (σ * τ) = r σ + r τ := fun σ τ => hθm (ι σ) (ι τ)
  have h1 : θ' 1 = 0 := by
    have h := hθm 1 1
    rw [mul_one] at h
    linear_combination -h
  have hpow : ∀ n : ℕ, θ' (σ₀ ^ n) = (n : ZMod (N * d)) := by
    intro n
    induction n with
    | zero => rw [pow_zero, h1, Nat.cast_zero]
    | succ n ih => rw [pow_succ, hθm, ih, hθ1, Nat.cast_succ]
  let g : J := ⟨(σ₀ : Pi1 A K) ^ (p ^ k * d), hd _ σ₀.2⟩
  have hg : r g = ((p ^ k * d : ℕ) : ZMod (N * d)) := by
    rw [← hpow]
    show θ' (ι g) = _
    congr 1
  have hp : Nat.Coprime p (N * d) := coprime_of_isUnit (K := K) hNA
  obtain ⟨f, hf, τ₀, hτ₀⟩ := exists_div_char (Fact.out : p.Prime).pos hp r hr hg
  let θ : J → ZMod N := fun σ => f (r σ)
  have hθm' : ∀ σ τ, θ (σ * τ) = θ σ + θ τ := hf
  have hθc' : IsLocallyConstant θ := (hθc.comp_continuous hιc).comp f
  have hconj : ∀ g ∈ Q.inertia (Pi1 A K), ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J),
      θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩ := by
    intro g hg σ hσ hσ'
    show f (θ' (ι ⟨g⁻¹ * σ * g, hσ'⟩)) = f (θ' (ι ⟨σ, hσ⟩))
    congr 1
    have e : ι ⟨g⁻¹ * σ * g, hσ'⟩ = (⟨g, hg⟩ : Q.inertia (Pi1 A K))⁻¹ * ι ⟨σ, hσ⟩ * ⟨g, hg⟩ := rfl
    have hinv : θ' (⟨g, hg⟩ : Q.inertia (Pi1 A K))⁻¹ = -θ' ⟨g, hg⟩ := by
      have h := hθm (⟨g, hg⟩ : Q.inertia (Pi1 A K))⁻¹ ⟨g, hg⟩
      rw [inv_mul_cancel, h1] at h
      linear_combination -h
    rw [e, hθm, hθm, hinv]
    ring
  have hN : IsUnit (N : R0) := by
    rw [Nat.cast_mul] at hNR
    exact isUnit_of_mul_isUnit_left hNR
  have hζN : IsPrimitiveRoot (ζ ^ d) N := IsPrimitiveRoot.pow (NeZero.pos _) hζ (mul_comm N d)
  have hζJ : ∀ σ ∈ J, σ (ζ ^ d) = ζ ^ d := fun σ hσ => by rw [map_pow, hζI σ (hJ hσ)]
  exact ⟨θ, τ₀, hθc', hθm', hτ₀, hconj, fun χ hχc hχ => exists_eq_mul_of_surj
    (fun χ' hc' h' => exists_ne_eq_of_family_le hQ hN hζN hJ hζJ χ' hc' h') hθc' hθm' hτ₀ hχc hχ⟩

end

end TameInertia
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_LocRam =====
section

/-!
# S4-PD (4), E4L part 3: the ramification converse at a finite level

* `log_val_eq_card_mul`: for a finite Galois level `L` over `K` and a subextension `F ≤ L`, the valuation of `x ∈ F` at
  a prime `w` of `B_L = integralClosure R0 L` is `#(I_w ∩ Gal(L/F))` times its valuation at `w ∩ B_F` (Hilbert
  ramification theory, `Ideal.card_inertia_eq_ramificationIdxIn`, for the subgroup `Gal(L/F)` over `B_F`).
* `dvd_val_of_fix_lev` (R): `γ ∈ K_U`, `γ ^ N = a ∈ M` for a finite level `M ≤ K_U`, and every inertia element at `Q`
  fixing `M` fixes `γ`: then `N ∣ v(a)` at `v = Q ∩ B_M` (converse of `fix_of_val_dvd_lev`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- Valuations of elements of `F ≤ L` at a prime `w` of `B_L` are `#(I_w ∩ Gal(L/F))` times those at `w ∩ B_F`. -/
theorem log_val_eq_card_mul [Ring.HasFiniteQuotients R0] {L F : IntermediateField K (AlgebraicClosure K)}
    [FiniteDimensional K L] [IsGalois K L] (hFL : F ≤ L)
    [IsDedekindDomain (integralClosure R0 F)] [IsFractionRing (integralClosure R0 F) F]
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    (w : HeightOneSpectrum (integralClosure R0 L)) (vF : HeightOneSpectrum (integralClosure R0 F))
    (hvF : vF.asIdeal = w.asIdeal.comap (incl R0 K hFL)) (x : F) :
    WithZero.log (w.valuation L (IntermediateField.inclusion hFL x)) =
      (Nat.card ↥(w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hFL).fixingSubgroup) : ℤ) *
        WithZero.log (vF.valuation F x) := by
  classical
  have : FiniteDimensional K F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFL).toLinearMap
      (IntermediateField.inclusion hFL).injective
  have : Algebra.IsSeparable K F :=
    Algebra.IsSeparable.of_algHom (F := K) (E := F) (E' := L) (f := IntermediateField.inclusion hFL)
  have : Module.Finite R0 (integralClosure R0 L) := IsIntegralClosure.finite R0 K L (integralClosure R0 L)
  have : Module.Finite R0 (integralClosure R0 F) := IsIntegralClosure.finite R0 K F (integralClosure R0 F)
  have hGal : IsGaloisGroup (L ≃ₐ[K] L) R0 (integralClosure R0 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) R0 (integralClosure R0 L) K L
  letI : Algebra (integralClosure R0 F) (integralClosure R0 L) := (incl R0 K hFL).toRingHom.toAlgebra
  letI : SMul (integralClosure R0 F) (integralClosure R0 L) := Algebra.toSMul
  letI : Algebra F L := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : Algebra (integralClosure R0 F) L :=
    ((algebraMap F L).comp (algebraMap (integralClosure R0 F) F)).toAlgebra
  have : @IsScalarTower (integralClosure R0 F) F L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : @IsScalarTower (integralClosure R0 F) (integralClosure R0 L) L Algebra.toSMul Algebra.toSMul
      Algebra.toSMul := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R0 (integralClosure R0 F) (integralClosure R0 L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext (Subtype.ext rfl))
  have : Module.IsTorsionFree (integralClosure R0 F) (integralClosure R0 L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : integralClosure R0 L => ((z : L) : AlgebraicClosure K)) h))
  have : Module.Finite (integralClosure R0 F) (integralClosure R0 L) :=
    Module.Finite.of_restrictScalars_finite R0 _ _
  have : Module.Flat (integralClosure R0 F) (integralClosure R0 L) := inferInstance
  have : Ring.HasFiniteQuotients (integralClosure R0 F) := Ring.HasFiniteQuotients.of_module_finite R0 _
  have : Finite (integralClosure R0 F ⧸ vF.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient vF.ne_bot
  have : w.asIdeal.LiesOver vF.asIdeal := ⟨hvF.trans (Ideal.ext fun _ => Iff.rfl)⟩
  set H := (IntermediateField.restrict hFL).fixingSubgroup
  have hfixH : ∀ h : H, ∀ c : integralClosure R0 F,
      (h : L ≃ₐ[K] L) • algebraMap (integralClosure R0 F) (integralClosure R0 L) c =
        algebraMap (integralClosure R0 F) (integralClosure R0 L) c := by
    intro h c
    apply Subtype.ext
    show (h : L ≃ₐ[K] L) (IntermediateField.inclusion hFL (c : F)) = IntermediateField.inclusion hFL (c : F)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 _
      ((IntermediateField.mem_restrict hFL _).2 (c : F).2)
  have : IsGaloisGroup H (integralClosure R0 F) (integralClosure R0 L) := by
    refine ⟨⟨fun {h1 h2} heq => Subtype.ext (hGal.faithful.eq_of_smul_eq_smul fun b => heq b)⟩,
      ⟨fun h c b => ?_⟩, ⟨fun b hb => ?_⟩⟩
    · rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
      congr 1
      exact hfixH h c
    · have hbF : (b : L) ∈ IntermediateField.restrict hFL := by
        rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.restrict hFL),
          IntermediateField.mem_fixedField_iff]
        intro f hf
        exact congrArg (fun z : integralClosure R0 L => (z : L)) (hb ⟨f, hf⟩)
      rw [IntermediateField.mem_restrict] at hbF
      have hint : IsIntegral R0 (⟨((b : L) : AlgebraicClosure K), hbF⟩ : F) := by
        rw [← isIntegral_algHom_iff ((IntermediateField.inclusion hFL).restrictScalars R0)
          (IntermediateField.inclusion hFL).injective]
        exact b.2
      exact ⟨⟨⟨_, hbF⟩, hint⟩, Subtype.ext (Subtype.ext rfl)⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := H) vF.asIdeal w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx vF.asIdeal w.asIdeal H] at hcard
  have he' : vF.asIdeal.ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx (integralClosure R0 F) :=
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ vF.ne_bot
  have hval := HeightOneSpectrum.valuation_liesOver L vF w x
  have hc : Nat.card ↥(w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ H) = Nat.card ↥(w.asIdeal.inertia H) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ H ≤ H)).toEquiv, Subgroup.inf_subgroupOf_right]
    rfl
  rw [hc, hcard, ← he']
  change WithZero.log (w.valuation L (algebraMap F L x)) = _
  rw [← hval, WithZero.log_pow, nsmul_eq_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Ramification converse (R).** If `γ ^ N = a ∈ M` (finite level `M ≤ K_U`) and every element of `I(Q)` fixing `M`
fixes `γ`, then `N ∣ v(a)` at `v = Q ∩ B_M`. -/
theorem dvd_val_of_fix_lev [Ring.HasFiniteQuotients R0] {Q : Ideal (proChart A K R0)} [Q.IsPrime] {N : ℕ}
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K) [FiniteDimensional K M]
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    (v : HeightOneSpectrum (integralClosure R0 M)) (hv : v.asIdeal = Q.comap (inclU R0 hMU))
    {γ : maxUnram A K} {a : M} (hγ : γ ^ N = IntermediateField.inclusion hMU a)
    (hfix : ∀ σ ∈ Q.inertia (Pi1 A K), (∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → σ x = x) →
      σ γ = γ) :
    (N : ℤ) ∣ WithZero.log (v.valuation M a) := by
  classical
  by_cases ha0 : a = 0
  · simp [ha0]
  -- a finite Galois level `L ⊇ M(γ)` inside `K_U`
  obtain ⟨t, ht⟩ : M.FG := by
    have : Module.Finite K M.toSubalgebra.toSubmodule := inferInstanceAs (Module.Finite K M)
    exact IntermediateField.fg_of_fg_toSubalgebra M (Subalgebra.fg_of_fg_toSubmodule Submodule.FG.of_finite)
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K (insert (γ : AlgebraicClosure K) t) (by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact γ.2
    · exact hMU (by rw [← ht]; exact IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 hx)))
  have : FiniteDimensional K L := hL.1
  have : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  have hγL : (γ : AlgebraicClosure K) ∈ L :=
    hle (IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 (Finset.mem_insert_self _ _)))
  have hML : M ≤ L := by
    rw [← ht, IntermediateField.adjoin_le_iff]
    intro x hx
    exact hle (IntermediateField.subset_adjoin K _
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx))))
  have : IsFractionRing (integralClosure R0 L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K L
  have : IsDedekindDomain (integralClosure R0 L) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := L)
  have hcomp : ∀ y : integralClosure R0 M, inclU R0 hLU (incl R0 K hML y) = inclU R0 hMU y :=
    fun y => Subtype.ext (Subtype.ext rfl)
  obtain ⟨y0, hy0v, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  -- the prime `w = Q ∩ B_L`
  let w : HeightOneSpectrum (integralClosure R0 L) := ⟨Q.comap (inclU R0 hLU), Ideal.IsPrime.comap _, by
    refine (Submodule.ne_bot_iff _).2 ⟨incl R0 K hML y0, ?_, ?_⟩
    · rw [Ideal.mem_comap, hcomp, ← Ideal.mem_comap, ← hv]
      exact hy0v
    · intro h
      exact hy00 (Subtype.ext (Subtype.ext
        (congrArg (fun z : integralClosure R0 L => ((z : L) : AlgebraicClosure K)) h)))⟩
  have hvw : v.asIdeal = w.asIdeal.comap (incl R0 K hML) := by
    ext y
    show y ∈ v.asIdeal ↔ inclU R0 hLU (incl R0 K hML y) ∈ Q
    rw [hcomp, hv, Ideal.mem_comap]
  -- the fixed field `F` of `I_w ∩ Gal(L/M)`: it contains `M` and `γ`
  obtain ⟨F, hFL, hmemF⟩ : ∃ F : IntermediateField K (AlgebraicClosure K), ∃ _ : F ≤ L,
      ∀ y : L, (y : AlgebraicClosure K) ∈ F ↔
        ∀ τ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hML).fixingSubgroup, τ y = y := by
    refine ⟨(IntermediateField.fixedField (w.asIdeal.inertia (L ≃ₐ[K] L) ⊓
      (IntermediateField.restrict hML).fixingSubgroup)).map L.val, ?_, fun y => ?_⟩
    · intro x hx
      obtain ⟨y, -, rfl⟩ := (IntermediateField.mem_map _).1 hx
      exact y.2
    · rw [IntermediateField.mem_map]
      constructor
      · rintro ⟨x, hx, hxy⟩
        have hxy' : x = y := Subtype.ext hxy
        subst hxy'
        exact (IntermediateField.mem_fixedField_iff _ _).1 hx
      · intro h
        exact ⟨y, (IntermediateField.mem_fixedField_iff _ _).2 h, rfl⟩
  have hMF : M ≤ F := fun x hx => (hmemF ⟨x, hML hx⟩).2 fun τ hτ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 _
      ((IntermediateField.mem_restrict hML _).2 hx)
  have hγF : (γ : AlgebraicClosure K) ∈ F := by
    refine (hmemF ⟨γ, hγL⟩).2 fun τ hτ => ?_
    obtain ⟨g, hgI, hg⟩ := exists_inertia_lift (R0 := R0) hLU (Q := Q) (Subgroup.mem_inf.1 hτ).1
    have hgM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x := by
      intro x hx
      have h1 := hg ⟨x, hML hx⟩
      have h2 : τ ⟨x, hML hx⟩ = ⟨x, hML hx⟩ :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 _
          ((IntermediateField.mem_restrict hML _).2 hx)
      rw [h2] at h1
      exact h1
    have h4 : IntermediateField.inclusion hLU (τ ⟨γ, hγL⟩) = IntermediateField.inclusion hLU ⟨γ, hγL⟩ :=
      (hg ⟨γ, hγL⟩).symm.trans (hfix g hgI hgM)
    exact (IntermediateField.inclusion hLU).injective h4
  have hIeq : w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hML).fixingSubgroup =
      w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hFL).fixingSubgroup := by
    apply le_antisymm
    · intro τ hτ
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hτ).1,
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_⟩
      exact (hmemF y).1 ((IntermediateField.mem_restrict hFL _).1 hy) τ hτ
    · intro τ hτ
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hτ).1,
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_⟩
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 y
        ((IntermediateField.mem_restrict hFL _).2 (hMF ((IntermediateField.mem_restrict hML _).1 hy)))
  -- instances at `F` and the prime `vF = w ∩ B_F`
  have : FiniteDimensional K F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFL).toLinearMap
      (IntermediateField.inclusion hFL).injective
  have : Algebra.IsSeparable K F :=
    Algebra.IsSeparable.of_algHom (F := K) (E := F) (E' := L) (f := IntermediateField.inclusion hFL)
  have : IsFractionRing (integralClosure R0 F) F :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K F
  have : IsDedekindDomain (integralClosure R0 F) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := F)
  let vF : HeightOneSpectrum (integralClosure R0 F) := ⟨w.asIdeal.comap (incl R0 K hFL), Ideal.IsPrime.comap _, by
    refine (Submodule.ne_bot_iff _).2 ⟨incl R0 K hMF y0, ?_, ?_⟩
    · have h5 : incl R0 K hFL (incl R0 K hMF y0) = incl R0 K hML y0 := Subtype.ext (Subtype.ext rfl)
      rw [Ideal.mem_comap, h5, ← Ideal.mem_comap, ← hvw]
      exact hy0v
    · intro h
      exact hy00 (Subtype.ext (Subtype.ext
        (congrArg (fun z : integralClosure R0 F => ((z : F) : AlgebraicClosure K)) h)))⟩
  have hA := log_val_eq_card_mul (R0 := R0) hML w v hvw a
  have hB := log_val_eq_card_mul (R0 := R0) hFL w vF rfl ⟨γ, hγF⟩
  rw [← hIeq] at hB
  have hpow : IntermediateField.inclusion hML a = (IntermediateField.inclusion hFL ⟨γ, hγF⟩) ^ N := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    have h : ((γ ^ N : maxUnram A K) : AlgebraicClosure K) =
        ((IntermediateField.inclusion hMU a : maxUnram A K) : AlgebraicClosure K) := congrArg Subtype.val hγ
    rw [SubmonoidClass.coe_pow] at h
    exact h.symm
  rw [hpow, map_pow, WithZero.log_pow, nsmul_eq_mul, hB] at hA
  have he : (Nat.card ↥(w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hML).fixingSubgroup) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  refine ⟨WithZero.log (vF.valuation F ⟨γ, hγF⟩), ?_⟩
  apply mul_left_cancel₀ he
  linear_combination hA.symm

end

end TameInertia
end RamanujanPetersson

end


