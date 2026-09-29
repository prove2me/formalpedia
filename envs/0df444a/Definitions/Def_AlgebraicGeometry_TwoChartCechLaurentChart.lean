-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
-- name    : AlgebraicGeometry_TwoChartCechLaurentChart
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a58d39c7-d4ef-5728-9466-849a27fb3c42
-- title:
--   Laurent charts and residues on two-chart covers
-- statement:
--   The first part of the module develops the calculus of formal Laurent series $R((t)) =$ `LaurentSeries R` over a commutative ring $R$: the coefficient formula $[t^n]\,x' = (n+1)\,[t^{n+1}]x$ for Mathlib's `LaurentSeries.derivative`, its behaviour on $t^n\cdot x$ and on power series, the Leibniz rule `derivative_mul_def` (proved by writing each series as $t^{\mathrm{ord}}$ times its power-series part), and the residue [`LaurentSeries.residue`](../def/AlgebraicGeometry_TwoChartCechLaurentChart.html#L76), the $R$-linear map $x \mapsto [t^{-1}]x$. Its basic properties are recorded: the residue kills $R[[t]]$ and kills $P\,\mathrm{d}Q$ for power series $P,Q$, it sends $t^{-1}\,\mathrm{d}t$ to $1$, and it commutes with coefficientwise application of a ring homomorphism.
--
--   The main definition is [`TwoChartCech.Cover.LaurentChart`](../def/AlgebraicGeometry_TwoChartCechLaurentChart.html#L107): for a two-chart cover $\mathcal U = (A_0,A_1,A_{01};\rho_0,\rho_1)$ of $R$-algebras, a structure with a single datum `expand` $: A_{01} \to R((t))$, a ring homomorphism, subject to `expand_algebraMap`, that $\mathrm{expand}(r\cdot 1) = \mathrm{C}(r)$ for $r \in R$. Via `expand`, $R((t))$ becomes an $A_{01}$-module; differentiation composed with `expand` is an $R$-derivation $A_{01} \to R((t))$, whence an $A_{01}$-linear map `expandKaehler` $\colon \Omega_{A_{01}/R} \to R((t))$ with $f\,\mathrm{d}g \mapsto \widehat f\,\widehat g\,'$, and the chart's residue `LaurentChart.residue` $\colon \Omega_{A_{01}/R} \to R$ is its composition with $[t^{-1}]$. Two predicates on a chart relative to an $R$-algebra map $\rho \colon B \to A_{01}$ are defined: `IsRegular`, that $\mathrm{expand}(\rho b)$ lies in the image of $R[[t]]$ for every $b$, and `HasParameter`, that $\mathrm{expand}(\rho b) = t$ for some $b$. The structure `IsCompletionAlong` $\rho$ $e$, for an $R$-point $e \colon B \to R$, carries regularity together with two conditions as fields: every $n$-jet of a power series is realised by the expansion of some $\rho b$ in degrees $< n$, and the vanishing of the coefficients of $\mathrm{expand}(\rho b)$ in degrees $<n$ is equivalent to $b \in (\ker e)^n$. All of this is instantiated on the formal disc `formalDisc R` ($A_0 = A_{01} = R((t))$, $A_1 = R[[t]]$ with $\rho_0$ the identity and $\rho_1$ the inclusion, the $R$-algebra structures coming from constants), whose identity chart is shown to be regular along $\rho_1$, to have the parameter $t$, to give $\mathrm{Res}(t^{-1}\,\mathrm{d}t) = 1$, and to be a completion along $\rho_1$ together with the point $\mathrm{constantCoeff}$; a companion lemma identifies $\ker(\mathrm{constantCoeff})^n$ with the power series whose coefficients below degree $n$ vanish.
--
--   **Relation to Mathlib.** Mathlib supplies `LaurentSeries` (as Hahn series over $\mathbb Z$) with its `derivative`, `ofPowerSeries`, and the module of Kähler differentials $\Omega_{A/R}$; the residue map on Laurent series, the `LaurentChart` structure on a two-chart cover, the predicates `IsRegular`, `HasParameter` and `IsCompletionAlong`, and the formal disc as a cover are the project's own.
--
--   **Where it is used.** A two-chart cover models a curve covered by two affine opens, and a Laurent chart records the local expansion of functions on the overlap in a formal parameter; the resulting residue map on $\Omega_{A_{01}/R}$ is the ingredient used in the Čech-level treatment of differentials and duality for the curves occurring in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoChartCechLaurentChart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

namespace LaurentSeries

variable (R : Type*) [CommRing R]

theorem derivative_coeff (x : LaurentSeries R) (n : ℤ) :
    (derivative R x).coeff n = (n + 1) • x.coeff (n + 1) := by
  simp only [derivative_apply, hasseDeriv_coeff, Nat.cast_one, Ring.choose_one_right]

theorem derivative_single_one_mul (n : ℤ) (x : LaurentSeries R) :
    derivative R (HahnSeries.single n (1 : R) * x) =
      HahnSeries.single (n - 1) (n : R) * x + HahnSeries.single n (1 : R) * derivative R x := by
  ext m
  simp only [HahnSeries.coeff_add, derivative_coeff, HahnSeries.coeff_single_mul, one_mul, zsmul_eq_mul]
  rw [show m - (n - 1) = m - n + 1 by ring, show m + 1 - n = m - n + 1 by ring]
  push_cast
  ring

theorem coeff_ofPowerSeries_of_neg (p : PowerSeries R) {m : ℤ} (hm : m < 0) :
    (HahnSeries.ofPowerSeries ℤ R p).coeff m = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨k, hk⟩
  change (k : ℤ) = m at hk
  omega

theorem derivative_ofPowerSeries (p : PowerSeries R) :
    derivative R (HahnSeries.ofPowerSeries ℤ R p) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.derivative R p) := by
  ext m
  rw [derivative_coeff]
  rcases lt_trichotomy m (-1) with hm | rfl | hm
  · rw [coeff_ofPowerSeries_of_neg R _ (by omega), coeff_ofPowerSeries_of_neg R _ (by omega), smul_zero]
  · rw [neg_add_cancel, zero_smul, coeff_ofPowerSeries_of_neg R _ (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
    have : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_derivative, zsmul_eq_mul]
    push_cast
    ring

theorem derivative_mul_def (x y : LaurentSeries R) :
    derivative R (x * y) = x * derivative R y + derivative R x * y := by

  obtain ⟨a, P, rfl⟩ :
      ∃ (a : ℤ) (P : PowerSeries R), x = HahnSeries.single a (1 : R) * HahnSeries.ofPowerSeries ℤ R P :=
    ⟨x.order, x.powerSeriesPart, (single_order_mul_powerSeriesPart x).symm⟩
  obtain ⟨b, Q, rfl⟩ :
      ∃ (b : ℤ) (Q : PowerSeries R), y = HahnSeries.single b (1 : R) * HahnSeries.ofPowerSeries ℤ R Q :=
    ⟨y.order, y.powerSeriesPart, (single_order_mul_powerSeriesPart y).symm⟩
  have hab : HahnSeries.single (a + b) (1 : R) = HahnSeries.single a 1 * HahnSeries.single b 1 := by
    rw [HahnSeries.single_mul_single, one_mul]
  have h1 : HahnSeries.single (a + b - 1) (((a + b : ℤ)) : R) =
      HahnSeries.single (a - 1) (a : R) * HahnSeries.single b 1 +
        HahnSeries.single a 1 * HahnSeries.single (b - 1) (b : R) := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single, mul_one, one_mul,
      show a - 1 + b = a + b - 1 by ring, show a + (b - 1) = a + b - 1 by ring, ← HahnSeries.single_add,
      Int.cast_add]
  have hPQ : HahnSeries.single a (1 : R) * HahnSeries.ofPowerSeries ℤ R P *
        (HahnSeries.single b 1 * HahnSeries.ofPowerSeries ℤ R Q) =
      HahnSeries.single (a + b) 1 * HahnSeries.ofPowerSeries ℤ R (P * Q) := by
    rw [map_mul, hab]; ring
  rw [hPQ, derivative_single_one_mul, derivative_ofPowerSeries, (PowerSeries.derivative R).leibniz, smul_eq_mul,
    smul_eq_mul, map_add, map_mul, map_mul, map_mul, derivative_single_one_mul, derivative_single_one_mul,
    derivative_ofPowerSeries, derivative_ofPowerSeries, hab, h1]
  ring

def residue : LaurentSeries R →ₗ[R] R := HahnSeries.coeff.linearMap (-1)

@[simp] theorem residue_apply (x : LaurentSeries R) : residue R x = x.coeff (-1) := rfl

theorem residue_ofPowerSeries (p : PowerSeries R) : residue R (HahnSeries.ofPowerSeries ℤ R p) = 0 :=
  coeff_ofPowerSeries_of_neg R p (by norm_num)

theorem residue_ofPowerSeries_mul_derivative_ofPowerSeries (p q : PowerSeries R) :
    residue R (HahnSeries.ofPowerSeries ℤ R p * derivative R (HahnSeries.ofPowerSeries ℤ R q)) = 0 := by
  rw [derivative_ofPowerSeries, ← map_mul, residue_ofPowerSeries]

theorem residue_single_neg_one_mul_derivative_single_one :
    residue R (HahnSeries.single (-1) (1 : R) * derivative R (HahnSeries.single 1 (1 : R))) = 1 := by
  rw [residue_apply, HahnSeries.coeff_single_mul, one_mul, derivative_coeff, HahnSeries.coeff_single]
  norm_num

theorem map_derivative {S : Type*} [CommRing S] (τ : R →+* S) (x : LaurentSeries R) :
    (derivative R x).map τ = derivative S (x.map τ) := by
  ext n
  rw [HahnSeries.map_coeff, derivative_coeff, derivative_coeff, HahnSeries.map_coeff, map_zsmul]

theorem residue_map {S : Type*} [CommRing S] (τ : R →+* S) (x : LaurentSeries R) :
    residue S (x.map τ) = τ (residue R x) := by
  rw [residue_apply, residue_apply, HahnSeries.map_coeff]

end LaurentSeries

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R]

structure LaurentChart (𝒰 : Cover.{u, v} R) where

  expand : 𝒰.A01 →+* LaurentSeries R

  expand_algebraMap : ∀ r : R, expand (algebraMap R 𝒰.A01 r) = HahnSeries.C r

namespace LaurentChart

variable {𝒰 : Cover.{u, v} R} (Λ : 𝒰.LaurentChart)

abbrev expandModule : Module 𝒰.A01 (LaurentSeries R) := Module.compHom (LaurentSeries R) Λ.expand

theorem expand_smul (r : R) (a : 𝒰.A01) : Λ.expand (r • a) = r • Λ.expand a := by
  rw [Algebra.smul_def, map_mul, expand_algebraMap, HahnSeries.C_mul_eq_smul]

theorem isScalarTower_expandModule :
    letI := Λ.expandModule
    IsScalarTower R 𝒰.A01 (LaurentSeries R) :=
  letI := Λ.expandModule
  ⟨fun r a x => by
    change Λ.expand (r • a) * x = r • (Λ.expand a * x)
    rw [expand_smul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]⟩

def expandLinear : 𝒰.A01 →ₗ[R] LaurentSeries R where
  toFun := Λ.expand
  map_add' := map_add _
  map_smul' := Λ.expand_smul

@[simp] theorem expandLinear_apply (a : 𝒰.A01) : Λ.expandLinear a = Λ.expand a := rfl

def expandDerivation :
    letI := Λ.expandModule
    Derivation R 𝒰.A01 (LaurentSeries R) :=
  letI := Λ.expandModule
  Derivation.mk' (LaurentSeries.derivative R ∘ₗ Λ.expandLinear) fun f g => by
    change LaurentSeries.derivative R (Λ.expand (f * g)) =
      Λ.expand f * LaurentSeries.derivative R (Λ.expand g) + Λ.expand g * LaurentSeries.derivative R (Λ.expand f)
    rw [map_mul, LaurentSeries.derivative_mul_def, mul_comm (LaurentSeries.derivative R (Λ.expand f))]

theorem expandDerivation_apply (f : 𝒰.A01) :
    letI := Λ.expandModule
    Λ.expandDerivation f = LaurentSeries.derivative R (Λ.expand f) := rfl

def expandKaehler :
    letI := Λ.expandModule
    Ω[𝒰.A01⁄R] →ₗ[𝒰.A01] LaurentSeries R :=
  letI := Λ.expandModule
  haveI := Λ.isScalarTower_expandModule
  Λ.expandDerivation.liftKaehlerDifferential

theorem expandKaehler_smul_D (f g : 𝒰.A01) :
    letI := Λ.expandModule
    Λ.expandKaehler (f • KaehlerDifferential.D R 𝒰.A01 g) = Λ.expand f * LaurentSeries.derivative R (Λ.expand g) := by
  letI := Λ.expandModule
  haveI := Λ.isScalarTower_expandModule
  change Λ.expandDerivation.liftKaehlerDifferential (f • KaehlerDifferential.D R 𝒰.A01 g) = _
  rw [LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

theorem expandKaehler_D (g : 𝒰.A01) :
    letI := Λ.expandModule
    Λ.expandKaehler (KaehlerDifferential.D R 𝒰.A01 g) = LaurentSeries.derivative R (Λ.expand g) := by
  letI := Λ.expandModule
  haveI := Λ.isScalarTower_expandModule
  exact Λ.expandDerivation.liftKaehlerDifferential_comp_D g

def residue : Ω[𝒰.A01⁄R] →ₗ[R] R where
  toFun ω := letI := Λ.expandModule; LaurentSeries.residue R (Λ.expandKaehler ω)
  map_add' ω ω' := by
    letI := Λ.expandModule
    change LaurentSeries.residue R (Λ.expandKaehler (ω + ω')) = _
    rw [map_add, map_add]
  map_smul' r ω := by
    letI := Λ.expandModule
    haveI := Λ.isScalarTower_expandModule
    change LaurentSeries.residue R (Λ.expandKaehler (r • ω)) = r • LaurentSeries.residue R (Λ.expandKaehler ω)
    have h1 : Λ.expandKaehler (r • ω) = r • Λ.expandKaehler ω := by
      rw [← IsScalarTower.algebraMap_smul 𝒰.A01 r ω, LinearMap.map_smul]
      change Λ.expand (algebraMap R 𝒰.A01 r) * Λ.expandKaehler ω = _
      rw [expand_algebraMap, HahnSeries.C_mul_eq_smul]
    rw [h1, map_smul]

theorem residue_apply (ω : Ω[𝒰.A01⁄R]) :
    letI := Λ.expandModule
    Λ.residue ω = (Λ.expandKaehler ω).coeff (-1) := rfl

theorem residue_smul_D (f g : 𝒰.A01) :
    Λ.residue (f • KaehlerDifferential.D R 𝒰.A01 g) =
      (Λ.expand f * LaurentSeries.derivative R (Λ.expand g)).coeff (-1) := by
  rw [residue_apply, expandKaehler_smul_D]

theorem residue_D (g : 𝒰.A01) :
    Λ.residue (KaehlerDifferential.D R 𝒰.A01 g) = (LaurentSeries.derivative R (Λ.expand g)).coeff (-1) := by
  rw [residue_apply, expandKaehler_D]

def IsRegular {B : Type*} [CommRing B] [Algebra R B] (ρ : B →ₐ[R] 𝒰.A01) : Prop :=
  ∀ b : B, Λ.expand (ρ b) ∈ (HahnSeries.ofPowerSeries ℤ R).range

theorem IsRegular.exists_eq_ofPowerSeries {B : Type*} [CommRing B] [Algebra R B] {ρ : B →ₐ[R] 𝒰.A01}
    (h : Λ.IsRegular ρ) (b : B) : ∃ p : PowerSeries R, HahnSeries.ofPowerSeries ℤ R p = Λ.expand (ρ b) :=
  h b

def HasParameter {B : Type*} [CommRing B] [Algebra R B] (ρ : B →ₐ[R] 𝒰.A01) : Prop :=
  ∃ b : B, Λ.expand (ρ b) = HahnSeries.single 1 1

end LaurentChart

def formalDisc (R : Type u) [CommRing R] : Cover.{u, u} R :=
  letI : Algebra R (LaurentSeries R) := (HahnSeries.C : R →+* LaurentSeries R).toAlgebra
  letI : Algebra R (PowerSeries R) := inferInstance
  { A0 := LaurentSeries R
    A1 := PowerSeries R
    A01 := LaurentSeries R
    ρ0 := AlgHom.id R _
    ρ1 := { (HahnSeries.ofPowerSeries ℤ R) with
      commutes' := fun r => by
        change HahnSeries.ofPowerSeries ℤ R (algebraMap R (PowerSeries R) r) = HahnSeries.C r
        rw [PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C] } }

def formalDiscChart (R : Type u) [CommRing R] : (formalDisc R).LaurentChart where
  expand := RingHom.id _
  expand_algebraMap _ := rfl

theorem formalDiscChart_isRegular (R : Type u) [CommRing R] : (formalDiscChart R).IsRegular (formalDisc R).ρ1 :=
  fun a => ⟨a, rfl⟩

theorem formalDiscChart_hasParameter (R : Type u) [CommRing R] :
    (formalDiscChart R).HasParameter (formalDisc R).ρ1 :=
  ⟨PowerSeries.X, by
    change HahnSeries.ofPowerSeries ℤ R PowerSeries.X = HahnSeries.single 1 1
    exact HahnSeries.ofPowerSeries_X⟩

theorem formalDiscChart_residue_tinv_dt (R : Type u) [CommRing R] (f g : (formalDisc R).A01)
    (hf : f = HahnSeries.single (-1) (1 : R)) (hg : g = HahnSeries.single 1 (1 : R)) :
    (formalDiscChart R).residue (f • KaehlerDifferential.D R (formalDisc R).A01 g) = 1 := by
  rw [LaurentChart.residue_smul_D]
  subst hf hg
  exact LaurentSeries.residue_single_neg_one_mul_derivative_single_one R

end TwoChartCech.Cover

namespace TwoChartCech.Cover.LaurentChart

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R}

structure IsCompletionAlong (Λ : 𝒰.LaurentChart) {B : Type*} [CommRing B] [Algebra R B]
    (ρ : B →ₐ[R] 𝒰.A01) (e : B →ₐ[R] R) : Prop where

  isRegular : Λ.IsRegular ρ

  exists_coeff_eq : ∀ (n : ℕ) (p : PowerSeries R), ∃ b : B,
    ∀ k : ℕ, k < n → (Λ.expand (ρ b)).coeff (k : ℤ) = PowerSeries.coeff k p

  forall_coeff_eq_zero_iff : ∀ (n : ℕ) (b : B),
    (∀ k : ℕ, k < n → (Λ.expand (ρ b)).coeff (k : ℤ) = 0) ↔ b ∈ RingHom.ker e.toRingHom ^ n

end TwoChartCech.Cover.LaurentChart

theorem PowerSeries.forall_coeff_eq_zero_iff_mem_ker_constantCoeff_pow (R : Type*) [CommRing R] (n : ℕ)
    (a : PowerSeries R) :
    (∀ k : ℕ, k < n → PowerSeries.coeff k a = 0) ↔ a ∈ RingHom.ker (PowerSeries.constantCoeff (R := R)) ^ n := by
  have hker : RingHom.ker (PowerSeries.constantCoeff (R := R)) = Ideal.span {PowerSeries.X} := by
    ext φ
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
  rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]

namespace TwoChartCech.Cover

def formalDiscPoint (R : Type u) [CommRing R] : (formalDisc R).A1 →ₐ[R] R :=
  { (PowerSeries.constantCoeff : PowerSeries R →+* R) with
    commutes' := fun r => by
      change PowerSeries.constantCoeff (algebraMap R (PowerSeries R) r) = r
      rw [PowerSeries.algebraMap_eq]
      exact PowerSeries.constantCoeff_C r }

theorem formalDiscChart_isCompletionAlong (R : Type u) [CommRing R] :
    (formalDiscChart R).IsCompletionAlong (formalDisc R).ρ1 (formalDiscPoint R) where
  isRegular := formalDiscChart_isRegular R
  exists_coeff_eq n p := ⟨p, fun k _ => HahnSeries.ofPowerSeries_apply_coeff p k⟩
  forall_coeff_eq_zero_iff n a := by
    refine Iff.trans ?_ (PowerSeries.forall_coeff_eq_zero_iff_mem_ker_constantCoeff_pow R n a)
    simp only [show ∀ b, (formalDiscChart R).expand ((formalDisc R).ρ1 b) = HahnSeries.ofPowerSeries ℤ R b from
      fun _ => rfl, HahnSeries.ofPowerSeries_apply_coeff]

end TwoChartCech.Cover

end


