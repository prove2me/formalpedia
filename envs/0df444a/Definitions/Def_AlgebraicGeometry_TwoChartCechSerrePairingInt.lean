-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
-- name    : AlgebraicGeometry_TwoChartCechSerrePairingInt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/53b452e1-6bf9-59a0-80ab-1b4105740649
-- title:
--   Residue sums, Kähler trace and integral Serre pairing
-- statement:
--   Fix a commutative ring $R$, a two-chart cover $\mathcal U$ of $R$ (algebras $A_0,A_1,A_{01}$ with $R$-algebra maps $\rho_0\colon A_0\to A_{01}$, $\rho_1\colon A_1\to A_{01}$), and a finite family $\Lambda\colon\iota\to\mathcal U.\mathrm{LaurentChart}$, each member being a ring homomorphism $A_{01}\to R(\!(t)\!)$ compatible with the structure map and carrying its residue functional $\Omega_{A_{01}/R}\to R$, the coefficient of $t^{-1}$ of the induced expansion of a differential. `residueSum` is the $R$-linear functional $\sum_{i}\mathrm{Res}_{\Lambda_i}$ on $\Omega_{A_{01}/R}$. The predicate `ResiduesVanishOnCoboundaries` asserts that the range of the Čech differential $(\omega_0,\omega_1)\mapsto r_1\omega_1-r_0\omega_0$ of the Kähler sections data (restriction of differentials along $\rho_0$, $\rho_1$) is contained in the kernel of this functional; `residuesVanishOnCoboundaries_iff` splits this into the two conditions that the residue sum annihilate $r_0\omega$ for every $\omega\in\Omega_{A_0/R}$ and $r_1\omega$ for every $\omega\in\Omega_{A_1/R}$.
--
--   Given such a $\Lambda$ and a proof $hv$ of that containment, `kaehlerTrace` is the resulting functional on $H^1$ of the Kähler sections data, i.e. on $\Omega_{A_{01}/R}$ modulo Čech coboundaries, sending the class of $\eta$ to $\sum_i\mathrm{Res}_{\Lambda_i}\eta$. `serrePairingInt` is the $R$-bilinear pairing obtained from the cup product followed by this trace:
--   $$H^0(\mathcal U,\Omega^1)\otimes H^1(\mathcal U,\mathcal O)\to R,$$
--   where $H^0$ is the submodule of pairs $(\omega_0,\omega_1)$ with $r_0\omega_0=r_1\omega_1$ and $H^1(\mathcal U,\mathcal O)$ is $A_{01}$ modulo the elements $\rho_1 s_1-\rho_0 s_0$. On representatives it is $\langle\omega,[f]\rangle=\sum_i\mathrm{Res}_{\Lambda_i}(f\cdot r_0\omega_0)$, equally $\sum_i\mathrm{Res}_{\Lambda_i}(f\cdot r_1\omega_1)$; the last theorem records that it is by definition the trace of the cup product.
--
--   **Relation to Mathlib.** Mathlib supplies the Kähler differential module $\Omega_{A/R}$ and Laurent series; the two-chart Čech package (covers, sections data, $H^0$, $H^1$, cup product), the Laurent charts with their residue functionals and the pairing defined here are the project's own.
--
--   **Where it is used.** These definitions provide an $R$-valued Serre duality pairing between $H^0$ of the differentials and $H^1$ of the structure sheaf for a curve over $R$ presented by two affine charts, with the trace computed as a sum of formal residues. They feed the two-chart Čech computations of relative Picard and Néron model data used in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoChartCechSerrePairingInt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechCupProduct
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v w

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) {ι : Type w} [Fintype ι]

def residueSum (Λ : ι → 𝒰.LaurentChart) : Ω[𝒰.A01⁄R] →ₗ[R] R := ∑ i, (Λ i).residue

theorem residueSum_apply (Λ : ι → 𝒰.LaurentChart) (η : Ω[𝒰.A01⁄R]) :
    𝒰.residueSum Λ η = ∑ i, (Λ i).residue η := by
  rw [residueSum, LinearMap.sum_apply]

def ResiduesVanishOnCoboundaries (Λ : ι → 𝒰.LaurentChart) : Prop :=
  LinearMap.range 𝒰.kaehler.cechDiff ≤ LinearMap.ker (𝒰.residueSum Λ)

theorem residuesVanishOnCoboundaries_iff (Λ : ι → 𝒰.LaurentChart) :
    𝒰.ResiduesVanishOnCoboundaries Λ ↔
      (∀ ω : Ω[𝒰.A0⁄R], 𝒰.residueSum Λ (𝒰.kaehler.r0 ω) = 0) ∧
        ∀ ω : Ω[𝒰.A1⁄R], 𝒰.residueSum Λ (𝒰.kaehler.r1 ω) = 0 := by
  constructor
  · intro h
    refine ⟨fun ω => ?_, fun ω => ?_⟩
    · have hmem := h (LinearMap.mem_range_self 𝒰.kaehler.cechDiff ((ω, 0) : _ × _))
      rwa [LinearMap.mem_ker, Sections.cechDiff_apply, map_zero, zero_sub, map_neg, neg_eq_zero] at hmem
    · have hmem := h (LinearMap.mem_range_self 𝒰.kaehler.cechDiff ((0, ω) : _ × _))
      rwa [LinearMap.mem_ker, Sections.cechDiff_apply, map_zero, sub_zero] at hmem
  · rintro ⟨h0, h1⟩ _ ⟨s, rfl⟩
    rw [LinearMap.mem_ker, Sections.cechDiff_apply, map_sub, h0, h1, sub_zero]

def kaehlerTrace (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) : 𝒰.kaehler.H1 →ₗ[R] R :=
  𝒰.kaehler.traceForm (𝒰.residueSum Λ) hv

@[simp] theorem kaehlerTrace_mk (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (η : Ω[𝒰.A01⁄R]) :
    𝒰.kaehlerTrace Λ hv (Submodule.Quotient.mk η) = ∑ i, (Λ i).residue η := by
  rw [kaehlerTrace, Sections.traceForm_mk, residueSum_apply]

def serrePairingInt (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) :
    𝒰.kaehler.H0 →ₗ[R] 𝒰.structureSheaf.H1 →ₗ[R] R :=
  𝒰.kaehler.tracePairing (𝒰.residueSum Λ) hv

theorem serrePairingInt_apply_mk (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ω : 𝒰.kaehler.H0) (f : 𝒰.A01) :
    𝒰.serrePairingInt Λ hv ω (Submodule.Quotient.mk f) = ∑ i, (Λ i).residue (f • 𝒰.kaehler.r0 ω.val.1) := by
  rw [serrePairingInt, Sections.tracePairing_apply_mk, residueSum_apply]

theorem serrePairingInt_apply_mk' (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ω : 𝒰.kaehler.H0) (f : 𝒰.A01) :
    𝒰.serrePairingInt Λ hv ω (Submodule.Quotient.mk f) = ∑ i, (Λ i).residue (f • 𝒰.kaehler.r1 ω.val.2) := by
  rw [serrePairingInt_apply_mk, (𝒰.kaehler.mem_H0_iff _).mp ω.2]

theorem serrePairingInt_eq_kaehlerTrace_cupProduct (Λ : ι → 𝒰.LaurentChart)
    (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) (ω : 𝒰.kaehler.H0) (x : 𝒰.structureSheaf.H1) :
    𝒰.serrePairingInt Λ hv ω x = 𝒰.kaehlerTrace Λ hv (𝒰.kaehler.cupProduct ω x) := rfl

end TwoChartCech.Cover

end


