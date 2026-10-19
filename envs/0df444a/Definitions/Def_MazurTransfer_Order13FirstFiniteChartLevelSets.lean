-- Prove2me | Definitions.Def_MazurTransfer_Order13FirstFiniteChartLevelSets
-- name    : MazurTransfer_Order13FirstFiniteChartLevelSets
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:06:05.959445+00:00
-- url     : https://prove2.me/theorems/385c5fd8-7983-4194-92f3-95dda61c5872
-- title:
--   Finite free level sets of the actual first-chart parameter
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $U$ be the actual first finite chart of the order-thirteen curve and $f$ its specified parameter section. The map $R[T]\to\Gamma(U)$, $T\mapsto f$, is finite. For every nontrivial commutative $R$-algebra $S$ and $s\in S$, the evaluated quotient $Q=(S\otimes_R\Gamma(U))/(1\otimes f-s\otimes1)$ has the specified $S$-basis of three elements. Thus $Q$ is finite free of rank three. The constructor is the base change of the actual polynomial basis transported through the original FLT tensor equivalence.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Three structural declarations following Order13SingleSectionComplementLevelSets.lean. Reuses the original official Anthropic FLT levelSetEquiv at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2 through its public Definitions interface. The original structural R-action and literal fresh first-chart parameter are retained. Native, strict and full frontend checks pass with standard axioms only; all three declaration types are closed. Named downstream consumers: finite_f and levelSet_free in unchanged integral order-thirteen FiniteMapData.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Retains the official Anthropic FLT levelSetEquiv construction at pin 6e837e75355538c7f80bab5b956861e86c4eacc2 through its public constructor interface.
Design boundary: finite free evaluated level sets of the actual first chart with the structural R-action and literal chosen parameter section.
Named downstream consumer: levelSet_free and finite_f in the unchanged integral order-thirteen FiniteMapData existence contract. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartPolynomialBasis
import Definitions.Def_MazurTransfer_OfficialFLTPolynomialLevelSetEquiv
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial Module
open scoped TensorProduct
open MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13FirstFiniteChartFromPublicTheorem
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem parameter_finite (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
    (aeval (parameterSection R h104) : Polynomial R →ₐ[R]
      Γ(curveScheme R, chartOpen R)).toRingHom.Finite := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, chartOpen R) :=
    (aeval (parameterSection R h104)).toRingHom.toAlgebra
  exact Module.Finite.of_basis (polynomialBasis R h104)

variable (S : Type u) [CommRing S] [Algebra R S]

def levelSetBasis (h104 : IsUnit (104 : R)) (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
    Basis (Fin 3) S (S ⊗[R] Γ(curveScheme R, chartOpen R) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] parameterSection R h104 -
        s ⊗ₜ[R] (1 : Γ(curveScheme R, chartOpen R))}) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, chartOpen R) :=
    (aeval (parameterSection R h104)).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) Γ(curveScheme R, chartOpen R) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R Γ(curveScheme R, chartOpen R) r =
        aeval (parameterSection R h104) (C r)
      rw [aeval_C]
  letI : Algebra (Polynomial R) S := (aeval s).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = aeval s (C r)
    rw [aeval_C]
  let e := P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.levelSetEquiv
    R Γ(curveScheme R, chartOpen R) S (parameterSection R h104) s
      (by change aeval (parameterSection R h104) X = _; exact aeval_X _)
      (by change aeval s X = s; exact aeval_X s)
  exact ((polynomialBasis R h104).baseChange S).map e.symm.toLinearEquiv

theorem levelSet_finite_free_finrank (h104 : IsUnit (104 : R)) [Nontrivial S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
    let Q := S ⊗[R] Γ(curveScheme R, chartOpen R) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] parameterSection R h104 -
        s ⊗ₜ[R] (1 : Γ(curveScheme R, chartOpen R))}
    Module.Finite S Q ∧ Module.Free S Q ∧ Module.finrank S Q = 3 := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
  let b := levelSetBasis R S h104 s
  exact ⟨Module.Finite.of_basis b, Module.Free.of_basis b, by
    simpa using Module.finrank_eq_card_basis b⟩

end MazurTransfer.Order13FirstFiniteChartFromPublicTheorem
#print axioms MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.parameter_finite
#print axioms MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.levelSetBasis
#print axioms MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.levelSet_finite_free_finrank


