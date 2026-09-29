-- Prove2me | Definitions.Def_ModularCurve_MultCoveringFamily
-- name    : ModularCurve_MultCoveringFamily
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/f4305b0c-b420-567a-b16e-5aefa6897245
-- title:
--   Good family data and contexts for the multiplicative covering
-- statement:
--   Throughout, $p$ is a prime and the ambient field is $\overline{\mathbb Q}$-coefficient Laurent series, with $\mathrm{modularFunctionFieldBar}(1\cdot p)$ the geometric modular function field of level $1\cdot p$. A `FamData p r` records $r$ elements $t_0,\dots,t_{r-1}$ of that field, together with elements $t^{\mathbb Q}_l$ of the full modular function field over $\mathbb Q$ and the requirement that each $t_l$ is exactly the coefficientwise image of $t^{\mathbb Q}_l$; thus the family is rational. For such data, `zeroSeries` is the rational Laurent series underlying the Fricke transform $w_p t^{\mathbb Q}_l$, and `coe_frickeInvolutionBar_t` states that the geometric Fricke involution of $t_l$ has precisely that series as its coefficient image. `hasseContent` is the integer $n$ realised as the minimum of $v_p$ on the nonzero coefficients of `zeroSeries` (chosen from the statement that such a minimum exists and is attained, and set to $0$ otherwise), `hasseExp` its nonnegative part $n^+$, and `goodFamilyZero` the rescaled member $p^{-n^+}t_l$. For a valuation subring $A$ of $\overline{\mathbb Q}$ with residue field of characteristic $p$ and a chart context $\Gamma$, `ssPolyBar` and `ssPolyBarZero` are the products $\prod_e(\tilde\jmath-a_e)$ and $\prod_e(\tilde\jmath-a_e^{\,p})$ over $e$ in `Fin (mAnnuli p)`, where $a_e=\mathrm{ssValue}\,\Gamma\,e$ enumerates the supersingular $j$-values.
--
--   `FamCtx p r` extends `FamData p r` by four properties, carried as structure fields: $t$ satisfies `IsEmbBasis (1*p)`; $t_l=1$ for index $l=0$; for every $A$ lying over $p$ and every chart context $\Gamma$ over $A$, all $t_l$ are integral on the $\infty$-chart, $t_0$ reduces to $1$, and there are polynomials $P_l$ over the residue field with $\deg P_l+1\le \mathrm{mAnnuli}\,p$ and reduction of $t_l$ equal to $\mathrm{ssPolyBar}\,\Gamma\cdot P_l(\tilde\jmath)$ for $l\ge 1$, the $P_l$ ($l\ge1$) being linearly independent with span the polynomials of degree $<\mathrm{mAnnuli}\,p$; and, under the hypothesis that every $a_e$ differs from $0$ and $1728$, all $p^{-n^+}t_l$ are integral on the zero chart, with polynomials $P_l$ of degree $\le \mathrm{mAnnuli}\,p$, linearly independent and spanning every polynomial of degree $\le\mathrm{mAnnuli}\,p$, satisfying $\overline{p^{-n^+}t_l}\cdot\mathrm{ssPolyBarZero}\,\Gamma=P_l(\tilde\jmath)$ and $P_l=\prod_e(X-a_e^{\,p})$ for $l=0$. The abbreviation `goodFamily` returns the underlying family $t$ of such a context.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient ingredients used here ($p$-adic valuation on rationals, Laurent series, valuation subrings and residue fields, `Polynomial.degreeLT` and `Submodule.span`); the modular function fields, the Fricke involution, the component charts and annuli, the supersingular $j$-set and the family notions `FamData`/`FamCtx` are the project's own.
--
--   **Where it is used.** The family context packages the integral structure, at both cusps and at every valuation ring above $p$, of a rational basis of a space of modular functions on $X_0(p)$; it is the input from which the multiplicative covering of $X_0(p)$ by charts and annuli over such valuation rings is assembled, and hence feeds the proximity and height estimates used on the modular-curve side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_MultCoveringFamily.lean

import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

namespace ModularCurve.MultCovering

structure FamData (p : ℕ) [Fact p.Prime] (r : ℕ) where

  t : Fin r → ↥(modularFunctionFieldBar (1 * p))

  tRat : Fin r → ↥(modularFunctionFieldFull (1 * p))
  t_eq : ∀ l, t l = ⟨coeffEmb (AlgebraicClosure ℚ) ↑(tRat l),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (tRat l).2⟩

noncomputable def zeroSeries {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) : LaurentSeries ℚ :=
  ((frickeInvolutionFull (1 * p) (Φ.tRat l) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ)

theorem coe_frickeInvolutionBar_t {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) :
    ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (zeroSeries Φ l) := by
  rw [Φ.t_eq l, frickeInvolutionBar_def, coe_geomAut_coeffEmb]
  rfl

open Classical in

noncomputable def hasseContent {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) : ℤ :=
  if h : ∃ n : ℤ, (∀ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 → n ≤ padicValRat p ((zeroSeries Φ l).coeff k)) ∧
      (∃ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 ∧ padicValRat p ((zeroSeries Φ l).coeff k) = n)
  then h.choose else 0

noncomputable def hasseExp {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) : ℕ :=
  (hasseContent Φ l).toNat

noncomputable def goodFamilyZero {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) :
    modularFunctionFieldBar (1 * p) :=
  (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l))⁻¹ * Φ.t l

section PerA
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

def ssPolyBar : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  ∏ e : Fin (mAnnuli p), (jBar (IsLocalRing.ResidueField ↥A)
    - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e))

def ssPolyBarZero : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  ∏ e : Fin (mAnnuli p), (jBar (IsLocalRing.ResidueField ↥A)
    - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e ^ p))

end PerA

structure FamCtx (p : ℕ) [Fact p.Prime] (r : ℕ) extends FamData p r where

  t_basis : IsEmbBasis (1 * p) t

  t_zero : ∀ l : Fin r, (l : ℕ) = 0 → t l = 1

  t_inf : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
      ∃ hint : ∀ l, t l ∈ (infChart Γ).integers,
        (∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨t l, hint l⟩ = 1) ∧
        ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
          (∀ l : Fin r, 1 ≤ (l : ℕ) →
            (P l).natDegree + 1 ≤ mAnnuli p ∧
            (infChart Γ).residue ⟨t l, hint l⟩
              = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
          LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
          Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
            = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p)

  t_zeroChart : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
      (∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) →
      ∃ (hint : ∀ l, goodFamilyZero toFamData l ∈ (zeroChart Γ).integers)
        (P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)),
        (∀ l, (P l).natDegree ≤ mAnnuli p) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) P ∧
        (∀ Q : Polynomial (IsLocalRing.ResidueField ↥A), Q.natDegree ≤ mAnnuli p →
          Q ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P)) ∧
        (∀ l : Fin r, (l : ℕ) = 0 →
          P l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
        ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero toFamData l, hint l⟩ * ssPolyBarZero Γ
          = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)

abbrev goodFamily {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r) : Fin r → ↥(modularFunctionFieldBar (1 * p)) :=
  Φ.t

end ModularCurve.MultCovering

end


