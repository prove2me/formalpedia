-- Prove2me | Definitions.Def_ModularCurve_PernodeHyps
-- name    : ModularCurve_PernodeHyps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/fcd59016-b6fe-5547-ad45-3a132d82e56c
-- title:
--   Per-node hypothesis frame for descent of semistable charts
-- statement:
--   This module defines a single Prop-valued structure, [`ModularCurve.FullLevel.PernodeHyps`](../def/ModularCurve_PernodeHyps.html#L29), which bundles the hypotheses needed to descend one end of an integral chart from a large modular function field to a subfield. Its parameters are: a prime $q$, a level $M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ with a finite set $W$ of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)(M')$ and a distinguished $s \in W$, a `ConstantReduction` $R_0$ reducing $\mathrm{modularFunctionFieldBar}\,M'$ to that residue function field; a subfield $k_0 \subseteq \overline{\mathbb Q}$ with an element $\pi_0$ lying in $A$, a prime $\ell'$, $\xi \in k_0$, a subfield $K_\ell$ of $\mathrm{LaurentSeries}\,k_0$ over $k_0$ with a nonzero $j_\ell \in K_\ell$, an ideal $y$ of `chartAlgFin` over $A_0 := A \cap k_0$, valuation subrings $W_t \subseteq K_\ell$, a natural number $n$, an automorphism $\tau_0 \in \mathrm{Aut}_{k_0}(K_\ell)$ with a finite group $G$ of such automorphisms, an exponent $m$, a finite set `ends` of subrings of $K_\ell$, a subfield $K_0 \subseteq K_\ell$ with a finite set `nodes` of subrings of it, and finally an end $\tilde{\mathcal O} \in K_\ell$ and a subring $\mathcal O \subseteq K_0$; further data ($\ell$, $\zeta_0$, $\varpi_t$, $K_b$, $A_b$, $\varpi_b$, $\varpi_t'$, $B_t$, $\gamma_0$, $\zeta_c$, $a_0$, $B_0$, $W_0'$) are carried in the signature as part of the frame.
--
--   The fields assert: $\tilde{\mathcal O}$ is one of the `ends` and $\mathcal O = \tilde{\mathcal O} \cap K_0$ (`hÕ`, `hO`); $G$ is finite, contains $\tau_0$, each of its elements realises the slash action of some $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ in the sense of `IsLevelAutAt` at level $(q\ell')^2M'$ with the character group `levelH`, $\tau_0^n$ acts trivially, and the stabiliser of $\tilde{\mathcal O}$ in $G$ consists of powers of $\tau_0$ (`hGfin`–`hHcyc`); invariant-theoretic finiteness: for a $G$-stable finite-type $A_0$-subalgebra $B_x$ of $K_\ell$ and its subring of $G$-invariants, the latter is Noetherian, $B_x$ is module-finite over it, and $B_x \cap K_0$ is generated over the image of $A \cap k_0$ by a finite set (`hInvFin`); the adic completion of $A_0$ at its maximal ideal is a complete discrete valuation domain with uniformiser the image of $\pi_0$, $n$ is a unit in it, and the crossing model $UV - \hat\pi_0^m$ over it is local and adically complete (`hAdom`–`hmodelcompl`); two clauses producing $G$-invariant separating functions, one inside the chart algebra distinguishing a discrete valuation ring $W_x$ dominating $\tilde{\mathcal O}$ from $W_t$, one inside $\tilde{\mathcal O}$ (`hsplit₁`, `hsplit₂`); for such $W_x$ adapted to $A_0$ and residually transcendental along $\mathrm{jqNModC}\,k_0\,(q\ell')$, existence of a residually transcendental element of $W_x \cap K_0$ (`hN3wit`) and the reduction laws for $\mathrm{qExpand}$ of integral level-$M'$ modular functions regular where $j$ is: the descended function lies in $K_0$ and in $W_x \cap K_0$, lies in the maximal ideal exactly when its $R_0$-reduction vanishes, and when that reduction is finite at $s$ it lies in $\mathcal O$ and is congruent there to the constant given by evaluating the reduction at $s$ (`hN3laws`); a fraction-field clause for $K_0$ relative to a $G$-stable subalgebra presenting $\tilde{\mathcal O}$ as a localisation (`hN4frac`); $G$-invariance of $\mathrm{jqNModC}\,k_0\,(q\ell')$ (`hjfix`); descent of an invariant element with prescribed poles to $K_0$ (`hN5`); and, assuming separation of the other ends and of their level translates from $W_x$, separation of every other node from $W_x \cap K_0$ by a function of that node (`hIGSEP`).
--
--   **Relation to Mathlib.** The frame is stated in terms of Mathlib notions (valuation subrings, adic completions, discrete valuation rings, Noetherian rings and module-finiteness, intermediate fields of Laurent series) together with project-specific ones (`ConstantReduction`, `UVCrossingModel`, `chartAlgFin`, `IsLevelAutAt`, the modular function fields of the project); Mathlib has no counterpart of such a hypothesis bundle.
--
--   **Where it is used.** The structure packages, as one named predicate, the input hypotheses of the per-node step in the construction of a semistable model of the modular curve of level divisible by $q$: it is the data required to descend one end of a chart over a big Laurent-series field to a subfield, matching the Igusa components and the supersingular nodes of a `SemistableCovering`. Such models underlie the analysis of the component group and of the Galois action on the Jacobian used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_PernodeHyps.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AdicCompletionLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 12800000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

structure ModularCurve.FullLevel.PernodeHyps
    (q : ℕ)
    [Fact q.Prime]
    (M' : ℕ)
    [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (π₀ : ↥k₀)
    (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (ℓ : ℕ)
    (ζ₀ : ↥k₀)
    (ϖt : ↥k₀)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (Ab : ValuationSubring ↥Kb)
    (ϖb : ↥Ab)
    (ℓ' : ℕ)
    [Fact ℓ'.Prime]
    (ξ : ↥k₀)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ)
    [Fact (jℓ ≠ 0)]
    (ϖt' : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ))
    (Bt : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (Wt : ValuationSubring ↥Kℓ)
    (n : ℕ)
    (γ₀ : SL(2, ℤ))
    (τ₀ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (m : ℕ)
    (ζc : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (B₀ : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (W₀' : ValuationSubring ↥K₀)
    (nodes : Finset (Subring ↥K₀))
    (Õ : Subring ↥Kℓ) (O : Subring ↥K₀) : Prop where
  hÕ : Õ ∈ ends
  hO : ∀ f : ↥K₀, f ∈ O ↔ (f : ↥Kℓ) ∈ Õ
  hGfin : Finite ↥G
  hτ₀G : τ₀ ∈ G
  hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
        ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ
  hτ₀n : ∀ f : ↥Kℓ, (τ₀ ^ n) f = f
  hHcyc : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → (∀ f : ↥Kℓ, f ∈ Õ ↔ σ f ∈ Õ) → ∃ j : ℕ, ∀ f : ↥Kℓ, σ f = (τ₀ ^ j) f
  hInvFin : ∀ (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ) (BG : Subring ↥Kℓ), Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bx →
        (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx) →
        (∀ f : ↥Kℓ, f ∈ BG ↔ f ∈ Bx ∧ ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f) →
        IsNoetherianRing ↥BG ∧ (∀ (hle : BG ≤ Bx.toSubring), letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥BG ↥Bx.toSubring) ∧
        (∃ T : Finset ↥K₀, Bx.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) = Subring.closure
          ({f : ↥K₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥K₀ x} ∪ (↑T : Set ↥K₀)))
  hAdom : IsDomain (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
  hAdvr : IsDiscreteValuationRing (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
  hAcompl : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
  hπhat : maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = Ideal.span {(algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩)}
  hnunit : IsUnit ((n : ℕ) : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
  hmodelloc : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))
  hmodelcompl : IsAdicComplete (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))
  hsplit₁ : ∀ Wx : ValuationSubring ↥Kℓ, (∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) → IsDiscreteValuationRing ↥Wx →
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) →
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) →
        (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
        ∃ f : ↥Kℓ, f ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ∧ (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f) ∧
          (∀ hfW : f ∈ Wt, (⟨f, hfW⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧ (∀ hfX : f ∈ Wx, (⟨f, hfX⟩ : ↥Wx) ∉ maximalIdeal ↥Wx)
  hsplit₂ : ∀ (c : ↥Kℓ) (hcO : c ∈ Õ), ¬ IsUnit (⟨c, hcO⟩ : ↥Õ) → (∀ hcW : c ∈ Wt, (⟨c, hcW⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) →
        ∃ (f : ↥Kℓ) (hfO : f ∈ Õ), (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f) ∧ ¬ IsUnit (⟨f, hfO⟩ : ↥Õ) ∧
          (∀ hfW : f ∈ Wt, (⟨f, hfW⟩ : ↥Wt) ∉ maximalIdeal ↥Wt)
  hN3wit : ∀ Wx : ValuationSubring ↥Kℓ, (∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) → IsDiscreteValuationRing ↥Wx →
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) →
        (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) →
        (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
        (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
          (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
          ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →
        ∃ t : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)), ∀ p : Polynomial ↥k₀, (∀ i, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
          (∃ hm : Polynomial.aeval (t : ↥K₀) p ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hm⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) →
            ∀ i, ∃ hc : algebraMap ↥k₀ ↥K₀ (p.coeff i) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hc⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))
  hN3laws : ∀ Wx : ValuationSubring ↥Kℓ, (∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) →
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) →
        (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) →
        (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
        (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
          (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
          ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →
        ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
          (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
              ↥(modularFunctionFieldBar M'))) →
          ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
            (⟨_, hF⟩ : ↥K₀) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ) ∧
            (∀ hW : (⟨_, hF⟩ : ↥K₀) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hW⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)) ↔
              (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
            ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              (⟨_, hF⟩ : ↥K₀) ∈ O ∧
              ∀ (hO' : (⟨_, hF⟩ : ↥K₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥K₀ c ∈ O),
                residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                ¬ IsUnit ((⟨_, hO'⟩ : ↥O) - ⟨_, hcO⟩))
  hN4frac : ∀ (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ), (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx) →
        (∀ f : ↥Kℓ, f ∈ Bx → f ∈ Õ) →
        (∀ f : ↥Kℓ, f ∈ Õ ↔ ∃ g h : ↥Kℓ, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g) →
        ∀ f : ↥K₀, ∃ g h : ↥K₀, (g : ↥Kℓ) ∈ Bx ∧ (h : ↥Kℓ) ∈ Bx ∧ h ≠ 0 ∧ f * h = g
  hjfix : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) = (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ)
  hN5 : ∀ (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ), (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx) →
        (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                  (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                      ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                    (∃ f : ↥Kℓ, f ∈ Õ ∧ f ∉ V) → b ∉ V)) →
        (∃ b : ↥K₀, b ∈ Bx.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧ ∀ V : ValuationSubring ↥K₀,
                    (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
                    (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                    ∀ (hjK' : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
                      (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                        ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                          (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                    (∃ f : ↥K₀, f ∈ O ∧ f ∉ V) → b ∉ V)
  hIGSEP : ∀ Wx : ValuationSubring ↥Kℓ, (∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) → IsDiscreteValuationRing ↥Wx →
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) →
        (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) →
        (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
        (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
          (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
          ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →
        (∀ O' ∈ ends, O' ≠ Õ → ∃ f : ↥Kℓ, f ∈ O' ∧ f ∉ Wx) →
        (∀ O' ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ →
          (∀ f : ↥Kℓ, f ∈ O' → τ f ∈ Wx) → O' = Õ) →
        ∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥K₀, f ∈ O' ∧ f ∉ Wx.comap (algebraMap ↥K₀ ↥Kℓ)


