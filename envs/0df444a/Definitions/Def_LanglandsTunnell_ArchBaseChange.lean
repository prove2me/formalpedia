-- Prove2me | Definitions.Def_LanglandsTunnell_ArchBaseChange
-- name    : LanglandsTunnell_ArchBaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/eb4f193a-7ee9-5d83-8999-1b37815bed32
-- title:
--   Base change of archimedean parameters to complex places
-- statement:
--   For a parameter at a real place, given either as a principal-series datum `principal u₁ a₁ u₂ a₂` with $u_1,u_2\in\mathbb C$ and signs $a_1,a_2\in\mathbb Z/2$, or as a discrete-series datum `discrete u k hk` with $u\in\mathbb C$ and $k\geq 1$, `RealArchParam.baseChange` produces a parameter at a complex place (a quadruple $(u_1,k_1,u_2,k_2)$ with $u_i\in\mathbb C$, $k_i\in\mathbb Z$): the principal datum goes to $(u_1,0,u_2,0)$, and the discrete datum to $(u,k,u,-k)$. The accompanying identities record that the central twist $k_1+k_2$ of a base-changed parameter vanishes, that its central exponent agrees with that of the original, that `oddArtin` base-changes to `ComplexArchParam.trivialArtin`, and the explicit $\Gamma_{\mathbb C}$-shift multisets of twists: $\{u_1+u+|k|/2,\,u_2+u+|k|/2\}$ in the principal case twisted by $(u,k)$, and $\{u+u_0+k_0/2\}$ doubled in the discrete case twisted by $(u,0)$. Further identities state that passing to the dual commutes with base change up to equality of the $\Gamma_{\mathbb C}$-multisets (with or without a further twist by $(u,k)$), that the epsilon factor of a base-changed principal parameter is $1$ and of a base-changed discrete parameter is $(-1)^k$, that $\Gamma_{\mathbb R}(x+\delta(b))\Gamma_{\mathbb R}(x+\delta(b+1))=\Gamma_{\mathbb C}(x)$ for the sign shift $\delta$ (values $0$ and $1$), and, as a consequence, that the archimedean factor of the base-changed parameter twisted by $(u,0)$ equals the product of the two archimedean factors of the real parameter twisted by $(u,a)$ and $(u,a+1)$, for either shape.
--
--   Over a number field $K$, `archOfParamR` and `archOfParamC` are the families assigning a fixed real parameter $P$ to every real place and $P^{\mathbb C}$ to every complex place; `rsGammaR` and `rsGammaC` abbreviate the corresponding `twistedGammaR` and `twistedGammaC`, i.e. the sums over real places of the $\Gamma_{\mathbb R}$-shifts, resp. over real and complex places of the $\Gamma_{\mathbb C}$-shifts, of the locally twisted parameters. For constant twist data these are evaluated as $r_1(K)$- and $r_2(K)$-fold multiset multiples (`nrRealPlaces`, `nrComplexPlaces`) of the shifts of $P$ and $P^{\mathbb C}$, with the principal and discrete cases written out explicitly (the $\Gamma_{\mathbb R}$-multiset vanishing in the discrete case); the dual families are evaluated in the same way, and the archimedean root number of constant data is $\varepsilon(P\text{ twisted})^{r_1(K)}\varepsilon(P^{\mathbb C}\text{ twisted})^{r_2(K)}$.
--
--   **Relation to Mathlib.** The parameter types, their twists, duals, $\Gamma$-shift multisets and epsilon factors are the project's own; the Gamma factors $\Gamma_{\mathbb R}$, $\Gamma_{\mathbb C}$ with their product identity, and the counts of real and complex infinite places, are Mathlib's.
--
--   **Where it is used.** These are the archimedean ingredients of the $L$-data attached to a twisted Hecke eigensystem over a number field, as used on the converse-theorem side of the Langlands–Tunnell step that supplies modularity of the residual mod $3$ representation in the deduction of Fermat's Last Theorem. The content is the bookkeeping of Gamma shifts, signs and epsilon factors under base change from a real to a complex place, and its spreading over all infinite places of $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ArchBaseChange.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace LanglandsTunnell

open Complex NumberField

namespace RealArchParam

def baseChange : RealArchParam → ComplexArchParam
  | principal u₁ _ u₂ _ => ⟨u₁, 0, u₂, 0⟩
  | discrete u k _ => ⟨u, (k : ℤ), u, -(k : ℤ)⟩

theorem baseChange_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).baseChange = ⟨u₁, 0, u₂, 0⟩ := rfl

theorem baseChange_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).baseChange = ⟨u, (k : ℤ), u, -(k : ℤ)⟩ := rfl

theorem centralTwist_baseChange (P : RealArchParam) : P.baseChange.centralTwist = 0 := by
  cases P <;> simp [baseChange, ComplexArchParam.centralTwist]

theorem centralExponent_baseChange (P : RealArchParam) :
    P.baseChange.centralExponent = P.centralExponent := by
  cases P <;> simp [baseChange, ComplexArchParam.centralExponent, centralExponent, two_mul]

theorem baseChange_oddArtin : oddArtin.baseChange = ComplexArchParam.trivialArtin := rfl

theorem gammaC_baseChange_twist_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ)
    (k : ℤ) :
    ((principal u₁ a₁ u₂ a₂).baseChange.twist u k).gammaC =
      {u₁ + u + (k.natAbs : ℂ) / 2, u₂ + u + (k.natAbs : ℂ) / 2} := by
  simp [baseChange, ComplexArchParam.twist, ComplexArchParam.gammaC]

theorem gammaC_baseChange_twist_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) (u : ℂ) :
    ((discrete u₀ k₀ hk).baseChange.twist u 0).gammaC =
      {u₀ + u + (k₀ : ℂ) / 2, u₀ + u + (k₀ : ℂ) / 2} := by
  simp [baseChange, ComplexArchParam.twist, ComplexArchParam.gammaC]

theorem gammaC_baseChange_dual (P : RealArchParam) :
    P.dual.baseChange.gammaC = P.baseChange.dual.gammaC := by
  cases P <;> simp [baseChange, dual, ComplexArchParam.dual, ComplexArchParam.gammaC]

theorem gammaC_baseChange_dual_twist (P : RealArchParam) (u : ℂ) (k : ℤ) :
    (P.dual.baseChange.twist u k).gammaC = (P.baseChange.dual.twist u k).gammaC := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    simp [baseChange, dual, ComplexArchParam.dual, ComplexArchParam.twist, ComplexArchParam.gammaC]
  | discrete u₀ k₀ hk =>
    simp only [baseChange, dual, ComplexArchParam.dual, ComplexArchParam.twist,
      ComplexArchParam.gammaC, neg_neg]
    exact Multiset.pair_comm _ _

theorem epsilonFactor_baseChange_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).baseChange.epsilonFactor = 1 := by
  simp [baseChange, ComplexArchParam.epsilonFactor]

theorem epsilonFactor_baseChange_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).baseChange.epsilonFactor = (-1) ^ k := by
  simp only [baseChange, ComplexArchParam.epsilonFactor, Int.natAbs_neg, Int.natAbs_natCast,
    ← pow_add, ← two_mul, pow_mul, I_sq]

theorem Gammaℝ_signShift_mul (x : ℂ) (b : ZMod 2) :
    Gammaℝ (x + signShift b) * Gammaℝ (x + signShift (b + 1)) = Gammaℂ x := by
  have h := Gammaℝ_mul_Gammaℝ_add_one x
  have h' : Gammaℝ (x + 1) * Gammaℝ x = Gammaℂ x := by rw [mul_comm]; exact h
  fin_cases b
  · change Gammaℝ (x + signShift 0) * Gammaℝ (x + signShift (0 + 1)) = Gammaℂ x
    rw [zero_add, signShift_zero, signShift_one, add_zero]
    exact h
  · change Gammaℝ (x + signShift 1) * Gammaℝ (x + signShift (1 + 1)) = Gammaℂ x
    rw [show (1 : ZMod 2) + 1 = 0 by decide, signShift_zero, signShift_one, add_zero]
    exact h'

theorem archFactor_baseChange_twist_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) (u : ℂ) (a : ZMod 2)
    (s : ℂ) :
    ((discrete u₀ k₀ hk).baseChange.twist u 0).archFactor s =
      ((discrete u₀ k₀ hk).twist u a).archFactor s *
        ((discrete u₀ k₀ hk).twist u (a + 1)).archFactor s := by
  simp [ComplexArchParam.archFactor, archFactor, gammaC_baseChange_twist_discrete, twist, gammaR,
    gammaC]

theorem archFactor_baseChange_twist_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ)
    (a : ZMod 2) (s : ℂ) :
    ((principal u₁ a₁ u₂ a₂).baseChange.twist u 0).archFactor s =
      ((principal u₁ a₁ u₂ a₂).twist u a).archFactor s *
        ((principal u₁ a₁ u₂ a₂).twist u (a + 1)).archFactor s := by
  have h₁ := Gammaℝ_signShift_mul (s + (u₁ + u)) (a₁ + a)
  have h₂ := Gammaℝ_signShift_mul (s + (u₂ + u)) (a₂ + a)
  simp only [ComplexArchParam.archFactor, archFactor, gammaC_baseChange_twist_principal, twist,
    gammaR, gammaC, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, Multiset.map_zero, Multiset.prod_zero, mul_one,
    Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, add_assoc] at h₁ h₂ ⊢
  rw [mul_mul_mul_comm, h₁, h₂]

end RealArchParam

namespace Converse

variable (K : Type) [Field K]

def archOfParamR (P : RealArchParam) : ∀ w : InfinitePlace K, w.IsReal → RealArchParam :=
  fun _ _ => P

def archOfParamC (P : RealArchParam) : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam :=
  fun _ _ => P.baseChange

theorem archOfParamR_apply (P : RealArchParam) (w : InfinitePlace K) (hw : w.IsReal) :
    archOfParamR K P w hw = P := rfl

theorem archOfParamC_apply (P : RealArchParam) (w : InfinitePlace K) (hw : w.IsComplex) :
    archOfParamC K P w hw = P.baseChange := rfl

variable [NumberField K]

abbrev rsGammaR (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) : Multiset ℂ :=
  twistedGammaR K (archOfParamR K P) uR aR

abbrev rsGammaC (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) : Multiset ℂ :=
  twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC

theorem rsGammaR_def (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) :
    rsGammaR K P uR aR = twistedGammaR K (archOfParamR K P) uR aR := rfl

theorem rsGammaC_def (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    rsGammaC K P uR aR uC kC = twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC :=
  rfl

theorem rsGammaR_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    rsGammaR K P (fun _ _ => u) (fun _ _ => a) =
      InfinitePlace.nrRealPlaces K • (P.twist u a).gammaR := by
  simp [rsGammaR, twistedGammaR, archOfParamR, Finset.sum_const, Finset.card_univ]

theorem rsGammaC_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) (u' : ℂ) (k' : ℤ) :
    rsGammaC K P (fun _ _ => u) (fun _ _ => a) (fun _ _ => u') (fun _ _ => k') =
      InfinitePlace.nrRealPlaces K • (P.twist u a).gammaC +
        InfinitePlace.nrComplexPlaces K • (P.baseChange.twist u' k').gammaC := by
  simp [rsGammaC, twistedGammaC, archOfParamR, archOfParamC, Finset.sum_const, Finset.card_univ]

theorem rsGammaR_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ) (a : ZMod 2) :
    rsGammaR K (.principal u₁ a₁ u₂ a₂) (fun _ _ => u) (fun _ _ => a) =
      InfinitePlace.nrRealPlaces K •
        ({u₁ + u + signShift (a₁ + a), u₂ + u + signShift (a₂ + a)} : Multiset ℂ) := by
  rw [rsGammaR_const]; rfl

theorem rsGammaR_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) (u : ℂ) (a : ZMod 2) :
    rsGammaR K (.discrete u₀ k₀ hk) (fun _ _ => u) (fun _ _ => a) = 0 := by
  rw [rsGammaR_const]; simp [RealArchParam.twist, RealArchParam.gammaR]

theorem rsGammaC_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ) (a : ZMod 2)
    (u' : ℂ) (k' : ℤ) :
    rsGammaC K (.principal u₁ a₁ u₂ a₂) (fun _ _ => u) (fun _ _ => a) (fun _ _ => u')
        (fun _ _ => k') =
      InfinitePlace.nrComplexPlaces K •
        ({u₁ + u' + (k'.natAbs : ℂ) / 2, u₂ + u' + (k'.natAbs : ℂ) / 2} : Multiset ℂ) := by
  rw [rsGammaC_const, RealArchParam.gammaC_baseChange_twist_principal]
  simp [RealArchParam.twist, RealArchParam.gammaC]

theorem rsGammaC_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) (u : ℂ) (a : ZMod 2) (u' : ℂ) (k' : ℤ) :
    rsGammaC K (.discrete u₀ k₀ hk) (fun _ _ => u) (fun _ _ => a) (fun _ _ => u') (fun _ _ => k') =
      InfinitePlace.nrRealPlaces K • ({u₀ + u + (k₀ : ℂ) / 2} : Multiset ℂ) +
        InfinitePlace.nrComplexPlaces K •
          ({u₀ + u' + (((k₀ : ℤ) + k').natAbs : ℂ) / 2,
            u₀ + u' + ((-(k₀ : ℤ) + k').natAbs : ℂ) / 2} : Multiset ℂ) := by
  rw [rsGammaC_const]
  simp [RealArchParam.twist, RealArchParam.gammaC, RealArchParam.baseChange, ComplexArchParam.twist,
    ComplexArchParam.gammaC]

theorem twistedGammaR_archOfParam_dual_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun _ _ => -u) (fun _ _ => a) =
      InfinitePlace.nrRealPlaces K • (P.dual.twist (-u) a).gammaR := by
  simp [twistedGammaR, archOfParamR, Finset.sum_const, Finset.card_univ]

theorem twistedGammaC_archOfParam_dual_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) (u' : ℂ)
    (k' : ℤ) :
    twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual) (fun _ _ => -u) (fun _ _ => a) (fun _ _ => -u')
        (fun _ _ => -k') =
      InfinitePlace.nrRealPlaces K • (P.dual.twist (-u) a).gammaC +
        InfinitePlace.nrComplexPlaces K • (P.dual.baseChange.twist (-u') (-k')).gammaC := by
  simp [twistedGammaC, archOfParamR, archOfParamC, Finset.sum_const, Finset.card_univ,
    RealArchParam.gammaC_baseChange_dual_twist]

theorem archRootNumber_archOfParam_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) (u' : ℂ)
    (k' : ℤ) :
    archRootNumber K (archOfParamR K P) (archOfParamC K P) (fun _ _ => u) (fun _ _ => a)
        (fun _ _ => u') (fun _ _ => k') =
      (P.twist u a).epsilonFactor ^ InfinitePlace.nrRealPlaces K *
        (P.baseChange.twist u' k').epsilonFactor ^ InfinitePlace.nrComplexPlaces K := by
  simp [archRootNumber, archOfParamR, archOfParamC, Finset.prod_const, Finset.card_univ]

end Converse

end LanglandsTunnell

end


