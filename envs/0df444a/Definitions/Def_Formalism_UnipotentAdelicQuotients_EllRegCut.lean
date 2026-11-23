-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
-- name    : Formalism_UnipotentAdelicQuotients_EllRegCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:49.424832+00:00
-- url     : https://prove2.me/theorems/2ca8c0f0-38ce-42e5-b991-d566c6f86336
-- title:
--   Ell Reg Cut
-- statement:
--   Definitions and structural lemmas for Ell Reg Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllRegCut.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
def cut (χ : E d → ℝ) (g : E d → ℂ) : E d → ℂ := fun x => (χ x : ℂ) * g x
def om (s M ε : ℝ) (ξ : E d) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ε ^ 2 * ‖ξ‖ ^ 2) ^ (-(M / 2))
def nrm (s M ε : ℝ) (F : E d → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (om s M ε ξ) ^ 2 * ‖F ξ‖ₑ ^ 2
def Hs (s : ℝ) (g : E d → ℂ) : Prop := nrm s 0 0 (𝓕 g) < ⊤
def conv (K F : E d → ℂ) (ξ : E d) : ℂ := ∫ η, K (ξ - η) * F η
def eF (ξ : E d) (y : E d) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)))
def mono {n : ℕ} (w : Fin n → Fin d) (η : E d) : ℂ := ∏ l, (2 * Real.pi * Complex.I * ((η (w l) : ℝ) : ℂ))
def MomentsSmooth : Prop :=
  ∀ (d : ℕ) (g : E d → ℂ), Continuous g → HasCompactSupport g → (∀ s : ℕ, Hs (s : ℝ) g) → ContDiff ℝ ∞ g
def Bump : Prop :=
  ∀ (d : ℕ) (x0 : E d) (r : ℝ), 0 < r → ∃ χ : E d → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ ball x0 r ∧ χ =ᶠ[𝓝 x0] fun _ => 1
def CutCont : Prop :=
  ∀ (d : ℕ) (U : Set (E d)) (u : E d → ℂ) (χ : E d → ℝ), IsOpen U → ContinuousOn u U → ContDiff ℝ ∞ χ →
    HasCompactSupport χ → tsupport χ ⊆ U → Continuous (cut χ u) ∧ HasCompactSupport (cut χ u)
def LocalGlobal : Prop :=
  ∀ (d : ℕ) (U : Set (E d)) (f : E d → ℂ), IsOpen U →
    (∀ x0 ∈ U, ∃ χ : E d → ℝ, χ =ᶠ[𝓝 x0] (fun _ => 1) ∧ ContDiff ℝ ∞ (cut χ f)) → ContDiffOn ℝ ∞ f U
def BaseLevel : Prop :=
  ∀ (d : ℕ) (g : E d → ℂ), Continuous g → HasCompactSupport g → Hs (-(d : ℝ) - 1) g
def Step : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ), Hyp P U u →
    ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∀ s : ℝ,
      (∀ χ : E d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball x0 r → Hs s (cut χ u)) →
      ∀ χ : E d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball x0 r → Hs (s + 1) (cut χ u)
def LocalSobolev : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ), Hyp P U u →
    ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∀ χ : E d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ ball x0 r → ∀ s : ℕ, Hs (s : ℝ) (cut χ u)
def SymbLower : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (x0 : E d) (k : ℕ), (∀ i, P.ord i ≤ k) →
    (∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x0 ξ ≠ 0) →
    ∃ c > 0, ∀ ξ : E d, ξ ≠ 0 → c * ‖ξ‖ ^ (2 * k) ≤ ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2
def WeightDiff : Prop :=
  ∀ (d : ℕ) (s M : ℝ), 0 ≤ M → ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ ξ η : E d,
    |om s M ε ξ - om s M ε η| ≤ C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η
def ConvBound : Prop :=
  ∀ (d : ℕ) (s M ε C N : ℝ), 0 ≤ C →
    (∀ ξ η : E d, |om s M ε ξ - om s M ε η| ≤ C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η) →
    ∀ K F : E d → ℂ, Continuous K → Continuous F →
      nrm s M ε (conv K F) ^ (1 / 2 : ℝ) ≤
        (∫⁻ ζ, ‖K ζ‖ₑ) * nrm s M ε F ^ (1 / 2 : ℝ) +
          ENNReal.ofReal C * (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ) *
            nrm (s - 1) M ε F ^ (1 / 2 : ℝ)
def KernelSmall : Prop :=
  ∀ (d : ℕ) (U : Set (E d)) (a : E d → ℂ) (x0 : E d) (ψ0 : E d → ℝ), IsOpen U → x0 ∈ U →
    ContDiffOn ℝ ∞ a U → ContDiff ℝ ∞ ψ0 → HasCompactSupport ψ0 → tsupport ψ0 ⊆ ball 0 2 →
    ∃ r0 > 0, ∃ C : ℝ, ball x0 (2 * r0) ⊆ U ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      (∫⁻ ζ, ‖𝓕 (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (a x - a x0)) ζ‖ₑ) ≤ ENNReal.ofReal (C * r) ∧
      ∀ N : ℝ, (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) *
        ‖𝓕 (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (a x - a x0)) ζ‖ₑ) < ⊤
def PairingFourier : Prop :=
  ∀ (d m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (g : E d → ℂ),
    (∀ n w, ContDiff ℝ ∞ (b n w) ∧ HasCompactSupport (b n w)) → Continuous g → HasCompactSupport g →
    ∀ ξ : E d, ∫ y, g y * trOp m b (eF ξ) y =
      ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, conv (𝓕 (b n w)) (fun η => mono w η * 𝓕 g η) ξ
def DwExp : Prop :=
  ∀ (d : ℕ) (ξ : E d) (w : List (Fin d)),
    dw w (eF ξ) = fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y
def FourierPair : Prop :=
  ∀ (d : ℕ) (g : E d → ℂ), Continuous g → HasCompactSupport g → ∀ ξ : E d, ∫ y, g y * eF ξ y = 𝓕 g ξ
def PairingLocal : Prop :=
  ∀ (d m : ℕ) (b b' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (g φ : E d → ℂ) (V : Set (E d)), IsOpen V →
    tsupport g ⊆ V → (∀ n w, ∀ x ∈ V, b n w x = b' n w x) →
    ∫ y, g y * trOp m b φ y = ∫ y, g y * trOp m b' φ y
def WeakFourier : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ), Hyp P U u →
    ∀ (i : ι) (χ χ' : E d → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ContDiff ℝ ∞ χ' → HasCompactSupport χ' → tsupport χ' ⊆ U →
      (∀ x ∈ tsupport χ, χ' =ᶠ[𝓝 x] fun _ => 1) →
      ∃ c : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiff ℝ ∞ (c n w) ∧ HasCompactSupport (c n w)) ∧
        ∀ ξ : E d, ∫ y, cut χ u y * P.tr i (eF ξ) y =
          ∑ n ∈ Finset.range (P.ord i), ∑ w : Fin n → Fin d,
            ∫ y, cut χ' u y * c n w y * dw (List.ofFn w) (eF ξ) y
def StepOfParts : Prop :=
  SymbLower → WeightDiff → ConvBound → KernelSmall → PairingFourier → DwExp → FourierPair → PairingLocal →
    WeakFourier → Bump → CutCont → Step
end
end ZetaZeros.D.EllReg


