-- Prove2me | Definitions.Def_Formalism_MoebiusJetDuality_StatementV
-- name    : Formalism_MoebiusJetDuality_StatementV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:07.738483+00:00
-- url     : https://prove2.me/theorems/3354f0c6-ae90-4c3f-9276-dfc30c96269a
-- title:
--   Statement V
-- statement:
--   Definitions and structural lemmas for Statement V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MoebiusJetDuality/StatementV.lean

import Definitions.Def_Formalism_MoebiusJetDuality_StatementS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MJ
open MvPolynomial
def partialDv {σ : Type} [DecidableEq σ] (i : σ) (f : (σ → ℂ) → ℂ) : (σ → ℂ) → ℂ :=
  fun z => deriv (fun t => f (Function.update z i t)) (z i)
def partialPowV {σ : Type} [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) (f : (σ → ℂ) → ℂ) :
    (σ → ℂ) → ℂ :=
  (Finset.univ : Finset σ).toList.foldr (fun i g => (partialDv i)^[α i] g) f
def degLe (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  (Finset.range (N + 1)).biUnion fun d => (Finset.univ : Finset σ).finsuppAntidiag d
def ajetPoly {σ : Type} [Fintype σ] [DecidableEq σ] (N : ℕ) (f : (σ → ℂ) → ℂ) :
    MvPolynomial σ ℂ :=
  ∑ α ∈ degLe σ N, monomial α (partialPowV α f 0 / (mfac α : ℂ))
def vjet {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (N : ℕ) (F : (σ → ℂ) → (Fin r → ℂ)) :
    Fin r → MvPolynomial σ ℂ :=
  fun i => ajetPoly N (fun z => F z i)
def actF {p q r : ℕ} (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ)) :
    (Fin p × Fin q → ℂ) → (Fin r → ℂ) :=
  fun z => ((ρ k : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec
    (F ((hcMat ((k.1⁻¹ : GL (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ)
      ((k.2 : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)).mulVec z))
def AJetPolyV : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) (F : MvPolynomial σ ℂ),
    ajetPoly N (fun z => eval z F) = jetTrunc N F
def AJetPolyCoeff : Prop :=
  ∀ (n N : ℕ) (f : (Fin n → ℂ) → ℂ) (α : Fin n →₀ ℕ), AnalyticAt ℂ f 0 →
    coeff α (ajetPoly N f) = if α.degree ≤ N then ajetCoeff f α else 0
def AJetSubstV : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) (g : Matrix σ σ ℂ) (f : (σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → ajetPoly N (fun z => f (g.mulVec z)) = linSubst g (ajetPoly N f)
def AJetMulV : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) (f h : (σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ h 0 →
      ajetPoly N (fun z => f z * h z) = jetTrunc N (ajetPoly N f * ajetPoly N h)
def AJetLinear : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) (c : ℂ) (f h : (σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ h 0 →
      ajetPoly N (fun z => c * f z + h z) = c • ajetPoly N f + ajetPoly N h
def ActFMul : Prop :=
  ∀ (p q r : ℕ) (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k k' : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ)),
    actF ρ (k * k') F = actF ρ k (actF ρ k' F)
def VJetEquiv : Prop :=
  ∀ (p q r N : ℕ) (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ)),
    (∀ i, AnalyticAt ℂ (fun z => F z i) 0) →
      vjet N (actF ρ k F) = actK ρ k (vjet N F)
def VJetInjective : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r : ℕ) (F : (σ → ℂ) → (Fin r → ℂ))
    (U : Set (σ → ℂ)),
    IsOpen U → IsPreconnected U → (0 : σ → ℂ) ∈ U → (∀ i, AnalyticOnNhd ℂ (fun z => F z i) U) →
      (∀ N, vjet N F = 0) → Set.EqOn F 0 U
end Formalism.MJ


