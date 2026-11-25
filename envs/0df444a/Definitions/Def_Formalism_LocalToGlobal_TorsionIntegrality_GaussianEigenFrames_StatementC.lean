-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementC
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementC
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:23.355652+00:00
-- url     : https://prove2.me/theorems/cba1f9c5-a12f-413b-bac4-7280d0981060
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussianEigenFrames/StatementC.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementB
import Definitions.Def_Formalism_GaussJetBounds_StatementY
import Definitions.Def_Formalism_GaussJetBounds_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.GD
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4 TransInt
  opU taylorMv)
open Formalism.L2.Th1.Top (IsLatH phC)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.L2.Th1.G (linSub toZ phSum betaPair)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)
def LocNorm (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) {n : Type} [Fintype n]
    [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  ∃ (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (ε : ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ p ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
    relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) ≠ 0 ∧
    ‖ι ε‖ ≤ 1 ∧
    Formalism.L2.Th1.H.tens4 θ = ε • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₁
def TransIntC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → IntCurve (curveL p L ι) →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    TransInt p L ι ω₀ (logSer (curveL p L ι)) (phC p L ι)
def TensStd : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
  ∀ (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (ε : ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ¬ p ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) ≠ 0 →
    ‖ι ε‖ ≤ 1 →
    Formalism.L2.Th1.H.tens4 θ = ε • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₁ →
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ p ∣ N → (N : ℂ) • t ∈ Λ →
    ∃ G : MvPowerSeries (Fin 4 × n) ℂ_[p], Formalism.L2.Th1.C.IntMv (unitBall ℂ_[p]) G ∧
      linSub (fun w w' => ι (g₁.symm (Pi.single w' 1) w))
          (Formalism.L2.Th1.G.tens4 (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) t θ)))) =
        toZ (expSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι))
          (Formalism.L2.Th1.C.mvExp (-(phSum (fun _ => (1 : ℂ_[p])) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι))) * G)
def ShapeLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p]) (q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]),
    ‖th‖ ≤ ‖(dK : ℂ_[p])‖ ^ (1 / 2 : ℝ) → IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a₀ b₀ dK ha hdK lam hlam) h Λ v A u th q →
    ‖(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι)) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)‖ ≤ ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) ∧
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg ∧
      (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) =
        Formalism.DworkPowerSeriesWeights.mvExp ((-(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι)) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)) • betaPair H N0 N1 u) * sg
def ThmBLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p]) (q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]),
    ‖th‖ ≤ ‖(dK : ℂ_[p])‖ ^ (1 / 2 : ℝ) → IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a₀ b₀ dK ha hdK lam hlam) h Λ v A u th q →
    (∀ s, ‖u s‖ ≤ 1) →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) ℂ_[p]), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) → (∀ τ, size τ = ∑ c, ht τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) ℂ_[p])) (ht τ) (hht τ) (I τ))
          (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A))‖ ≤
        ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ s : H, ((size (false, s) : ℝ) -
          (if s ∈ TT then (nu1 (false, s) : ℝ) - nu2 (false, s) else 0) +
          (if s ∈ TT then (nu1 (true, s) : ℝ) else 0)))
def ThmBGaussLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p]) (q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]),
    ‖th‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) → IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a₀ b₀ dK ha hdK lam hlam) h Λ v A u th q →
    (∀ s, ‖u s‖ ≤ 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) →
      (∀ τ, size τ = ∑ c, ht τ c) →
    ∀ nn : ((Bool × H) × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff nn (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p])))
            (ht τ) (hht τ) (I τ))
          (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)))‖ ≤
        ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ s : H, ((size (false, s) : ℝ) -
          (if s ∈ TT then (nu1 (false, s) : ℝ) - nu2 (false, s) else 0) +
          (if s ∈ TT then (nu1 (true, s) : ℝ) else 0)))
def IntOpLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) →
    JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) ∧
    ∀ P : MvPolynomial ν ℂ_[p], (∀ k, ‖MvPolynomial.coeff k P‖ ≤ 1) →
      ‖jetPair P (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A))‖ ≤ 1
end Formalism.L2.Th1.GD


