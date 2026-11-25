-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementJ
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementJ
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:34.502311+00:00
-- url     : https://prove2.me/theorems/759bf6e9-7b1d-4ee3-bc78-3f2c74176d17
-- title:
--   Statement J
-- statement:
--   Definitions and structural lemmas for Statement J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussianEigenFrames/StatementJ.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementG
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
open NumberField
namespace Formalism.L2.Th1.GD
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4)
open Formalism.L2.Th1.Top (IsLatH phC)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.L2.Th1.G (betaPair)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)
def IsEigenFrame {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (th0 : ℂ_[p]) {n J H : Type} [Fintype n]
    [DecidableEq n] [Fintype J] {N0 N1 : ℕ} (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (E : Type) [Field E] [NumberField E] (cE s : E ≃+* E) (δ : E) (emb : Bool × H → (E →+* ℂ_[p]))
    (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)) (v : J → n → ℂ) (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) : Prop :=
  δ ^ 2 = -(p : E) ∧ cE δ = -δ ∧ s δ = -δ ∧ (∀ y, cE (cE y) = y) ∧ (∀ y, s (s y) = y) ∧
  (∀ y, s (cE y) = cE (s y)) ∧ Function.Injective emb ∧ (∀ τ ρ, emb τ δ = emb ρ δ) ∧
  (∀ t y, emb (true, t) y = emb (false, t) (s (cE y))) ∧ (∀ τ (y : E), s y = y → emb τ y ∈ MaximalUnramifiedExtension p) ∧
  (∀ e e' : 𝓞 E, (e' : E) = cE (e : E) → ∀ x y, matH h (act e x) y = matH h x (act e' y)) ∧
  (∀ e, ∀ x ∈ Λ, act e x ∈ Λ) ∧ (∀ j, InMul L Λ (v j)) ∧ (∀ j x, ‖A j x‖ ≤ 1) ∧
  (∀ (e : 𝓞 E) x i, mapVec (ι : ℂ →+* ℂ_[p]) (act e) (fun i' => frameM (ι : ℂ →+* ℂ_[p]) v A i' x) i =
    emb x.1 (e : E) * frameM (ι : ℂ →+* ℂ_[p]) v A i x) ∧
  ∀ (t : H) (ab ab' : Fin N0 × Fin N1), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
    ∑ j, ∑ k, A j ((false, t), ab) * ι (hOK L h (v j) (v k)) * A k ((true, t), ab') =
      (if ab = ab' then u t else 0) + th0 * e
def TensorNorm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (n : Type) [Fintype n] (h : Matrix n n ℂ)
    (E : Type) [Field E] (H : Type) [Fintype H] [DecidableEq H] (emb : Bool × H → (E →+* ℂ_[p]))
    (Ja Jl Jr : Type) [Fintype Ja] [Fintype Jl] [Fintype Jr] (v : Ja × Jl × Jr → n → ℂ)
    (hA : Ja → Ja → E) (hl : Jl → Jl → E) (hr : Jr → Jr → E) (N0 N1 : ℕ)
    (Gc : Bool × H → Ja → ℂ_[p]) (P : Bool × H → Jl → Fin N0 → ℂ_[p]) (P' : Bool × H → Jr → Fin N1 → ℂ_[p])
    (A : Ja × Jl × Jr → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (th : ℂ_[p]) (u : H → ℂ_[p]), ‖th‖ ≤ 1 →
    (∀ j k, ι (hOK L h (v j) (v k)) = ∑ ρ, emb ρ (hA j.1 k.1 * hl j.2.1 k.2.1 * hr j.2.2 k.2.2)) →
    (∀ j x, A j x = Gc x.1 j.1 * P x.1 j.2.1 x.2.1 * P' x.1 j.2.2 x.2.2) →
    (∀ τ ρ : Bool × H, ρ ≠ τ → ∀ α', ∑ α, Gc τ α * emb ρ (hA α α') = 0) →
    (∀ t, u t = ∑ α, ∑ α', Gc (false, t) α * emb (false, t) (hA α α') * Gc (true, t) α') →
    (∀ t, ‖u t‖ ≤ 1) →
    (∀ t a a', ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
      ∑ l, ∑ l₂, P (false, t) l a * emb (false, t) (hl l l₂) * P (true, t) l₂ a' =
        (if a = a' then 1 else 0) + th * e) →
    (∀ t b b', ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
      ∑ r, ∑ r₂, P' (false, t) r b * emb (false, t) (hr r r₂) * P' (true, t) r₂ b' =
        (if b = b' then 1 else 0) + th * e) →
    ∀ (t : H) (ab ab' : Fin N0 × Fin N1), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
      ∑ j, ∑ k, A j ((false, t), ab) * ι (hOK L h (v j) (v k)) * A k ((true, t), ab') =
        (if ab = ab' then u t else 0) + th * e
def ShapeEigenLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p])
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E)
    (emb : Bool × H → (E →+* ℂ_[p])) (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
    IsEigenFrame ι (cmL a₀ b₀ dK ha hdK lam hlam) (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) h Λ E cE s δ emb act v A u →
    ‖(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι)) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)‖ ≤ ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) ∧
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg ∧
      (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) =
        Formalism.DworkPowerSeriesWeights.mvExp ((-(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι)) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)) • betaPair H N0 N1 u) * sg
def ThmBEigenLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p])
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E)
    (emb : Bool × H → (E →+* ℂ_[p])) (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
    IsEigenFrame ι (cmL a₀ b₀ dK ha hdK lam hlam) (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) h Λ E cE s δ emb act v A u →
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
def ThmBGaussEigenLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p])
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E)
    (emb : Bool × H → (E →+* ℂ_[p])) (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
    IsEigenFrame ι (cmL a₀ b₀ dK ha hdK lam hlam) (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) h Λ E cE s δ emb act v A u →
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
def ShapeEigenFree : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
  ∀ g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p])
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E)
    (emb : Bool × H → (E →+* ℂ_[p])) (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
    IsEigenFrame ι (cmL a₀ b₀ dK ha hdK lam hlam) (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) h Λ E cE s δ emb act v A u →
    ‖(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι)) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)‖ ≤ ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) ∧
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg ∧
      (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) =
        Formalism.DworkPowerSeriesWeights.mvExp ((-(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι)) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)) • betaPair H N0 N1 u) * sg
def ThmBEigenFree : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
  ∀ g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p])
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E)
    (emb : Bool × H → (E →+* ℂ_[p])) (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
    IsEigenFrame ι (cmL a₀ b₀ dK ha hdK lam hlam) (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) h Λ E cE s δ emb act v A u →
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
def ThmBGaussEigenFree : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
  ∀ g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p])
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E)
    (emb : Bool × H → (E →+* ℂ_[p])) (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
    IsEigenFrame ι (cmL a₀ b₀ dK ha hdK lam hlam) (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) h Λ E cE s δ emb act v A u →
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
end Formalism.L2.Th1.GD


