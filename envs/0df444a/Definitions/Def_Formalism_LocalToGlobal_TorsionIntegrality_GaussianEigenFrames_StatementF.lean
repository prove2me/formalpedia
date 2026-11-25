-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementF
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementF
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:15:41.055944+00:00
-- url     : https://prove2.me/theorems/6db40202-8ddb-4538-803a-5eeb3b4e8979
-- title:
--   Statement F
-- statement:
--   Definitions and structural lemmas for Statement F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussianEigenFrames/StatementF.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementE
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
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
def mapVec {K : Type} [Field K] (ι : ℂ →+* K) {n : Type} [Fintype n] [DecidableEq n]
    (T : (n → ℂ) →ₗ[ℂ] (n → ℂ)) (m : n → K) : n → K :=
  fun i => ∑ i', ι (T (Pi.single i' 1) i) * m i'
def GramBasic : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    ∀ B' B : J → ℂ_[p], (∀ j, ‖B' j‖ ≤ 1) → (∀ j, ‖B j‖ ≤ 1) →
      ‖∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k‖ ≤ 1 ∧
      (∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k -
          ∑ j, ∑ k, B j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B' k = ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e) ∧
      ((∀ i, ∑ k, B k * ι (v k i) = 0) → ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k = ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e) ∧
      ((∀ i, ∑ j, B' j * ι (v j i) = 0) →
        ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k = 0)
def EigenCompat : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    ∀ T T' : (n → ℂ) →ₗ[ℂ] (n → ℂ), (∀ x y, matH h (T x) y = matH h x (T' y)) → (∀ x ∈ Λ, T' x ∈ Λ) →
    ∀ (B' B : J → ℂ_[p]) (χ χ' : ℂ_[p]), (∀ j, ‖B' j‖ ≤ 1) → (∀ j, ‖B j‖ ≤ 1) → ‖χ'‖ ≤ 1 →
      (∀ i, mapVec (ι : ℂ →+* ℂ_[p]) T (fun i' => ∑ j, ι (v j i') * B' j) i = χ * ∑ j, ι (v j i) * B' j) →
      (∀ i, mapVec (ι : ℂ →+* ℂ_[p]) T' (fun i' => ∑ j, ι (v j i') * B j) i = χ' * ∑ j, ι (v j i) * B j) →
      ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        (χ - χ') * ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k = ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e
def EigenFrame : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]),
      (∀ j x, ‖A j x‖ ≤ 1) →
    ∀ (Xo : Type) (T T' : Xo → (n → ℂ) →ₗ[ℂ] (n → ℂ)) (chi chi' : Xo → Bool × H → ℂ_[p]),
      (∀ e x y, matH h (T e x) y = matH h x (T' e y)) → (∀ e, ∀ x ∈ Λ, T' e x ∈ Λ) →
      (∀ e τ, ‖chi' e τ‖ ≤ 1) →
      (∀ e x i, mapVec (ι : ℂ →+* ℂ_[p]) (T e) (fun i' => frameM (ι : ℂ →+* ℂ_[p]) v A i' x) i =
        chi e x.1 * frameM (ι : ℂ →+* ℂ_[p]) v A i x) →
      (∀ e x i, mapVec (ι : ℂ →+* ℂ_[p]) (T' e) (fun i' => frameM (ι : ℂ →+* ℂ_[p]) v A i' x) i =
        chi' e x.1 * frameM (ι : ℂ →+* ℂ_[p]) v A i x) →
      (∀ τ ρ : Bool × H, ρ ≠ (!τ.1, τ.2) → ∃ e, ‖chi e τ - chi' e ρ‖ = 1) →
      (∀ (t : H) (ab ab' : Fin N0 × Fin N1), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        ∑ j, ∑ k, A j ((false, t), ab) * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * A k ((true, t), ab') =
          (if ab = ab' then u t else 0) + ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e) →
      ∃ q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p],
        IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a b d ha hd lam hlam) h Λ v A u (ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ))) q
def IntNorm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ_[p]) (y : 𝓞 E), ‖φ (y : E)‖ ≤ 1
def EigenFrameE : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    p = d →
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E), δ ^ 2 = -(p : E) →
      cE δ = -δ → s δ = -δ → (∀ y, cE (cE y) = y) → (∀ y, s (s y) = y) → (∀ y, s (cE y) = cE (s y)) →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (emb : Bool × H → (E →+* ℂ_[p])), Function.Injective emb →
      (∀ τ ρ, emb τ δ = emb ρ δ) → (∀ t y, emb (true, t) y = emb (false, t) (s (cE y))) →
      (∀ τ (y : E), s y = y → emb τ y ∈ MaximalUnramifiedExtension p) →
    ∀ (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
      (∀ e e' : 𝓞 E, (e' : E) = cE (e : E) → ∀ x y, matH h (act e x) y = matH h x (act e' y)) →
      (∀ e, ∀ x ∈ Λ, act e x ∈ Λ) →
    ∀ (N0 N1 : ℕ) (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) →
      (∀ (e : 𝓞 E) x i, mapVec (ι : ℂ →+* ℂ_[p]) (act e) (fun i' => frameM (ι : ℂ →+* ℂ_[p]) v A i' x) i =
        emb x.1 (e : E) * frameM (ι : ℂ →+* ℂ_[p]) v A i x) →
      (∀ (t : H) (ab ab' : Fin N0 × Fin N1), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        ∑ j, ∑ k, A j ((false, t), ab) * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * A k ((true, t), ab') =
          (if ab = ab' then u t else 0) + ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e) →
      ∃ q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p],
        IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a b d ha hd lam hlam) h Λ v A u (ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ))) q
def HomGram : Prop :=
  ∀ (O L L' : Type) [CommRing O] [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L']
    (hL' : L' → L' → O) (N0 N1 : ℕ) (e es : Fin N0 → L) (e' es' : Fin N1 → L'),
    (∀ y, hL' 0 y = 0) → (∀ y, hL' y 0 = 0) → (∀ b b', hL' (e' b) (es' b') = if b = b' then 1 else 0) →
    ∀ (Eab Es : Fin N0 × Fin N1 → L →ₗ[O] L'),
      (∀ a b a', Eab (a, b) (e a') = if a = a' then e' b else 0) → (∀ a b a', Eab (a, b) (es a') = 0) →
      (∀ a b a', Es (a, b) (es a') = if a = a' then es' b else 0) → (∀ a b a', Es (a, b) (e a') = 0) →
    ∀ x y : Fin N0 × Fin N1,
      (∑ a, hL' (Eab x (e a)) (Es y (es a)) + ∑ a, hL' (Eab x (es a)) (Es y (e a))) =
        if x = y then 1 else 0
end Formalism.L2.Th1.GD


