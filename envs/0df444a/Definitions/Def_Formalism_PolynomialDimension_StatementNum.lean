-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_StatementNum
-- name    : Formalism_PolynomialDimension_StatementNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:23.53627+00:00
-- url     : https://prove2.me/theorems/8e4cd8b2-0382-477d-be38-b53d09427a35
-- title:
--   Statement Num
-- statement:
--   Definitions and structural lemmas for Statement Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/StatementNum.lean

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_WeylDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CountingSumsFrames
open Real Finset
def lgII (p : ℕ) (a : ℝ) (k : ℕ) : ℝ := Real.logb p (2 * a + k) + 1
def omII (r N n' c₀ c'' : ℕ) : ℝ := (r : ℝ) * N * c₀ + 2 * r * n' * c''
def QII (p G' : ℕ) : ℝ := (p : ℝ) ^ G'
def cPrII (r N n' c₀ c'' cStar : ℕ) : ℝ := (cStar : ℝ) + omII r N n' c₀ c''
def mStarII (N₁ k : ℕ) (Q c' al : ℝ) : ℝ := ((N₁ : ℝ) + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c')
def slII (Y : ℝ) (k : ℕ) (B : ℝ) : ℝ := ((⌊B / (Y * (k : ℝ) ^ 2)⌋ : ℤ) : ℝ)
def errorTerm (CE : ℝ) (N₁ r k : ℕ) (Q c' : ℝ) : ℝ := CE * c' * ((N₁ : ℝ) + r * k) * Q ^ 2
def HypII (C : ℝ) (p r N N₁ Nₛ J k n' L₁ G' : ℕ) (Y a : ℝ) (c₀ c'' D cStar : ℕ) : Prop :=
  13 ≤ p ∧ 2 ≤ r ∧ r ≤ N₁ ∧ N₁ ^ 2 ≤ r * N ∧ (r : ℝ) ≤ Y ∧
  C * (N₁ : ℝ) ^ 2 * Real.log a ≤ k ∧ N₁ + 3 * r ≤ k ∧
  256 * (k : ℝ) ^ 2 * N * Y ^ 2 ≤ (p : ℝ) ^ (L₁ - 1) ∧
  C * (N : ℝ) * (k : ℝ) ^ 2 * Real.logb p a ≤ D ∧ 8 * (D + 1) ≤ cStar ∧
  C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * (QII p G') ^ 5 * cPrII r N n' c₀ c'' cStar * Y ≤ a ∧
  1 ≤ L₁ ∧ L₁ ≤ G' ∧ Nₛ ≤ N₁ ∧ Nₛ ≤ 2 * N ∧ 1 ≤ J ∧ J * r ≤ N
def ParamsII0 : Prop :=
  ∀ CE C₂ : ℝ, 1 ≤ CE → 1 ≤ C₂ → ∃ C : ℝ, 1 ≤ C ∧
  ∀ (p r N N₁ Nₛ J k n' L₁ G' : ℕ) (Y a al : ℝ) (c₀ c'' D cStar : ℕ),
    HypII C p r N N₁ Nₛ J k n' L₁ G' Y a c₀ c'' D cStar →
    0 ≤ al → al ≤ 1 + r * k * QII p G' →
    32 * (p : ℝ) * Y * (k : ℝ) ^ 2 * Nₛ * (QII p G') ^ 2 *
        (errorTerm CE N₁ r k (QII p G') (cPrII r N n' c₀ c'' cStar) +
          mStarII N₁ k (QII p G') (cPrII r N n' c₀ c'' cStar) al + 1) ≤ a ∧
    (∀ B : ℝ, a / QII p G' ≤ B →
      100 * (r : ℝ) ^ 2 * cPrII r N n' c₀ c'' cStar + 24 * ((N₁ : ℝ) + r) * c₀ +
          mStarII N₁ k (QII p G') (cPrII r N n' c₀ c'' cStar) al ≤ slII Y k B ∧
        slII Y k B ≤ B / 100) ∧
    128 * (k : ℝ) ^ 2 * Nₛ * Y ^ 2 ≤ (p : ℝ) ^ (L₁ - 1) ∧
    C₂ * (Nₛ : ℝ) ^ 2 * Real.log a ≤ k ∧ 1 ≤ Y ∧ Nₛ + r ≤ k - r
def degreeLoss (p : ℕ) (a : ℝ) (k N r J : ℕ) : ℝ :=
  (N : ℝ) * (k : ℝ) ^ 2 * lgII p a k + 2 * N * ((r : ℝ) ^ 2 * lgII p a k) +
    (J : ℝ) * r * ((r : ℝ) ^ 2 * lgII p a k) + 2 * ((N : ℝ) * k * lgII p a k)
def kappaSecondRegime (p : ℕ) (a : ℝ) (k N : ℕ) : ℝ := (N : ℝ) * (k : ℝ) ^ 2 * lgII p a k
def ParamsII5 : Prop :=
  ∀ CE C₂ : ℝ, 1 ≤ CE → 1 ≤ C₂ → ∃ C : ℝ, 1 ≤ C ∧
  ∀ (p r N N₁ Nₛ J k n' L₁ G' : ℕ) (Y a : ℝ) (c₀ c'' D cStar : ℕ),
    HypII C p r N N₁ Nₛ J k n' L₁ G' Y a c₀ c'' D cStar →
    (∀ Q' B dw : ℝ, 1 ≤ Q' → Q' ≤ QII p G' → dw ≤ 3 * a / Q' → (p : ℝ) ^ L₁ * a / Q' ≤ B →
      dw ≤ 3 * (p : ℝ) ^ (-(L₁ : ℤ)) * B ∧ 3 * (p : ℝ) ^ (-(L₁ : ℤ)) * B ≤ slII Y k B / 8) ∧
    (∀ (Dd : ℕ) (Qj dj B : ℝ), (p : ℝ) ^ Dd ≤ QII p G' → 1 ≤ Qj → Qj ≤ QII p G' →
      dj ≤ 3 * a * (p : ℝ) ^ (-(Dd : ℤ) - L₁ - 1) → a / ((p : ℝ) ^ Dd * Qj) ≤ B →
      r * dj / Qj ≤ 3 * r * (p : ℝ) ^ (-(L₁ : ℤ) - 1) * B ∧
        3 * r * (p : ℝ) ^ (-(L₁ : ℤ) - 1) * B ≤ slII Y k B / 8) ∧
    2 * degreeLoss p a k N r J < cPrII r N n' c₀ c'' cStar ∧
    (∀ (B ms : ℝ), a / QII p G' ≤ B → ms ≤ ms + slII Y k B / 2 - 24 * cPrII r N n' c₀ c'' cStar) ∧
    (∀ B : ℝ, a / QII p G' ≤ B → 3 * ((N₁ : ℝ) + r) * c₀ ≤ slII Y k B / 8) ∧
    (D : ℝ) < cPrII r N n' c₀ c'' cStar / 2 ∧
    degreeLoss p a k N r J + kappaSecondRegime p a k N ≤ D
def t0II (Ct C₂ : ℝ) (p N Nₛ k L₁ G' : ℕ) (a : ℝ) : ℝ :=
  Ct * N * (C₂ * (Nₛ : ℝ) ^ 2 * Real.log a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * QII p G')
def tII (C : ℝ) (p r N N₁ k L₁ G' n' c₀ c'' : ℕ) (a : ℝ) : ℝ :=
  C * r * N * (C * (N₁ : ℝ) ^ 2 * Real.log a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + c₀ + k * QII p G') +
    2 * r * n' * c''
def ParamsII7 : Prop :=
  ∀ CE C₂ Ct : ℝ, 1 ≤ CE → 1 ≤ C₂ → 1 ≤ Ct → ∃ C : ℝ, 1 ≤ C ∧
  ∀ (p r N N₁ Nₛ J k n' L₁ G' : ℕ) (Y a : ℝ) (c₀ c'' D cStar : ℕ),
    HypII C p r N N₁ Nₛ J k n' L₁ G' Y a c₀ c'' D cStar →
    t0II Ct C₂ p N Nₛ k L₁ G' a + omII r N n' c₀ c'' ≤ tII C p r N N₁ k L₁ G' n' c₀ c'' a ∧
    t0II Ct C₂ p N Nₛ k L₁ G' a + N * c₀ + omII r N n' c₀ c'' ≤ tII C p r N N₁ k L₁ G' n' c₀ c'' a ∧
    (N : ℝ) * k * c₀ / a ≤ 1 / Y ∧
    1 - C * N * (r : ℝ) ^ 2 * k / Y ≤ (1 - C₂ * N * (r : ℝ) ^ 2 * k / Y) * (1 - 2 * k * c₀ / a) ^ N
def GramInequality : Prop :=
  ∀ (vB vC f₀ n₀ Dno nno n₁ ze Dl Dm κ₀ vAl vBe vbe : ℝ),
    vB = vC + (f₀ - vC / 2) + Dno + nno + n₁ - ze + Dl + Dm + κ₀ / 2 →
    vAl ≤ 2 * n₀ → vAl = vC + vBe → 2 * n₁ + 2 * nno - κ₀ ≤ vBe → f₀ ≤ n₀ → 0 ≤ ze →
    vbe = κ₀ + vB - 2 * n₀ →
    vB - 2 * n₀ ≤ Dno + Dl + Dm + κ₀ ∧ vbe ≤ Dno + Dm + Dl + 2 * κ₀
def GramError : Prop :=
  ∀ (n₁ ze c' κ₀ Dm Dl Dno nM vM vb : ℝ), 0 ≤ Dno → 0 ≤ Dm → 0 ≤ Dl → 0 ≤ κ₀ →
    2 * (Dno + Dm + Dl + 2 * κ₀) < c' →
    (c' - ze - n₁ + nM - κ₀ / 2 - Dm) + (nM - κ₀ / 2) ≤ vb → 2 * n₁ - κ₀ ≤ 2 * nM + vM →
    n₁ - ze + c' - 2 * κ₀ - Dm ≤ vM + vb ∧ n₁ - ze + Dl < n₁ - ze + c' - 2 * κ₀ - Dm
def FrameMultinomial : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r k N n : ℕ) (a : ℝ) (d : Fin n → ℕ) (M : Fin n → Fin r → ℕ),
    1 ≤ a → r + 1 ≤ k → n ≤ N → (∀ f, ∑ i, M f i ≤ d f) → (∀ f, (d f : ℝ) ≤ 2 * a) →
    (∀ f, ((padicValNat p (d f).factorial : ℝ) - padicValNat p (d f - ∑ i, M f i).factorial -
        ∑ i, (padicValNat p (M f i).factorial : ℝ)) ≤ ((r : ℝ) + 1) * lgII p a k) ∧
    ∑ f, ((padicValNat p (d f).factorial : ℝ) - padicValNat p (d f - ∑ i, M f i).factorial -
        ∑ i, (padicValNat p (M f i).factorial : ℝ)) ≤ (N : ℝ) * k * lgII p a k
def WeylFlat : Prop :=
  ∀ (m : ℕ) (mu : Fin (m + 1) → ℤ) (a' : ℕ) (c₀ : ℕ) (a : ℝ), 0 < a → Antitone mu →
    (∀ i, 0 ≤ mu i ∧ mu i ≤ c₀) → a ≤ a' → (a' : ℝ) ≤ 2 * a →
    (1 - 2 * ((m : ℝ) + 2) * c₀ / a) * (weylDim (m + 2) (Fin.cons ((a' : ℤ) + mu 0) mu) : ℝ) ≤
      ((a' + m + 1).choose (m + 1) : ℝ) * (weylDim (m + 1) mu : ℝ)
def lgI (p : ℕ) (a : ℝ) (k : ℕ) : ℝ := Real.logb p (8 * a + k) + 1
def uI (p : ℕ) (a : ℝ) (k : ℕ) : ℝ := 3 * lgI p a k + 4 * k * lgI p a k
def kap0I (p N k : ℕ) (a : ℝ) : ℝ := 2 * N * k * Real.logb p a
def constantBudget (p N k n' : ℕ) (a cl cStar : ℝ) : ℝ :=
  cStar + 4 * N * uI p a k + 4 * kap0I p N k a + 4 * N * cl + 2 * n' * cl
def HypI (C C₀ : ℝ) (p N N₁ k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ) : Prop :=
  1 ≤ Y ∧ (k : ℝ) ^ 2 * Y ^ 2 ≤ p ∧ 1 ≤ N ∧ 1 ≤ N₁ ∧ 2 * N₁ + 3 ≤ k ∧
  8 * Real.log (N * Y) ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a ∧
  Yb * N * (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k ≤ Ib ∧ Ib ≤ b' / 2 ∧ C ≤ Yb ∧
  2 * Yb * N * (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) < k ∧
  (k : ℝ) * Y ^ 2 * Yb * N * (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * Real.log a ≤ a / b' ∧
  C * N₁ * (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) / k + 2 * Ib / b' < 1 / 6 ∧ (p : ℝ) < a / b' ∧
  C * N * (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) ^ 2 ≤ k ∧
  0 ≤ cl ∧ cl ≤ (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k ∧
  C * N * Y ^ 2 * ((N₁ : ℝ) ^ 5 + (k : ℝ) ^ 3) * Real.logb p a ≤ D ∧ 8 * (D + 1) ≤ cStar ∧
  C * (k : ℝ) ^ 3 * N * ((p : ℝ) ^ G') ^ 4 * (cStar + N * cl + n' * cl) * Y ≤ b' ∧ 0 < b'
def ParamsI : Prop :=
  ∀ Cm Cd Ck Ct : ℝ, 1 ≤ Cm → 1 ≤ Cd → 1 ≤ Ck → 1 ≤ Ct → ∃ C : ℝ, 4 ≤ C ∧
  ∀ C₀ : ℝ, 3 ≤ C₀ →
  ∀ (p N N₁ k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ),
    HypI C C₀ p N N₁ k n' G' Y Yb a b' Ib cl D cStar →
    (∀ Ai : ℝ, b' / (2 * (p : ℝ) ^ G') ≤ Ai →
      2 * (Cm * k * N₁ * (p : ℝ) ^ G' * constantBudget p N k n' a cl cStar) + 12 * constantBudget p N k n' a cl cStar ≤
        (C * N₁ * (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) / k + 2 * Ib / b') * Ai / 4) ∧
    (N : ℝ) * cl * ((k : ℝ) * Y / a + 1 / Ib) ≤ 1 / Y ∧
    Ck * N * k * (2 * cl) / b' ≤ 1 / Y ∧
    (∀ Jseg : ℕ, Jseg ≤ N →
      2 * ((Jseg : ℝ) * (Cd * Y ^ 2 * (N₁ : ℝ) ^ 2 * (k : ℝ) ^ 2 * lgI p a k + 2 * kap0I p N k a) +
            4 * kap0I p N k a + 6 * N * uI p a k) +
          2 * N * ((k : ℝ) ^ 2 * lgI p a k) + Ck * kap0I p N k a ≤ D ∧
        (Jseg : ℝ) * (Cd * Y ^ 2 * (N₁ : ℝ) ^ 2 * (k : ℝ) ^ 2 * lgI p a k + 2 * kap0I p N k a) +
            4 * kap0I p N k a + 6 * N * uI p a k < (constantBudget p N k n' a cl cStar - 4 * N * uI p a k) / 2 ∧
        4 * ((Jseg : ℝ) * (Cd * Y ^ 2 * (N₁ : ℝ) ^ 2 * (k : ℝ) ^ 2 * lgI p a k + 2 * kap0I p N k a) +
            4 * kap0I p N k a) < constantBudget p N k n' a cl cStar) ∧
    Yb * N * ((C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k) ≤ a / (k * Y) ∧
    Yb * N * ((C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k) ≤ Ib ∧
    Yb * N * (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) ≤ k * Y ∧
    (∀ al : ℝ, a ≤ al →
      1 - 2 / (Yb * N) ≤ (1 - ((k : ℝ) - 1) * ((C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k) / al) *
        (1 - Real.exp (-(C₀ * (N₁ : ℝ) ^ 2 * Real.log a) / 3))) ∧
    1 / 2 ≤ (1 - 2 / (Yb * N)) ^ N ∧
    (∀ S S' : ℝ, 0 ≤ S → S' ≤ S + N * ((C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k + 2 * cl + constantBudget p N k n' a cl cStar) →
      S' + Ct * N * (a / (p : ℝ) ^ 2 + b' / p + (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * a / (p * k) +
            (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k + k * (p : ℝ) ^ G' +
            (p : ℝ) ^ G' * constantBudget p N k n' a cl cStar) +
          N * ((C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k) + 2 * N * uI p a k + 2 * kap0I p N k a +
          4 * N * cl + 2 * n' * cl ≤
        S + C * N * N₁ * (a / (p : ℝ) ^ 2 + b' / p + (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * a / (p * k) +
            (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) * b' / k) +
          C * N * ((p : ℝ) ^ G' * (cStar + C * N * k * Real.logb p a + 4 * N * cl + 2 * n' * cl) +
            k * (p : ℝ) ^ G' + k * Real.logb p a + cl) + 2 * n' * cl)
def KeptWeight : Prop :=
  ∀ Cw : ℝ, 0 ≤ Cw → ∃ C₀min : ℝ, 1 ≤ C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (N₁ : ℕ) (a k : ℝ), 1 ≤ N₁ → 3 ≤ a → 0 ≤ k → k ≤ a →
      (8 * a + k) ^ (9 * (N₁ + 1) ^ 2) * Real.exp (Cw * N₁ - C₀ * (N₁ : ℝ) ^ 2 * Real.log a / 5) ≤
        Real.exp (-(C₀ * (N₁ : ℝ) ^ 2 * Real.log a) / 8)
end Formalism.CountingSumsFrames


