-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
-- name    : Formalism_MirabolicMackeyTheory_StatementT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:41:44.025553+00:00
-- url     : https://prove2.me/theorems/c8cb4e81-675b-4f5d-a869-69c397926e94
-- title:
--   Statement T
-- statement:
--   Definitions and structural lemmas for Statement T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/StatementT.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
section Defs
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)
def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)
def ellw (w : HeightOneSpectrum (𝓞 K)) : ℝ := (plc w : ℝ) / Real.sqrt (ramw w : ℝ)
end Defs
def RamBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (plc w).Prime ∧ 1 ≤ ramw w ∧ plc (conjPl w) = plc w ∧ ramw (conjPl w) = ramw w ∧
      2 / ellw w ^ 2 = (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)
def PlaceSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (X : ℕ → ℝ), (∀ p, 0 ≤ X p) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * X (plc w)) ≤ ∑ p ∈ S.image plc, Real.log (p : ℝ) * X p
def DepthCases : Prop :=
  ∀ (e ec F : ℝ),
    (∀ a : ℝ, e ≤ F + a + 1 → ec ≤ F + a + 1 → e + ec - 2 * F ≤ 2 * a + 2) ∧
    (e = 0 → ec = 0 → 0 ≤ F → e + ec - 2 * F ≤ 0) ∧
    (∀ s T β : ℝ, e ≤ s + T + 1 → ec ≤ s + T + 1 → -(2 * β) ≤ F → F ≤ 0 →
      e + ec - 2 * F ≤ 2 * (s + T + 1) + 4 * β) ∧
    (∀ s T : ℝ, e ≤ s + T + 1 → ec ≤ s + T + 1 → F = 0 → e + ec - 2 * F ≤ 2 * s + 2 * T + 2) ∧
    (∀ T nn nnc g2 : ℝ, e ≤ 2 * T - nn → ec ≤ 2 * T - nnc → nn + nnc = -(2 * F) →
      e + ec - 2 * F + 2 * g2 ≤ 4 * T + 2 * g2)
def NormaliserPair : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (π : K), π ≠ 0 →
    ∀ Dp Dm : ℕ, vw w (star π ^ Dp * π ^ Dm) + vw (conjPl w) (star π ^ Dp * π ^ Dm) =
      ((Dp : ℤ) + (Dm : ℤ)) * vw w (π * star π)
def LevelPair : Prop :=
  ∀ (en enc T vs vsc nn nnc frn Dp Dm F : ℝ), en ≤ T + 1 → enc ≤ T + 1 → 1 ≤ T → 0 ≤ frn →
    vs = nn + frn → vsc = nnc + frn → nn + nnc = Dp + Dm → F = -(Dp + Dm) / 2 →
      (en - vs ≤ 2 * T - nn) ∧ (enc - vsc ≤ 2 * T - nnc) ∧ nn + nnc = -(2 * F) ∧
        (en - vs) + (enc - vsc) - 2 * F ≤ 4 * T
def ShareNum : Prop :=
  ∀ (dK d0 d U δq ep y del : ℝ), 0 < U → 0 < δq → 0 ≤ dK → 0 ≤ d0 → 0 ≤ ep → ep ≤ y → y ≤ 1 / 8 →
    0 ≤ del → del ≤ 1 / 4 → (1 - ep) * dK ≤ U * d0 → (1 - y) * U ≤ δq → (1 - del) * d0 ≤ d →
      dK / δq ≤ 2 * d
def UnipNum : Prop :=
  ∀ (f r d dK δq : ℝ), 0 ≤ f → 1 ≤ r → 0 ≤ d → dK / δq ≤ 3 * d →
    f * r * (r - 1) / 2 * (d + dK / δq) ≤ 2 * f * r ^ 2 * d
def BudgetNum : Prop :=
  ∀ (dK δq D B : ℝ), 0 < δq → 0 < D → 0 ≤ B → dK / δq ≤ 3 * D →
    2 * (2 * (dK * B)) / (δq * D) ≤ 12 * B
def errGood (Y X2 A1 A2 kw T : ℝ) (th add : ℕ → ℝ) (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ Y then
    2 * (A1 / (p : ℝ) + kw * th p + T * add p + (if X2 < (p : ℝ) then A2 / (p : ℝ) ^ 2 else 0)) + 2
  else 0
def PrimeSums (Y X2 T Cth Cadd : ℝ) (th add : ℕ → ℝ) : Prop :=
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) → ∑ p ∈ Q, Real.log (p : ℝ) ≤ 1.02 * Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X2) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, th p * Real.log (p : ℝ) ≤ Cth) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → T * ∑ p ∈ Q, add p * Real.log (p : ℝ) ≤ Cadd)
def ErrSumGood : Prop :=
  ∀ (PI : Finset ℕ), (∀ p ∈ PI, p.Prime) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → PrimeSums Y X2 T Cth Cadd th add →
      ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + 1.02 * Y)
def OnSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Bad : Finset ℕ) (eb : ℕ → ℝ), (∀ p, 0 ≤ eb p) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → PrimeSums Y X2 T Cth Cadd th add →
  ∀ (errl : HeightOneSpectrum (𝓞 K) → ℝ),
    (∀ w ∈ S, errl w ≤ if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w)) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + 1.02 * Y) +
          ∑ p ∈ Bad, Real.log (p : ℝ) * eb p
def AbsorbOn : Prop :=
  ∀ (C Cb L xe f m b k ws Se Y X2 bad : ℝ), 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m → 0 < b →
    1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2.04 * (C * k * ws) / X2 + 1.02 * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + 25 * C + Cb + 12) * xe * (f * m * b * L)
def UnitChange : Prop :=
  ∀ (ρ x y d r k δ ε : ℝ), 0 < ρ → 0 < δ →
    (x + y) * d + (r + k * y) / δ + ε =
      ρ * ((x / ρ + y / ρ) * d + (r / ρ + k * (y / ρ)) / δ + ε / ρ)
def OnExport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ), 0 < D →
  ∀ (Tup : Type) (μ : HeightOneSpectrum (𝓞 K) → Tup) (J : Type) [Fintype J] (d : J → ℕ),
    (∀ j, d j = D) →
  ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K))
    (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K))
    (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e0 r0 ε0 F0 errl Jx : HeightOneSpectrum (𝓞 K) → J → ℝ)
    (vU0 gq : HeightOneSpectrum (𝓞 K) → ℝ) (dK EA Rb EJ : J → ℝ) (δq E3 : ℝ), 0 < δq →
    (∀ w ∈ S, ∀ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) ≤
      (ramw w : ℝ) * ((e0 w j + vU0 w) * (d j : ℝ) + (r0 w j + dK j * vU0 w) / δq + ε0 w j)) →
    (∀ w ∈ S, ∀ j, (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) ≤
      (ramw (conjPl w) : ℝ) * ((e0 (conjPl w) j + vU0 (conjPl w)) * (d j : ℝ) +
        (r0 (conjPl w) j + dK j * vU0 (conjPl w)) / δq + ε0 (conjPl w) j)) →
    (∀ j, dK j / δq ≤ 3 * (D : ℝ)) →
    (∀ w ∈ S, 0 ≤ vU0 w ∧ vU0 (conjPl w) = vU0 w ∧ 4 * vU0 w ≤ gq w) →
    (∀ w ∈ S, ∀ j, e0 w j + e0 (conjPl w) j - 2 * F0 w j + 2 * gq w ≤ errl w j) →
    (∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 1 / (plc w : ℝ) ^ 2) →
    (∀ j, ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w j) ≤ EA j) →
    (∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ S', lw w * ((ramw w : ℝ) * r0 w j) ≤ Rb j) →
    (∀ j, ∑ w ∈ S, lw w * Jx w j ≤ EJ j) →
    ∑ w ∈ S, lw w * ((ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) ≤ E3 →
      (∀ w ∈ S, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
        (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) +
          2 / ellw w ^ 2) * D) ∧
      (∀ j, ∑ w ∈ S, lw w * ((ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))) +
          Jx w j) ≤ EA j + 2 * Rb j / (δq * (D : ℝ)) + EJ j) ∧
      ∑ w ∈ S, lw w * (2 / ellw w ^ 2) ≤ E3
end Formalism.EigenvalueLevelCeiling


