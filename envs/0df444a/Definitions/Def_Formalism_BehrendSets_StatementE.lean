-- Prove2me | Definitions.Def_Formalism_BehrendSets_StatementE
-- name    : Formalism_BehrendSets_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:53.958817+00:00
-- url     : https://prove2.me/theorems/3c9d2df1-cd15-403f-a8d8-03201785b281
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/StatementE.lean

import Definitions.Def_Formalism_BehrendSets_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
namespace Formalism.BehrendSets
def OrdDvd : Prop := ∀ (s l j : ℕ) (hl : Nat.Coprime l (2 ^ (s + 2))),
  orderOf (frob s l hl) ∣ 2 ^ j ↔
    ((l : ℤ) ≡ 1 [ZMOD (2 ^ (s + 2 - j) : ℕ)] ∨ (l : ℤ) ≡ -1 [ZMOD (2 ^ (s + 2 - j) : ℕ)])
def OrdLargeJ : Prop := ∀ (s J l : ℕ) (hl : Nat.Coprime l (2 ^ (s + 2))), 2 ≤ l →
  orderOf (frob s l hl) ≤ J → 2 ^ (s + 2) ≤ J * (l + 1)
open Classical in
def OrdSqJ : Prop := ∀ (s J Y : ℕ), 1 ≤ s → 1 ≤ J →
  ∑ l ∈ (range Y).filter
      (fun l => 2 ≤ l ∧ ∃ hl : Nat.Coprime l (2 ^ (s + 2)), orderOf (frob s l hl) ≤ J),
    Real.log l / (l : ℝ) ^ 2 ≤ 10 * (J : ℝ) ^ 2 * Real.log (2 * (2 : ℝ) ^ s) / ((2 : ℝ) ^ s) ^ 2
def OrdD : Prop := ∀ (s d : ℕ) (hd : Nat.Coprime d (2 ^ (s + 2))), d % 16 = 7 →
  orderOf (frob s d hd) = 2 ^ (s - 1)
def CInPhi : Prop := ∀ (G₀ H : Type) [Group G₀] [Group H], IsPGroup 2 H →
  ∀ (c₀ : G₀) (h : H), orderOf c₀ = 2 →
    ((c₀, (1 : H)) ∈ Subgroup.zpowers (c₀, h) ↔ h = 1)
def CInPhiZ : Prop := ∀ (G₀ : Type) [Group G₀] (s : ℕ) (c₀ : G₀) (h : ZMod (2 ^ s)), orderOf c₀ = 2 →
  ((c₀, Multiplicative.ofAdd (0 : ZMod (2 ^ s))) ∈ Subgroup.zpowers (c₀, Multiplicative.ofAdd h) ↔ h = 0)
def SpaceFree (Lw : ℕ) (S : Finset ℕ) : Prop :=
  ∀ i j : ℤ, i ≠ 0 → j ≠ 0 → i ≠ j → |i| ≤ (Lw : ℤ) → |j| ≤ (Lw : ℤ) →
    ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
      j * ((s₂ : ℤ) - (s₁ : ℤ)) ≠ i * ((s₃ : ℤ) - (s₁ : ℤ))
def SpaceFreePos (Lw : ℕ) (S : Finset ℕ) : Prop :=
  ∀ i j : ℤ, 0 < i → i < j → j ≤ (Lw : ℤ) →
    ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
      j * ((s₂ : ℤ) - (s₁ : ℤ)) ≠ i * ((s₃ : ℤ) - (s₁ : ℤ))
def SpaceFreePosOf : Prop := ∀ (Lw : ℕ) (S : Finset ℕ), SpaceFree Lw S → SpaceFreePos Lw S
open Classical in
def Spacing : Prop := ∀ (n Lw : ℕ) [NeZero n] (S : Finset ℕ),
  (∀ s ∈ S, 4 * Lw * s < n) → SpaceFreePos Lw S →
  ∀ h u t : ZMod n, Lw < addOrderOf h → ∀ j₀ : ℤ,
    ((Finset.Icc j₀ (j₀ + (Lw : ℤ))).filter (fun i : ℤ => t + i • h ∈ thick n S u)).card ≤ 2
def SpacingOrbit : Prop := ∀ (n c : ℕ) [NeZero n] (S : Finset ℕ),
  (∀ s ∈ S, c * s < n) →
  ∀ h u t : ZMod n, addOrderOf h ≤ c → ∀ i₁ i₂ : ℤ,
    t + i₁ • h ∈ thick n S u → t + i₂ • h ∈ thick n S u → t + i₁ • h = t + i₂ • h
def SpaceExists : Prop := ∃ C : ℝ, 0 < C ∧ ∀ n Lw : ℕ, 1 ≤ n → 1 ≤ Lw →
  ∃ S : Finset ℕ, (∀ s ∈ S, 4 * Lw * s < n) ∧ SpaceFree Lw S ∧
    (n : ℝ) * Real.exp (-C * Real.sqrt (Real.log n * Real.log (2 * (Lw : ℝ)))) / Lw ≤ (S.card : ℝ)
open Classical in
def TopsBadSplit : Prop := ∀ {α : Type} [DecidableEq α] (X : Finset α) (δ : ℝ) (L K : ℕ) (t : α)
  (𝒲 : Finset (Finset α)), 0 ≤ δ → δ ≤ 1 → (∀ W ∈ 𝒲, W.card ≤ L) →
  prob X δ (fun T => t ∈ T ∧ ∃ W ∈ 𝒲, K + 1 ≤ (T ∩ W).card)
    ≤ δ * (((𝒲.filter (fun W => t ∈ W)).card : ℝ) * ((L : ℝ) * δ) ^ K
        + ((𝒲.filter (fun W => t ∉ W)).card : ℝ) * ((L : ℝ) * δ) ^ (K + 1))
def BadOrbitE : Prop := ∀ (n : ℕ) [NeZero n] (h t : ZMod n) (δ : ℝ) (L₂ K : ℕ),
  0 ≤ δ → δ ≤ 1 → 1 ≤ L₂ →
  prob (Finset.univ : Finset (ZMod n)) δ
      (fun T => t ∈ T ∧ ∃ W ∈ orbitWindows n h t L₂, K + 1 ≤ (T ∩ W).card)
    ≤ δ * ((addOrderOf h : ℝ) * ((L₂ : ℝ) * δ) ^ K * (1 + L₂ * δ) + L₂ * ((L₂ : ℝ) * δ) ^ K)
open Classical in
def SelectGen : Prop := ∀ (n : ℕ) [NeZero n] (δ : ℝ) {ι : Type} (I : Finset ι) (ω β : ι → ℝ)
  (Bad : ι → ZMod n → Finset (ZMod n) → Prop),
  0 ≤ δ → δ ≤ 1 → 16 ≤ δ * n → (∀ p, 0 ≤ ω p) →
  (∀ p ∈ I, ∀ t, prob (Finset.univ : Finset (ZMod n)) δ (fun T => t ∈ T ∧ Bad p t T) ≤ δ * β p) →
  ∃ T : Finset (ZMod n), δ * n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * n ∧
    ∑ p ∈ I, ω p * ((T.filter (fun t => Bad p t T)).card : ℝ) ≤ 4 * δ * n * ∑ p ∈ I, ω p * β p
open Classical in
def SelectTops : Prop := ∀ (n : ℕ) [NeZero n] (δ : ℝ) (L₂ K : ℕ) {ι : Type} (I : Finset ι)
  (ω : ι → ℝ) (hh : ι → ZMod n),
  0 ≤ δ → δ ≤ 1 → 16 ≤ δ * n → 1 ≤ L₂ → (∀ p, 0 ≤ ω p) →
  ∃ T : Finset (ZMod n), δ * n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * n ∧
    ∑ p ∈ I, ω p * ((T.filter (fun t => ∃ W ∈ orbitWindows n (hh p) t L₂, K + 1 ≤ (T ∩ W).card)).card : ℝ)
      ≤ 4 * δ * n * ∑ p ∈ I, ω p *
          ((addOrderOf (hh p) : ℝ) * ((L₂ : ℝ) * δ) ^ K * (1 + L₂ * δ) + L₂ * ((L₂ : ℝ) * δ) ^ K)
def TrivStab : Prop := ∀ (E : Type) [Field E] [NumberField E] (k g : ℕ), g.Prime →
  Module.finrank ℚ E * k < g - 1 →
  ∀ Γ : Subgroup (GL (Fin k) E), Finite Γ → IsPGroup g Γ → Γ = ⊥
def vand {r : ℕ} (u : Fin r → ℝ) : ℝ := ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (u i - u j)
def dimV {r : ℕ} (u : Fin r → ℝ) : ℝ := vand u / ∏ i : Fin r, ((i : ℕ).factorial : ℝ)
def CountIdentity : Prop := ∀ (P : Type) [Fintype P] (f k m : ℕ) (v : ℝ) (mass κ : ℕ → ℝ)
  (u : P → Fin k → ℝ) (w : P → Fin (k + m - 1) → ℝ),
  Fintype.card P = f → 1 ≤ m → 0 < v → (∀ r, 0 < mass r) → (∀ r, 0 < κ r) →
  (∀ r, k < r → r ≤ k + m - 1 →
    mass r = mass (r - 1) * (((r - 1).factorial : ℝ) * (v / π) ^ r) ^ f
      * (2 * v) ^ (-(f : ℝ) / 2) * κ r) →
  (∀ ρ, vand (w ρ) ≠ 0) → (∀ ρ, vand (u ρ) ≠ 0) →
  Real.log (mass (k + m - 1) * ∏ ρ, dimV (w ρ)) - Real.log (mass k * ∏ ρ, dimV (u ρ))
    = (∑ ρ, (Real.log (vand (w ρ)) - Real.log (vand (u ρ))))
      + (f : ℝ) * (((m : ℝ) - 1) * k + (m : ℝ) * ((m : ℝ) - 1) / 2) * Real.log (v / π)
      - ((m : ℝ) - 1) * ((f : ℝ) / 2) * Real.log (2 * v)
      + ∑ r ∈ Finset.Ioc k (k + m - 1), Real.log (κ r)
def CountQuad : Prop := ∀ k r : ℕ,
  let N : ℚ := (k : ℚ) + 1 + 2 * r
  let m : ℚ := 2 * r + 2
  N ^ 2 - (N ^ 2 - ((k : ℚ) + 1) ^ 2 - 2 * r) / 2 - (k : ℚ) * ((k : ℚ) - 1) / 2
    - (k : ℚ) * ((k : ℚ) + 1) / 2 = m * (2 * k + m - 1) / 2
def lserE (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun d => ∑ i ∈ range (d + 1), if d = (p ^ 2) ^ i then 1 / (p : ℚ) ^ i else 0
def zetaCoeff (p : ℕ) (t : PowerSeries ℚ) (d : ℕ) : ℚ :=
  ∑ i ∈ range (d + 1), PowerSeries.coeff d (t ^ (p * (p ^ 2) ^ i)) / (p : ℚ) ^ (i + 1)
def LevelThree : Prop := ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
  (∃ t : PowerSeries ℚ, PowerSeries.constantCoeff t = 0 ∧ PowerSeries.subst t (lserE p) = PowerSeries.X) ∧
  ∀ t : PowerSeries ℚ, PowerSeries.constantCoeff t = 0 → PowerSeries.subst t (lserE p) = PowerSeries.X →
    padicValRat p (zetaCoeff p t (p ^ 3)) = -((p : ℤ) + 1)
def SymbolAtD : Prop := ∀ (q d : ℕ) [Fact q.Prime] [Fact d.Prime], q ≠ d → q % 4 = 3 → d % 4 = 3 →
  legendreSym q (-(d : ℤ)) = 1 → legendreSym d (-(q : ℤ)) = -1
end Formalism.BehrendSets


