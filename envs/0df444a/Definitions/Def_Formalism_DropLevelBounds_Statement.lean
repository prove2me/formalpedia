-- Prove2me | Definitions.Def_Formalism_DropLevelBounds_Statement
-- name    : Formalism_DropLevelBounds_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:22.251611+00:00
-- url     : https://prove2.me/theorems/58f46dbb-debb-4e38-afc4-782e6f8ce48f
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DropLevelBounds/Statement.lean

import Definitions.Def_Formalism_IncomingBounds_ValuationWindowImpliesOriginal
import Definitions.Def_Formalism_IncomingBounds_LevelTail
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
namespace Formalism.UnitaryBoundIntegral
open Formalism.IncomingBounds
def ThmPv5 : Prop := ValuationWindowBound
def rowOf {n0 : ℕ} : PVar n0 → Fin n0 := Sum.elim Prod.fst Prod.fst
def rowDegZ {n0 : ℕ} (m : PVar n0 →₀ ℕ) (b : Fin n0) : ℕ := ∑ c : Fin n0, m (Sum.inl (b, c))
def rowDegZ' {n0 : ℕ} (m : PVar n0 →₀ ℕ) (b : Fin n0) : ℕ := ∑ c : Fin n0, m (Sum.inr (b, c))
def MplusRows {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (l n0 : ℕ)
    (h1 : MvPowerSeries (PVar n0) C) : Prop :=
  (∀ m : PVar n0 →₀ ℕ, MvPowerSeries.coeff m h1 ≠ 0 →
      ∃ b : Fin n0, ∀ x ∈ m.support, rowOf x = b) ∧
    (∀ m : PVar n0 →₀ ℕ, MvPowerSeries.coeff m h1 ≠ 0 → 1 ≤ degR m) ∧
    (∀ m : PVar n0 →₀ ℕ, degL m < l ^ 2 → degR m < l → 0 ≤ v (MvPowerSeries.coeff m h1))
def UBIntegral : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (n0 y : ℕ), y < l → ∀ h1 : MvPowerSeries (PVar n0) C, MplusRows v l n0 h1 →
      ∀ m : PVar n0 →₀ ℕ, (∀ b, rowDegZ m b ≤ l * y) → (∀ b, rowDegZ' m b ≤ y) →
        0 ≤ v (MvPowerSeries.coeff m (mvExp h1))
def UBUnit : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (n n0 y : ℕ), n0 ≤ n → y + n ≤ l - 1 →
    ∀ h1 : MvPowerSeries (PVar n0) C, MvPowerSeries.constantCoeff h1 = 0 →
      (∀ m : PVar n0 →₀ ℕ, (∀ b, rowDegZ m b ≤ l * y) → (∀ b, rowDegZ' m b ≤ y) →
        0 ≤ v (MvPowerSeries.coeff m (mvExp h1))) →
      v (LamP C l 1 n0 h1 y) = 0
def UBMplus : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (n n0 y : ℕ), n0 ≤ n → y + n ≤ l - 1 →
    ∀ h1 : MvPowerSeries (PVar n0) C, MplusRows v l n0 h1 →
      v (LamP C l 1 n0 h1 y) = 0
def DetPowDiag : Prop :=
  ∀ (R : Type) [CommRing R] (n0 n : ℕ) (hn : n0 ≤ n) (Y : ℕ) (e : (Fin n × Fin n) →₀ ℕ),
    (∀ ρ c : Fin n, n0 ≤ ρ.val → e (ρ, c) = if c = ρ then Y else 0) →
    MvPolynomial.coeff e
        ((Matrix.of fun b c : Fin n =>
          (MvPolynomial.X (b, c) : MvPolynomial (Fin n × Fin n) R)).det ^ Y) =
      MvPolynomial.coeff (e.filter fun x => x.1.val < n0)
        ((Matrix.of fun b c : Fin n0 =>
          (MvPolynomial.X (Fin.castLE hn b, Fin.castLE hn c) :
            MvPolynomial (Fin n × Fin n) R)).det ^ Y)
def embV {n0 n : ℕ} (hn : n0 ≤ n) : PVar n0 → PVar n :=
  Sum.map (Prod.map (Fin.castLE hn) (Fin.castLE hn)) (Prod.map (Fin.castLE hn) (Fin.castLE hn))
def restr {C : Type} [Field C] {n0 n : ℕ} (hn : n0 ≤ n) (G : MvPowerSeries (PVar n) C) :
    MvPowerSeries (PVar n0) C :=
  fun m => MvPowerSeries.coeff (m.mapDomain (embV hn)) G
def diagMon (n0 n L y : ℕ) : PVar n →₀ ℕ :=
  ∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val),
    (Finsupp.single (Sum.inl (ρ, ρ)) (L * y) + Finsupp.single (Sum.inr (ρ, ρ)) y)
def BlockJet : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 n : ℕ) (hn : n0 ≤ n) (L y : ℕ)
    (G1 H : MvPowerSeries (PVar n) C),
    (∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m G1 ≠ 0 → ∀ x ∈ m.support, (rowOf x).val < n0) →
    (∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m H ≠ 0 → ∀ x ∈ m.support, n0 ≤ (rowOf x).val) →
    (∀ m : PVar n →₀ ℕ, (∀ x ∈ m.support, n0 ≤ (rowOf x).val) →
      (∀ ρ : Fin n, n0 ≤ ρ.val → rowDegZ m ρ ≤ L * y ∧ rowDegZ' m ρ ≤ y) →
      MvPowerSeries.coeff m H = if m = diagMon n0 n L y then 1 else 0) →
    jetAt0 (detL C n ^ (L * y) * detR C n ^ y) (G1 * H) =
      ((((L * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) *
        jetAt0 (detL C n0 ^ (L * y) * detR C n0 ^ y) (restr hn G1)
def RestrictMul : Prop :=
  ∀ (C : Type) [Field C] (n0 n : ℕ) (hn : n0 ≤ n) (G G' : MvPowerSeries (PVar n) C),
    restr hn (G * G') = restr hn G * restr hn G'
def RestrictExp : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 n : ℕ) (hn : n0 ≤ n) (h : MvPowerSeries (PVar n) C),
    restr hn (mvExp h) = mvExp (restr hn h)
def leadMinor (R : Type) [CommRing R] (n k : ℕ) (hk : k ≤ n) : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.of fun b c : Fin k =>
    (MvPolynomial.X (Fin.castLE hk b, Fin.castLE hk c) : MvPolynomial (Fin n × Fin n) R)).det
def diagExp (n : ℕ) (e : Fin (n + 1) → ℕ) : (Fin n × Fin n) →₀ ℕ :=
  ∑ c : Fin n, Finsupp.single (c, c)
    (∑ k ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun k => c.val < k.val), e k)
def LeadMinorDiag : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (e : Fin (n + 1) → ℕ),
    MvPolynomial.coeff (diagExp n e)
        (∏ k : Fin (n + 1), leadMinor R n k.val (Nat.lt_succ_iff.mp k.isLt) ^ e k) = 1
def MonContent : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (σ : Type) (α : σ →₀ ℕ),
      v (mfact α : C) ≤ (((α.degree : ℝ) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) ∧
        ((∀ x, α x < l) → v (mfact α : C) = 0)
def BlockContent : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (i n n0 m y : ℕ), Odd i → n0 ≤ n → n - n0 ≤ (i + 3) * m → ∀ Λ : C,
      v Λ ≤ ((((n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1)) : ℝ) :
        WithTop ℝ) →
      v (((((l ^ i * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) * Λ) ≤
        ((((n : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1) +
          ((i : ℝ) + 3) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ)
def FScale : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (c : ℝ) (D : ZMod d → ℝ), 0 ≤ c → 0 ≤ D →
    Fnum l d (fun a => c * D a) = c * Fnum l d D
def ThetaShift : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (n : ℕ) (T θ : ℝ) (w W th : ZMod d → ℝ),
      0 < T → (∀ a, 0 < w a) → (∀ a, T * W a = w a * (1 - th a)) →
      (∀ a, 0 ≤ th a ∧ th a ≤ θ) → θ ≤ 1 / 2 →
      T * Fnum l d (fun a => (n : ℝ) * W a) ≤
        Fnum l d (fun a => (n : ℝ) * w a) + 6 * θ * n * (∑ a, w a) / l
def ThetaConst : Prop :=
  ∀ (n m : ℕ) (D T : ℝ), 1 ≤ m → 1 ≤ D → 0 < T → D * ((n : ℝ) + 1) / m ≤ T →
    6 * ((D + 4) / T) * n ≤ 30 * m
def ParametersSmall : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d →
    ∀ (n m : ℕ) (θ S : ℝ) (W : ZMod d → ℝ) (ys : ZMod d → ℕ → ℝ) (y : ZMod d → ℕ → ℕ)
      (u mon cCH cMON : ZMod d → ℝ) (cB eB : ZMod d → ℕ → ℝ),
      0 ≤ W → IsFlow l d W ys →
      maxFlow l d W - θ * (∑ a, W a) ≤ flowVal d ys →
      (∀ a i, (y a i : ℝ) ≤ ys a i) → (∀ a i, ys a i - y a i ≤ S) →
      (∀ a i, ys a i = 0 → y a i = 0) →
      (∀ a, 0 ≤ u a) → (∀ a, 0 ≤ mon a) →
      (∀ a, W a = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + u a + mon a) →
      (∀ a, ∀ i ∈ oddLevels d, cB a i ≤ n * y a i * (((l : ℝ) ^ i + 1) * gam l - 1) + eB a i) →
      (∀ a, cCH a ≤ u a * (n * gam l + m / ((l : ℝ) - 1))) →
      (∀ a, cMON a ≤ mon a / ((l : ℝ) - 1)) →
      (∑ a, ∑ i ∈ oddLevels d, cB a i) + (∑ a, cCH a) + (∑ a, cMON a) ≤
        Fnum l d (fun a => (n : ℝ) * W a) + n * θ * (∑ a, W a) +
          n * S * (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
            (fun p => ys p.1 p.2 ≠ 0)).card +
          (∑ a, ∑ i ∈ oddLevels d, eB a i) + m * (∑ a, u a) / ((l : ℝ) - 1) +
          (∑ a, mon a) / ((l : ℝ) - 1)
def DropLevelsBasic : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (W : ZMod d → ℝ), 0 ≤ W → ∀ i0 : ℕ,
    ∃ ys : ZMod d → ℕ → ℝ, IsFlow l d W ys ∧ (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → ys a i = 0) ∧
      (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
        (fun p => ys p.1 p.2 ≠ 0)).card ≤ d ∧
      maxFlow l d W - (∑ a, W a) / (l : ℝ) ^ i0 ≤ flowVal d ys
def SplitLarge : Prop :=
  ∀ (l n : ℕ) (l1 W ys : ℝ), 2 * n + 2 < l → 0 < l1 → l1 ≤ l → 0 ≤ ys →
    ((l : ℝ) + 1) * ys ≤ W →
    ∃ ps : List ℕ, (∀ p ∈ ps, p ≤ l - 1 - n) ∧ ps.sum = ⌊ys⌋₊ ∧
      (ps.length : ℝ) ≤ 2 * W / l1 ^ 2 + 1
def PhiNormal : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (M N n0 : ℕ) (Φ : Matrix (Fin M) (Fin N) O),
    n0 ≤ (Φ.map (IsLocalRing.residue O)).rank →
    ∃ (P : Matrix (Fin M) (Fin M) O) (σ : Equiv.Perm (Fin N)),
      IsUnit P.det ∧
        ∀ (b : Fin M) (c : Fin N), b.val < n0 → c.val < n0 →
          (P * Φ) b (σ c) = if b.val = c.val then -1 else 0
def ThetaBound : Prop :=
  ∀ (T D w c Y0 Sc : ℝ), 1 ≤ T → 0 ≤ D → 0 ≤ Y0 → 0 ≤ Sc → w - Y0 ≤ c → c ≤ w + Sc →
    T * (Y0 + (T + D + 2)) ≤ w → (D + 2) * (Sc + 2) ≤ w →
    (T * (⌊(c + 2) / (T + D + 2)⌋₊ : ℝ) ≤ w →
        0 ≤ 1 - T * (⌊(c + 2) / (T + D + 2)⌋₊ : ℝ) / w ∧
          1 - T * (⌊(c + 2) / (T + D + 2)⌋₊ : ℝ) / w ≤ (D + 4) / T) ∧
      (w < T * (⌊(c + 2) / (T + D + 2)⌋₊ : ℝ) →
        0 ≤ 1 - T * (⌊w / T⌋₊ : ℝ) / w ∧ 1 - T * (⌊w / T⌋₊ : ℝ) / w ≤ (D + 4) / T ∧
          (⌊(c + 2) / (T + D + 2)⌋₊ : ℝ) - (⌊w / T⌋₊ : ℝ) ≤ (Sc + 3) / T)
def ContentSmall : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (n m imax : ℕ) (T θ θl S : ℝ) (w W th : ZMod d → ℝ) (ys : ZMod d → ℕ → ℝ)
      (y : ZMod d → ℕ → ℕ) (u mon cCH cMON : ZMod d → ℝ) (cB : ZMod d → ℕ → ℝ),
      0 < T → (∀ a, 0 < w a) → (∀ a, T * W a = w a * (1 - th a)) →
      (∀ a, 0 ≤ th a ∧ th a ≤ θ) → θ ≤ 1 / 2 → 0 ≤ θl →
      IsFlow l d W ys → maxFlow l d W - θl * (∑ a, W a) ≤ flowVal d ys →
      (∀ a i, imax < i → ys a i = 0) →
      (∀ a i, (y a i : ℝ) ≤ ys a i) → (∀ a i, ys a i - y a i ≤ S) →
      (∀ a i, ys a i = 0 → y a i = 0) →
      (∀ a, 0 ≤ u a) → (∀ a, 0 ≤ mon a) →
      (∀ a, W a = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + u a + mon a) →
      (∀ a i, ys a i = 0 → cB a i = 0) →
      (∀ a, ∀ i ∈ oddLevels d, ys a i ≠ 0 → cB a i ≤ n * y a i * (((l : ℝ) ^ i + 1) * gam l - 1) +
        (n * (Real.logb l n + 1) + ((i : ℝ) + 3) * m * ((l : ℝ) ^ i + 1) * y a i / ((l : ℝ) - 1))) →
      (∀ a, cCH a ≤ u a * (n * gam l + m / ((l : ℝ) - 1))) →
      (∀ a, cMON a ≤ mon a / ((l : ℝ) - 1)) →
      T * ((∑ a, ∑ i ∈ oddLevels d, cB a i) + (∑ a, cCH a) + (∑ a, cMON a)) ≤
        Fnum l d (fun a => (n : ℝ) * w a) + 6 * θ * n * (∑ a, w a) / l + n * θl * (∑ a, w a) +
          T * ((((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
            (fun p => ys p.1 p.2 ≠ 0)).card : ℝ) * (n * S + n * (Real.logb l n + 1)) +
          2 * ((imax : ℝ) + 3) * m * (∑ a, w a) / ((l : ℝ) - 1) +
          m * (∑ a, w a) / ((l : ℝ) - 1) + T * (∑ a, mon a) / ((l : ℝ) - 1)
def RankChain : Prop :=
  ∀ (K V X : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup X] [Module K X] (U G : Submodule K V) (φ : V →ₗ[K] X),
    (Module.finrank K U : ℤ) - ((Module.finrank K V : ℤ) - Module.finrank K G) -
        Module.finrank K (LinearMap.ker φ) ≤
      Module.finrank K ((U ⊓ G).map φ)
def KerComp : Prop :=
  ∀ (K V V₂ V₃ : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] [AddCommGroup V₃] [Module K V₃]
    (f : V →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃),
    Module.finrank K (LinearMap.ker (g ∘ₗ f)) ≤
      Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.ker g)
def RankCount : Prop :=
  ∀ (i n j j' rh : ℕ), Odd i → rh ≤ j' →
    (n : ℤ) - (((i + 1) / 2 + 1 : ℕ) : ℤ) * j' - (((i - 1) / 2 : ℕ) : ℤ) * j' - rh - j ≥
      (n : ℤ) - ((i : ℤ) + 3) * ((j : ℤ) + j')
def CHValStep : Prop :=
  ∀ (A : Type) [CommRing A] (d : ℕ) [NeZero d] (l : ℕ), 2 ≤ l →
    ∀ (v : A → WithTop ℝ) (φ : A → A) (ξ : A) (h : ℕ) (p : ZMod d → ℕ) (de ε : ZMod d → A)
      (x : ZMod d → ℝ),
      (∀ a b, v (a * b) = v a + v b) → (∀ a, v (φ a) = (l : WithTop ℝ) * v a) →
      v ξ = 1 → (∀ a, v (ε a) = 0) → (∀ a, p a ≤ h) →
      (∀ a, v (de a) = ((x a : ℝ) : WithTop ℝ)) →
      (∀ a, de a * ξ ^ (h - p a) = ε a * φ (de (a - 1))) →
      ∀ a, x a = chSol d l ((h : ℝ)) (fun b => (p b : ℝ)) a
def UBContent : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (n n0 m y : ℕ), y < l → n0 ≤ n → n - n0 ≤ 4 * m → ∀ Λ : C, v Λ = 0 →
      v (((((l * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) * Λ) =
          ((((n - n0 : ℕ) : ℝ) * y : ℝ) : WithTop ℝ) ∧
        (((n - n0 : ℕ) : ℝ) * y ≤ 4 * (m : ℝ) * y)
def BlockWindow : Prop :=
  ∃ C0 : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (i : ℕ), Odd i → ∀ (n n0 m : ℕ), 1 ≤ n → n0 ≤ n → n - n0 ≤ (i + 3) * m →
    ∀ h1 : MvPowerSeries (PVar n0) C, MvPowerSeries.constantCoeff h1 = 0 →
      WeightCond v l i n0 h1 →
      ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧
        (y : ℝ) < Y0 + C0 * (n : ℝ) ^ 2 * ((i : ℝ) + Real.log ((n : ℝ) + 1)) ∧
        v (((((l ^ i * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) * LamP C l i n0 h1 y) ≤
          ((((n : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1) +
            ((i : ℝ) + 3) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ)
end Formalism.UnitaryBoundIntegral


