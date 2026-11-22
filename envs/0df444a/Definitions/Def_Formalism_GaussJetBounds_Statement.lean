-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_Statement
-- name    : Formalism_GaussJetBounds_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:39.722018+00:00
-- url     : https://prove2.me/theorems/755a84ce-a634-4f53-bb46-bf053e74ca35
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/Statement.lean

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
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
universe u v
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
section Weights
variable {K : Type u} [NormedField K] {ι : Type v}
def dot (n : ι →₀ ℕ) (r : ι → ℝ) : ℝ := n.sum fun i k => (k : ℝ) * r i
def MonoWtGe (pi : ℝ) (r : ι → ℝ) (w : ℝ) (n : ι →₀ ℕ) (c : K) : Prop :=
  ‖c‖ ≤ pi ^ (w - dot n r)
def WtGe (pi : ℝ) (r : ι → ℝ) (w : ℝ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, MonoWtGe pi r w n (MvPowerSeries.coeff n f)
def Integral (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, ‖MvPowerSeries.coeff n f‖ ≤ 1
def mvExp [CharZero K] (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  PowerSeries.subst f (PowerSeries.exp K)
def mfact (κ : ι →₀ ℕ) : ℕ := κ.prod fun _ k => k.factorial
end Weights
section Letters
variable {K : Type u} [Field K] {d : ℕ}
def lw (l : ℕ) (s : ZMod d) : ℤ := (if s.val % 2 = 0 then 1 else -1) * (l : ℤ) ^ s.val
def torus (l : ℕ) (ζ : K) : ZMod d → MvPowerSeries (ZMod d) K :=
  fun s => MvPowerSeries.C (ζ ^ lw l s) * MvPowerSeries.X s
def degE [NeZero d] (n : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if s.val % 2 = 0 then n s else 0
def degO [NeZero d] (n : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if s.val % 2 = 0 then 0 else n s
def NoLowBidegree [NeZero d] (be : MvPowerSeries (ZMod d) K) : Prop :=
  ∀ n : ZMod d →₀ ℕ, MvPowerSeries.coeff n be ≠ 0 →
    0 < degE n ∧ 0 < degO n ∧ ¬ (degE n = 1 ∧ degO n = 1)
abbrev V2 (d : ℕ) := Bool × ZMod d
def s0 (s : ZMod d) : MvPowerSeries (V2 d) K := MvPowerSeries.X (false, s)
def s1 (s : ZMod d) : MvPowerSeries (V2 d) K :=
  MvPowerSeries.X (false, s) + if s.val % 2 = 0 then MvPowerSeries.X (true, s) else 0
def s2 (s : ZMod d) : MvPowerSeries (V2 d) K :=
  if s.val % 2 = 0 then MvPowerSeries.X (true, s) else MvPowerSeries.X (false, s)
def s1' (s : ZMod d) : MvPowerSeries (V2 d) K :=
  MvPowerSeries.X (false, s) + if s.val % 2 = 0 then 0 else MvPowerSeries.X (true, s)
def s2' (s : ZMod d) : MvPowerSeries (V2 d) K :=
  if s.val % 2 = 0 then MvPowerSeries.X (false, s) else MvPowerSeries.X (true, s)
def de1 (be : MvPowerSeries (ZMod d) K) : MvPowerSeries (V2 d) K :=
  MvPowerSeries.subst s1 be - MvPowerSeries.subst s0 be - MvPowerSeries.subst s2 be
def de2 (be : MvPowerSeries (ZMod d) K) : MvPowerSeries (V2 d) K :=
  MvPowerSeries.subst s1' be - MvPowerSeries.subst s0 be - MvPowerSeries.subst s2' be
def letterLog (l : ℕ) (x : V2 d) : MvPowerSeries (V2 d) K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (x.1, x.2 - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0
def IsBiPower (l : ℕ) (n : ZMod d →₀ ℕ) : Prop :=
  ∃ (s s' : ZMod d) (α β : ℕ), s.val % 2 = 0 ∧ s'.val % 2 = 1 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
    s + (α : ZMod d) = s' + (β : ZMod d) ∧
    n = Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)
end Letters
def BHyp {K : Type u} [NormedField K] [CharZero K] (l d : ℕ) [NeZero d] (K0 : Subfield K)
    (ζ : K) (be : MvPowerSeries (ZMod d) K) : Prop :=
  (∀ n, MvPowerSeries.coeff n be ∈ K0) ∧
  MvPowerSeries.subst (torus l ζ) be = be ∧
  NoLowBidegree be ∧
  (Integral (MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de1 be))) ∧
    MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de1 be))) = 1) ∧
  (Integral (MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de2 be))) ∧
    MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de2 be))) = 1)
def Unram {K : Type u} [NormedField K] (l : ℕ) (K0 : Subfield K) : Prop :=
  ∀ a ∈ K0, a ≠ 0 → ∃ k : ℤ, ‖a‖ = ‖(l : K)‖ ^ k
def LemmaS : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d],
    l.Prime → Odd l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be ∧
      ∀ n, ¬ IsBiPower l n →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n (MvPowerSeries.coeff n be)
def LemmaSt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d],
    l.Prime → ‖(l : K)‖ < 1 →
    ∀ g : V2 d → MvPowerSeries (V2 d) K, (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (letterLog (K := K) l x) = MvPowerSeries.X x) →
      ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (g x)
section Entries
variable {K : Type u} [Field K] {d N0 N1 : ℕ}
abbrev ZV (d N0 N1 : ℕ) := ZMod d × Fin N0 × Fin N1
def entLog (l : ℕ) (x : ZV d N0 N1) : MvPowerSeries (ZV d N0 N1) K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (x.1 - 2 * (e : ZMod d), x.2.1, x.2.2) ((l ^ 2) ^ e) then
      ((l : K) ^ e)⁻¹ else 0
def linSub {ι : Type v} [Fintype ι] (M : ZV d N0 N1 → ι → K) (x : ZV d N0 N1) :
    MvPowerSeries ι K :=
  ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i
def bSum {ι : Type v} [Fintype ι] (M : ZV d N0 N1 → ι → K) (be : MvPowerSeries (ZMod d) K) :
    MvPowerSeries ι K :=
  ∑ ab : Fin N0 × Fin N1, MvPowerSeries.subst (fun s => linSub M (s, ab.1, ab.2)) be
def pureMon {ι : Type v} [DecidableEq ι] (l : ℕ) (i j : ι) (α β : ℕ) : ι →₀ ℕ :=
  Finsupp.single i (l ^ α) + Finsupp.single j (l ^ β)
end Entries
def LemmaR : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → Odd l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K),
      (∀ x i, ‖M x i‖ ≤ 1) → (∀ x i, M x i ≠ 0 → lt i = x.1) →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (entLog (K := K) l x) = MvPowerSeries.X x) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U →
    ∀ (ε : K), (ε = 1 ∨ ε = -1) → ∀ (sig : ι → ℝ), (∀ i, 0 ≤ sig i) → ∀ κ : ι →₀ ℕ,
      (∀ (i j : ι) (α β : ℕ), pureMon l i j α β ≤ κ →
        ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
            (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be)) →
        1 ≤ (l : ℝ) ^ α * sig i + (l : ℝ) ^ β * sig j) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
          (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U) * mvExp (ε • bSum M be))‖ ≤
        ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) * (gam l - sig i)) -
          (Fintype.card ι : ℝ) * (Real.logb l (κ.degree : ℝ) + 1))
def ThmARadii : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (sig eps : ZMod d → ℝ), IsDualAll l d sig → (∀ s, 0 ≤ sig s) →
      (∀ s, 0 ≤ eps s) → (∀ s ∈ TT, ∀ e : ℕ, dTop d TT s = (e : ℕ∞) → ((l : ℝ) ^ e)⁻¹ ≤ eps s) →
      (∀ (s s' : ZMod d) (α β : ℕ) (τ τ' : ℝ), sig s ≤ τ → sig s' ≤ τ' → Odd (α + β) →
          s + (α : ZMod d) = s' + (β : ZMod d) → 1 ≤ (l : ℝ) ^ α * τ + (l : ℝ) ^ β * τ') ∧
      (∀ (s : ZMod d) (β j : ℕ) (τ : ℝ), 0 < j → 1 - (l : ℝ) ^ j * eps s ≤ τ →
          1 ≤ (l : ℝ) ^ (β + j) * eps s + (l : ℝ) ^ β * τ) ∧
      (∀ (s : ZMod d) (α j : ℕ) (τ : ℝ), 0 < j → ((l : ℝ) ^ j)⁻¹ ≤ τ →
          1 ≤ (l : ℝ) ^ α * eps s + (l : ℝ) ^ (α + j) * τ) ∧
      (∀ s ∈ TT, ∀ s' ∈ TT, ∀ α β : ℕ, Odd (α + β) →
          s + (α : ZMod d) = s' + (β : ZMod d) → 1 ≤ (l : ℝ) ^ α * eps s + (l : ℝ) ^ β * eps s')
def OneLetterRadius : Prop :=
  ∀ l : ℕ, 3 ≤ l → (∀ α β : ℕ, Odd (α + β) → 1 ≤ ((l : ℝ) ^ α + (l : ℝ) ^ β) / ((l : ℝ) + 1)) ∧
    gam l - 1 / ((l : ℝ) + 1) = rho l
def oneLog {K : Type u} [Field K] {τ : Type v} [DecidableEq τ] (l : ℕ) (x : τ) : MvPowerSeries τ K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single x ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0
def OneLetterR : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l N0 N1 : ℕ),
    l.Prime → Odd l → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ be : MvPowerSeries (ZMod 2) K, BHyp l 2 K0 ζ be →
    ∀ (ep : K), ‖ep‖ = 1 →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : Fin N0 × Fin N1 → ι → K),
      (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K,
      (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (oneLog (K := K) l x) = MvPowerSeries.X x) →
    ∀ U : MvPowerSeries (Fin N0 × Fin N1) K, Integral U →
    ∀ (sgn : K), (sgn = 1 ∨ sgn = -1) → ∀ κ : ι →₀ ℕ,
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
          (MvPowerSeries.subst (fun x => ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)
              (MvPowerSeries.subst g U) *
            mvExp ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
              (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
                ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be))‖ ≤
        ‖(l : K)‖ ^ (rho l * (κ.degree : ℝ) -
          (Fintype.card ι : ℝ) * (Real.logb l (κ.degree : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights


