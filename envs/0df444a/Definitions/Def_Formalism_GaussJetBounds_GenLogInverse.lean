-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
-- name    : Formalism_GaussJetBounds_GenLogInverse
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:06:58.669224+00:00
-- url     : https://prove2.me/theorems/e327c595-f358-4d9e-a9e4-db2616ce34c7
-- title:
--   Gen Log Inverse
-- statement:
--   Definitions and structural lemmas for Gen Log Inverse, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GenLogInverse.lean

import Definitions.Def_Formalism_GaussJetBounds_Statement
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
universe u v w
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
def genLog {K : Type u} [Field K] {τ : Type v} [DecidableEq τ] (l : ℕ) (p : τ → τ) (x : τ) :
    MvPowerSeries τ K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0
def WtGeLe {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (κ : ι →₀ ℕ)
    (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, n ≤ κ → MonoWtGe pi r w n (MvPowerSeries.coeff n f)
def torus2 {K : Type u} [Field K] {d : ℕ} (l : ℕ) (ζ : K) : V2 d → MvPowerSeries (V2 d) K :=
  fun x => MvPowerSeries.C (ζ ^ lw l x.2) * MvPowerSeries.X x
def GenLogWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (τ : Type v) [Finite τ] [DecidableEq τ] (p : τ → τ)
    (g : τ → MvPowerSeries τ K), (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) →
      ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (g x)
def LogBridges : Prop :=
  ∀ (K : Type u) [Field K] (l d N0 N1 : ℕ),
    (∀ x : V2 d, letterLog (K := K) l x = genLog l (fun y : V2 d => (y.1, y.2 - 2)) x) ∧
    (∀ x : ZV d N0 N1, entLog (K := K) l x =
      genLog l (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) x) ∧
    (∀ x : Fin N0 × Fin N1, oneLog (K := K) l x = genLog l id x)
def GenLogInverse : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (l : ℕ), l.Prime → ∀ (τ : Type v) [Finite τ]
    [DecidableEq τ] (p : τ → τ),
    ∃ g : τ → MvPowerSeries τ K, (∀ x, MvPowerSeries.constantCoeff (g x) = 0) ∧
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) ∧
      (∀ x, MvPowerSeries.subst (genLog (K := K) l p) (g x) = MvPowerSeries.X x)
def SubstWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (σ : Type v) (τ : Type w) [Finite σ] (a : σ → MvPowerSeries τ K) (r : σ → ℝ) (r' : τ → ℝ)
      (wt : ℝ) (f : MvPowerSeries σ K),
      (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, WtGe pi r' (r i) (a i)) →
      WtGe pi r wt f → WtGe pi r' wt (MvPowerSeries.subst a f)
def RadMono : Prop :=
  ∀ (K : Type u) [NormedField K] (pi : ℝ), 0 < pi → pi < 1 → ∀ (ι : Type v) (r r' : ι → ℝ)
    (wt : ℝ), (∀ i, r i ≤ r' i) →
    (∀ f : MvPowerSeries ι K, WtGe pi r wt f → WtGe pi r' wt f) ∧
    (∀ (κ : ι →₀ ℕ) (f : MvPowerSeries ι K), WtGeLe pi r wt κ f → WtGeLe pi r' wt κ f)
def MulWtLe : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (pi : ℝ), 0 < pi →
    ∀ (ι : Type v) (r : ι → ℝ) (w1 w2 : ℝ) (κ : ι →₀ ℕ) (f g : MvPowerSeries ι K),
      WtGeLe pi r w1 κ f → WtGeLe pi r w2 κ g → WtGeLe pi r (w1 + w2) κ (f * g)
def ExpWtLe : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) (r : ι → ℝ) (κ : ι →₀ ℕ) (B : MvPowerSeries ι K),
      MvPowerSeries.constantCoeff B = 0 →
      WtGeLe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) κ B → WtGeLe ‖(l : K)‖ r 0 κ (mvExp B)
def FactVal : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) [Fintype ι] (κ : ι →₀ ℕ),
      ‖((mfact κ : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (κ.degree : ℝ) + 1))
def PureCross : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → ‖(l : K)‖ < 1 →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZV d N0 N1 → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ be : MvPowerSeries (ZMod d) K, MvPowerSeries.constantCoeff be = 0 →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be →
      (∀ n, ¬ IsBiPower l n →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n (MvPowerSeries.coeff n be)) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) (bSum M be) ∧
      ∀ n : ι →₀ ℕ, (¬ ∃ (i j : ι) (α β : ℕ), n = pureMon l i j α β) →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n (bSum M be))
def LogStep : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) (r : ι → ℝ) (D : MvPowerSeries ι K),
      MvPowerSeries.constantCoeff D = 0 →
      WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (mvExp D - 1) → WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) D
def ExpDeInv : Prop :=
  ∀ (K : Type u) [NormedField K] [CharZero K] (l d : ℕ) [NeZero d], l.Prime → 2 ≤ d → Even d →
    ∀ (K0 : Subfield K) (ζ : K), IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, (∀ n, MvPowerSeries.coeff n be ∈ K0) →
      MvPowerSeries.subst (torus l ζ) be = be → MvPowerSeries.constantCoeff be = 0 →
      ∀ D ∈ ({de1 be, de2 be} : Set (MvPowerSeries (V2 d) K)),
        (∀ n, MvPowerSeries.coeff n (mvExp D) ∈ K0) ∧
        ∀ n : V2 d →₀ ℕ, MvPowerSeries.coeff n (mvExp D) ≠ 0 →
          ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2
def Quant : Prop :=
  ∀ (K : Type u) [NormedField K] (l d : ℕ) [NeZero d], l.Prime → 2 ≤ d → Even d →
    ‖(l : K)‖ < 1 → 0 < ‖(l : K)‖ → ∀ (K0 : Subfield K), Unram l K0 →
    ∀ (c : K), c ∈ K0 → ∀ n : V2 d →₀ ℕ,
      ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2 →
      MonoWtGe ‖(l : K)‖ (fun _ => rho l) (rho l) n c →
      MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n c
def BinomExtract : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d],
    l.Prime → Odd l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 →
    ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) → ∀ be : MvPowerSeries (ZMod d) K,
      MvPowerSeries.subst (torus l ζ) be = be → NoLowBidegree be →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (de1 be) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (de2 be) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be ∧
      ∀ n, ¬ IsBiPower l n →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n (MvPowerSeries.coeff n be)
end Formalism.DworkPowerSeriesWeights


