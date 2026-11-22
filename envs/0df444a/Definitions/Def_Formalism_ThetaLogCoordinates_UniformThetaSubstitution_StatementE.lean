-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:12.188926+00:00
-- url     : https://prove2.me/theorems/b9c512e5-cf55-4ec6-960b-d5e21ad6f1b8
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementE.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
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
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
def HitsCapPos : Prop :=
  ∀ (K σ κ : Type) [Field K] [DecidableEq σ] [Fintype κ] (r0 r1 C : ℕ) (l : Fin C → ℕ)
    (sf : Fin C → σ) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1) (pos : κ → σ)
    (ξ : κ → Fin r0 → K) (col : κ → Fin r1) (S : Finset κ) (s₀ : σ),
    (∀ k ∈ S, pos k = s₀) → (∀ k ∈ S, ∀ k' ∈ S, ξ k = ξ k') →
    ∀ β : κ →₀ ℕ, (univ.filter (fun c => sf c = s₀)).card < ∑ k ∈ S, β k →
      hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (∏ c, minorAt (sf c) (T c) (I c)) = 0
def HitsColumnsPos : Prop :=
  ∀ (K σ κ : Type) [Field K] [DecidableEq σ] [Fintype κ] (r0 r1 C : ℕ) (l : Fin C → ℕ)
    (sf : Fin C → σ) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1) (pos : κ → σ)
    (ξ : κ → Fin r0 → K) (col : κ → Fin r1) (S : Finset κ) (s₀ : σ) (J : Finset (Fin r1)),
    (∀ k ∈ S, pos k = s₀) → (∀ k ∈ S, col k ∈ J) →
    ∀ β : κ →₀ ℕ,
      ∑ c ∈ univ.filter (fun c => sf c = s₀), ((univ.image (I c)) ∩ J).card < ∑ k ∈ S, β k →
      hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (∏ c, minorAt (sf c) (T c) (I c)) = 0
def HasseDegree : Prop :=
  ∀ (K ι κ : Type) [Field K] [Fintype κ] (b : κ → ι → K) (β : κ →₀ ℕ) (Q : MvPolynomial ι K),
    ∀ n ∈ (hasseDir b β Q).support, ∃ n0 ∈ Q.support, n ≤ n0 ∧ n.degree + ∑ k, β k = n0.degree
def MinorProdDegree : Prop :=
  ∀ (K σ : Type) [Field K] [DecidableEq σ] (r0 r1 C : ℕ) (l : Fin C → ℕ) (sf : Fin C → σ)
    (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
    ∀ n ∈ (∏ c, minorAt (sf c) (T c) (I c)).support, ∀ s : σ,
      ∑ x : Fin r0 × Fin r1, n (s, x) = ∑ c ∈ univ.filter (fun c => sf c = s), l c
section TopLow
variable {K Tp Lw : Type} [Field K]
def lowPoly (Q : MvPolynomial Lw K) : MvPolynomial (Tp ⊕ Lw) K := MvPolynomial.rename Sum.inr Q
def topMonoP (e : Tp →₀ ℕ) : MvPolynomial (Tp ⊕ Lw) K :=
  MvPolynomial.monomial (e.mapDomain Sum.inl) 1
def topMonoS (d : Tp →₀ ℕ) : MvPowerSeries (Tp ⊕ Lw) K :=
  MvPowerSeries.monomial (d.mapDomain Sum.inl) 1
def lowLin [Fintype Lw] (b : Lw → K) : MvPowerSeries (Tp ⊕ Lw) K :=
  ∑ x, MvPowerSeries.C (b x) * MvPowerSeries.X (Sum.inr x)
def lowDeg [Fintype Lw] (n : Tp ⊕ Lw →₀ ℕ) : ℕ := ∑ x : Lw, n (Sum.inr x)
end TopLow
def TermBound : Prop :=
  ∀ (K Tp Lw Φ κ : Type) [NormedField K] [IsUltrametricDist K] [Fintype Tp] [Fintype Lw]
    [Fintype Φ] [Fintype κ] [DecidableEq Tp] [DecidableEq Lw] (p D dQ : ℕ)
    (h g Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ) (aB : κ → K)
    (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) (e : Tp →₀ ℕ) (Q : MvPolynomial Lw K),
    p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ → MvPowerSeries.constantCoeff h = 0 → InClass (p : K) h g →
    (∀ φ, ‖aA φ‖ ≤ 1) → (∀ k, ‖aB k‖ ≤ 1) → (∀ k x, ‖b k x‖ ≤ 1) → Integral Z → Integral Y →
    (∀ n, MvPowerSeries.coeff n Z ≠ 0 → p ≤ lowDeg n) →
    (∀ n : Tp ⊕ Lw →₀ ℕ, n.degree ≤ D → MvPowerSeries.coeff n h = MvPowerSeries.coeff n
      (∑ φ, MvPowerSeries.C (aA φ) * topMonoS (Lw := Lw) (dA φ) +
        ∑ k, MvPowerSeries.C (aB k) * topMonoS (dB k) * lowLin (b k) + Z +
        MvPowerSeries.C (p : K) * Y)) →
    (∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1) → Q.IsHomogeneous dQ → e.degree + dQ = D →
    jetPair (topMonoP e * lowPoly Q) g = 0 ∨
    ∃ (α : Φ → ℕ) (β : κ →₀ ℕ) (i2 : ℕ) (n : Lw →₀ ℕ), n ∈ (hasseDir b β Q).support ∧
      (∀ φ, α φ ≠ 0 → aA φ ≠ 0) ∧ (∀ k, β k ≠ 0 → aB k ≠ 0) ∧
      (∀ τ, ∑ φ, α φ * dA φ τ + ∑ k, β k * dB k τ ≤ e τ) ∧ p * i2 ≤ n.degree ∧
      ‖jetPair (topMonoP e * lowPoly Q) g‖ ≤
        (p : ℝ) ^ (∑ φ, α φ + ∑ k, β k + i2) * ‖((mfact e : ℕ) : K)‖ *
          ‖(((∑ k, β k).factorial : ℕ) : K)‖ * ‖((mfact n : ℕ) : K)‖
section Decomp
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
abbrev TpV (ν r1 : ℕ) : Type := ZMod (2 * ν) × Fin r1
def zSub (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (x : ZV ν r0 r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  MvPowerSeries.X (Sum.inr x) +
    if x.1 ∈ TT then MvPowerSeries.C (ξ x.1 x.2.1) * MvPowerSeries.X (Sum.inl (x.1, x.2.2)) else 0
abbrev PhiI (ν r0 r1 E : ℕ) : Type := ZMod (2 * ν) × Fin E × Fin E × Fin r0 × Fin r1
def pairFirst {E : ℕ} (φ : PhiI ν r0 r1 E) : ZMod (2 * ν) := φ.1 - 2 * (φ.2.1.val : ZMod (2 * ν))
def pairSecond {E : ℕ} (φ : PhiI ν r0 r1 E) : ZMod (2 * ν) := φ.1 + 1 - 2 * (φ.2.2.1.val : ZMod (2 * ν))
def aAof {E : ℕ} (p : ℕ) (u : ZMod (2 * ν) → K) (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (φ : PhiI ν r0 r1 E) : K :=
  if pairFirst φ ∈ TT ∧ pairSecond φ ∈ TT then
    u φ.1 * (-1) ^ (φ.2.1.val + φ.2.2.1.val) * ξ (pairFirst φ) φ.2.2.2.1 ^ (p ^ (1 + 2 * φ.2.1.val)) *
      ξ (pairSecond φ) φ.2.2.2.1 ^ (p ^ (2 * φ.2.2.1.val))
  else 0
def dAof {E : ℕ} (p : ℕ) (φ : PhiI ν r0 r1 E) : TpV ν r1 →₀ ℕ :=
  Finsupp.single (pairFirst φ, φ.2.2.2.2) (p ^ (1 + 2 * φ.2.1.val)) +
    Finsupp.single (pairSecond φ, φ.2.2.2.2) (p ^ (2 * φ.2.2.1.val))
abbrev KapI (ν r1 E : ℕ) : Type := ZMod (2 * ν) × Fin E × Fin r1
def aBof {E : ℕ} (u : ZMod (2 * ν) → K) (TT : Finset (ZMod (2 * ν))) (k : KapI ν r1 E) : K :=
  if k.1 ∈ TT then u (k.1 + 2 * (k.2.1.val : ZMod (2 * ν))) * (-1) ^ k.2.1.val else 0
def dBof {E : ℕ} (p : ℕ) (k : KapI ν r1 E) : TpV ν r1 →₀ ℕ :=
  Finsupp.single (k.1, k.2.2) (p ^ (2 * k.2.1.val + 1))
def bBof {E : ℕ} (p : ℕ) (ξ : ZMod (2 * ν) → Fin r0 → K) (k : KapI ν r1 E) : ZV ν r0 r1 → K :=
  colDir (k.1 + ((2 * k.2.1.val + 1 : ℕ) : ZMod (2 * ν))) (fun a => ξ k.1 a ^ (p ^ (2 * k.2.1.val + 1)))
    k.2.2
end Decomp
def HhDecomp : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p ν r0 r1 E D : ℕ) [NeZero ν]
    (u : ZMod (2 * ν) → K) (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K),
    p.Prime → 2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ s, ‖u s‖ ≤ 1) → (∀ s a, ‖ξ s a‖ ≤ 1) →
    D < p ^ (2 * E) →
    ∃ Z Y : MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K, Integral Z ∧ Integral Y ∧
      (∀ n, MvPowerSeries.coeff n Z ≠ 0 → p ≤ lowDeg n) ∧
      ∀ n : TpV ν r1 ⊕ ZV ν r0 r1 →₀ ℕ, n.degree ≤ D →
        MvPowerSeries.coeff n (MvPowerSeries.subst (zSub TT ξ) (hhS (r0 := r0) (r1 := r1) p u)) =
          MvPowerSeries.coeff n
            (∑ φ : PhiI ν r0 r1 E,
                MvPowerSeries.C (aAof p u TT ξ φ) * topMonoS (Lw := ZV ν r0 r1) (dAof p φ) +
              ∑ k : KapI ν r1 E,
                MvPowerSeries.C (aBof u TT k) * topMonoS (dBof p k) * lowLin (bBof p ξ k) + Z +
              MvPowerSeries.C (p : K) * Y)
section Entry
variable {K : Type} [Field K] {ν r0 r1 C : ℕ}
def topForm (ξ : ZMod (2 * ν) → Fin r0 → K) (x : TpV ν r1) : MvPolynomial (ZV ν r0 r1) K :=
  ∑ a, MvPolynomial.C (ξ x.1 a) * MvPolynomial.X (x.1, a, x.2)
def lowOp (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
    (I : ∀ c, Fin (l c) → Fin r1) : MvPolynomial (ZV ν r0 r1) K :=
  ∏ c, minorAt (sf c) (T c) (I c)
def entryOp [NeZero ν] (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1) :
    MvPolynomial (ZV ν r0 r1) K :=
  (∏ x, topForm ξ x ^ e x) * lowOp l sf T I
def alN (e : TpV ν r1 → ℕ) (s : ZMod (2 * ν)) : ℕ := ∑ b, e (s, b)
def capN (sf : Fin C → ZMod (2 * ν)) (s : ZMod (2 * ν)) : ℕ := (univ.filter (fun c => sf c = s)).card
def lsN (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (s : ZMod (2 * ν)) : ℕ :=
  ∑ c ∈ univ.filter (fun c => sf c = s), l c
def dSet (TT : Finset (ZMod (2 * ν))) (s : ZMod (2 * ν)) : Finset ℕ :=
  (TT.filter (fun s' => s'.val % 2 ≠ s.val % 2)).image (fun s' => (s' - s).val)
def oddT (TT : Finset (ZMod (2 * ν))) : Finset (ZMod (2 * ν)) := TT.filter (fun s => s.val % 2 = 1)
end Entry
def EntryHyp {K : Type} [NormedField K] (p ν r0 r1 C : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K)
    (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (T : ∀ c, Fin (l c) → Fin r0 → K) : Prop :=
  p.Prime ∧ 2 < p ∧ ‖(p : K)‖ = (p : ℝ)⁻¹ ∧ (∀ s, ‖u s‖ ≤ 1) ∧ InClass (p : K) (hhS p u) F ∧
    (∀ s a, ‖ξ s a‖ ≤ 1) ∧ (∀ c i a, ‖T c i a‖ ≤ 1) ∧ ∀ x : TpV ν r1, x.1 ∉ TT → e x = 0
def EntryStar : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p ν r0 r1 C : ℕ) [NeZero ν]
    (u : ZMod (2 * ν) → K) (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
    (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
    EntryHyp p ν r0 r1 C u F TT ξ e l T →
    jetPair (entryOp ξ e l sf T I) F = 0 ∨
    ∃ (E : ℕ) (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ),
      (∀ φ, α φ ≠ 0 → pairFirst φ ∈ TT ∧ pairSecond φ ∈ TT) ∧ (∀ k, β k ≠ 0 → k.1 ∈ TT) ∧
      (∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ) ∧
      hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0 ∧
      ‖jetPair (entryOp ξ e l sf T I) F‖ ≤ (p : ℝ) ^ (-(gamP p * ∑ s ∈ TT, (alN e s : ℝ) -
        (∑ φ, (α φ : ℝ)) - (∑ k, (β k : ℝ)) - deLoss p r0 r1 TT (alN e) (lsN l sf) +
        rhoP p * ∑ s, ((alN e s : ℝ) + lsN l sf s)))
def EntryExcessBound : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p ν r0 r1 C : ℕ) [NeZero ν]
    (u : ZMod (2 * ν) → K) (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
    (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
    EntryHyp p ν r0 r1 C u F TT ξ e l T →
    ‖jetPair (entryOp ξ e l sf T I) F‖ ≤ (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT)
        (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ)) (deLoss p r0 r1 TT (alN e) (lsN l sf)) +
      rhoP p * ∑ s, ((alN e s : ℝ) + lsN l sf s)))
def EntryCappedBound : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p ν r0 r1 C : ℕ) [NeZero ν]
    (u : ZMod (2 * ν) → K) (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
    (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
    EntryHyp p ν r0 r1 C u F TT ξ e l T →
    ‖jetPair (entryOp ξ e l sf T I) F‖ ≤ (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT)
        (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ)) (deLoss p r0 r1 TT (alN e) (lsN l sf)) -
      ∑ s ∈ TT \ oddT TT, (alN e s : ℝ) + rhoP p * ∑ s, ((alN e s : ℝ) + lsN l sf s)))
def EntryB : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p ν r0 r1 C : ℕ) [NeZero ν]
    (u : ZMod (2 * ν) → K) (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
    (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1) (J : Finset (Fin r1)),
    EntryHyp p ν r0 r1 C u F TT ξ e l T →
    ‖(p : K) ^ (∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
          then e x else 0) +
        ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I c)) ∩ J).card else 0)) *
      jetPair (entryOp ξ e l sf T I) F‖ ≤ (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT)
        (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ)) (deLoss p r0 r1 TT (alN e) (lsN l sf)) +
      rhoP p * ∑ s, ((alN e s : ℝ) + lsN l sf s)))
end Formalism.InvariantFactorPaths.G7


