-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementE
-- name    : Formalism_PieriBlockIdeals_StatementE
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:57:35.919262+00:00
-- url     : https://prove2.me/theorems/77878372-79ff-4bc7-ad44-454010daf6b0
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementE.lean

import Definitions.Def_Formalism_PieriBlockIdeals_StatementTop
import Definitions.Def_Formalism_PieriBlockIdeals_StatementJoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.CohomologicalDescent.E
open Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
def ExInterval : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ l : ℕ, l.Prime → ∀ (lo : ℤ) (w : ℕ),
    (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
    LA.exZ N N le_rfl (res N lam) l ≤ N.choose 2 * Nat.log l w ∧
      (w ≤ l → LA.exZ N N le_rfl (res N lam) l = 0)
def ExIntervalLt : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ l : ℕ, l.Prime → ∀ (lo : ℤ) (w : ℕ),
    (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
    LA.exZ N N le_rfl (res N lam) l ≤ N.choose 2 * Nat.log l w ∧
      (w < l → LA.exZ N N le_rfl (res N lam) l = 0)
def ExCut : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ l : ℕ, l.Prime → ∀ (lo : ℤ) (w : ℕ),
    (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
    ∀ a : ℕ, a ≤ N →
      LA.exZ N N le_rfl (res N lam) l ≤
        LA.exZ a a le_rfl (res a lam) l +
          LA.exZ (N - a) (N - a) le_rfl (res (N - a) (fun i => lam (a + i))) l +
          a * (N - a) * Nat.log l w
section SF09
open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
def CorollaryOfRecord7E : Prop :=
  ExInterval → ExCut → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def CorollaryOfRecord7ELt : Prop :=
  ExIntervalLt → ExCut → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def CorollaryOfRecord7C : Prop :=
  ExCut → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
end SF09
section Record
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
  Formalism.CohomologicalDescent.LargeParameterEstimates
def JointRecordE : Prop :=
  ExInterval → ExCut → ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ P : Par, P.Hyp → x0 ≤ P.x → P.L = P.x ^ ε →
    Rows P (Real.exp (P.x ^ (ε / 3))) (P.x ^ C) → P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l)) ∧
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
      (DG : ℕ), 0 < DG →
      ∑ w ∈ S, lw w * ((W.Jrec7 P (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b +
            Real.log (DG : ℝ) ∧
      30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b ≤
          32 * P.x ^ ε * ((P.f : ℝ) * (P.m : ℝ) * P.b * P.x ^ ε)) ∧
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
      Hᴴ = H → IsUnit H.det →
      ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
      ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
      ∀ w : HeightOneSpectrum (𝓞 K),
      (∀ z ∈ cutLat E A,
        (((plc w : ℕ) : 𝓞 K) ^ W.Jrec7 P (plc w)) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
        (jw (Eᴴ * H * E) w (matLat Pr A) : ℝ) ≤
          ((W.Jrec7 P (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) * (d : ℝ) +
            (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℝ))
def JointRecordELt : Prop :=
  ExIntervalLt → ExCut → ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ P : Par, P.Hyp → x0 ≤ P.x → P.L = P.x ^ ε →
    Rows P (Real.exp (P.x ^ (ε / 3))) (P.x ^ C) → P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l)) ∧
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
      (DG : ℕ), 0 < DG →
      ∑ w ∈ S, lw w * ((W.Jrec7 P (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b +
            Real.log (DG : ℝ) ∧
      30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b ≤
          32 * P.x ^ ε * ((P.f : ℝ) * (P.m : ℝ) * P.b * P.x ^ ε)) ∧
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
      Hᴴ = H → IsUnit H.det →
      ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
      ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
      ∀ w : HeightOneSpectrum (𝓞 K),
      (∀ z ∈ cutLat E A,
        (((plc w : ℕ) : 𝓞 K) ^ W.Jrec7 P (plc w)) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
        (jw (Eᴴ * H * E) w (matLat Pr A) : ℝ) ≤
          ((W.Jrec7 P (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) * (d : ℝ) +
            (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℝ))
def JointRecordC : Prop :=
  ExCut → ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ P : Par, P.Hyp → x0 ≤ P.x → P.L = P.x ^ ε →
    Rows P (Real.exp (P.x ^ (ε / 3))) (P.x ^ C) → P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l)) ∧
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
      (DG : ℕ), 0 < DG →
      ∑ w ∈ S, lw w * ((W.Jrec7 P (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b +
            Real.log (DG : ℝ) ∧
      30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b ≤
          32 * P.x ^ ε * ((P.f : ℝ) * (P.m : ℝ) * P.b * P.x ^ ε)) ∧
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
      Hᴴ = H → IsUnit H.det →
      ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
      ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
      ∀ w : HeightOneSpectrum (𝓞 K),
      (∀ z ∈ cutLat E A,
        (((plc w : ℕ) : 𝓞 K) ^ W.Jrec7 P (plc w)) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
        (jw (Eᴴ * H * E) w (matLat Pr A) : ℝ) ≤
          ((W.Jrec7 P (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) * (d : ℝ) +
            (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℝ))
end Record
end Formalism.CohomologicalDescent.E


