-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
-- name    : GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:53.289804+00:00
-- url     : https://prove2.me/theorems/b5fb8a86-f737-499c-8280-7ceafd8eff59
-- title:
--   Statements End
-- statement:
--   Definitions and structural lemmas for Statements End, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/StatementsEnd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset Filter Topology
variable (d : IndexData)
abbrev Emb := Fin d.f × Bool
def conjEmb (e : Emb d) : Emb d := (e.1, !e.2)
def conjPerm : Equiv.Perm (Emb d) where
  toFun := conjEmb d
  invFun := conjEmb d
  left_inv e := by simp [conjEmb]
  right_inv e := by simp [conjEmb]
def rankLie (e : Emb d) : ℕ := if e.2 then d.N - d.j else d.j
def liePowerSum (m : ℕ) (e : Emb d) : XPoly d :=
  if e.2 then ∑ i ∈ univ.filter (fun i : Fin d.N => d.j ≤ i.val), (-X (e.1, i)) ^ m
  else lowerPowerSum d m e.1
def IsFrobLike (φ : Equiv.Perm (Emb d)) : Prop :=
  (∀ e, φ (conjEmb d e) = conjEmb d (φ e)) ∧
    ((∀ τ, (φ (τ, false)).2 = false) ∨ ∀ τ, (φ (τ, false)).2 = true)
def IsSplitFrob (φ : Equiv.Perm (Emb d)) : Prop := ∀ τ, (φ (τ, false)).2 = false
def IsInertFrob (φ : Equiv.Perm (Emb d)) : Prop := ∀ τ, (φ (τ, false)).2 = true
def kaP (p : ℕ) (φ : Equiv.Perm (Emb d)) (τ : Fin d.f) : ℝ :=
  ∑' n : ℕ, ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ)
def IsHomDecomp (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d) : Prop :=
  F.IsHomogeneous (d.D + 1) ∧
    (∀ k ∈ Icc 1 d.N, ∀ τ : Fin d.f, (Q k τ).IsHomogeneous (d.D + 1 - k)) ∧
      RestTerms.IsPowerSumDecomposition d.f d.N F Q
def restSeries (p : ℕ) (φ : Equiv.Perm (Emb d)) (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f)
    (k n : ℕ) : ℝ :=
  ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
    (((k : ℚ) * intFl d (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * Q k τ) : ℚ) : ℝ)
def rest₂ (vol : ℝ) (p : ℕ) (φ : Equiv.Perm (Emb d)) (Q : ℕ → Fin d.f → XPoly d) : ℝ :=
  Real.log p * vol * ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n
def shSum (F : XPoly d) : ℚ := ∑ τ : Fin d.f, shiftFl d τ F
def totSum (F : XPoly d) : ℚ := ∑ τ : Fin d.f, totalFl d τ F
def shLin (τ : Fin d.f) : XPoly d →ₗ[ℚ] ℚ where
  toFun := shiftFl d τ
  map_add' F G := by simp [shiftFl, Finset.sum_add_distrib]
  map_smul' c F := by simp [shiftFl, ← Finset.smul_sum]
def totLin (τ : Fin d.f) : XPoly d →ₗ[ℚ] ℚ where
  toFun := totalFl d τ
  map_add' F G := by simp [totalFl, Finset.sum_add_distrib]
  map_smul' c F := by simp [totalFl, ← Finset.smul_sum]
abbrev topSpace : Submodule ℚ (XPoly d) := homogeneousSubmodule (Idx d) ℚ (d.D + 1)
def shOn (τ : Fin d.f) : topSpace d →ₗ[ℚ] ℚ := (shLin d τ).comp (topSpace d).subtype
def totOn (τ : Fin d.f) : topSpace d →ₗ[ℚ] ℚ := (totLin d τ).comp (topSpace d).subtype
def uR (u : Idx d → ℚ) : Weight d := fun p => (u p : ℝ)
def ubar (u : Weight d) (τ : Fin d.f) : ℝ := (1 / (d.N : ℝ)) * ∑ i : Fin d.N, u (τ, i)
def cTau (u : Weight d) (τ : Fin d.f) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i) - (d.j : ℝ) * ubar d u τ
theorem finN_nonempty : (univ : Finset (Fin d.N)).Nonempty :=
  ⟨⟨0, by have := d.two_le_N; omega⟩, mem_univ _⟩
def spread (u : Weight d) (τ : Fin d.f) : ℝ :=
  univ.sup' (finN_nonempty d) (fun i => u (τ, i)) - univ.inf' (finN_nonempty d) (fun i => u (τ, i))
def jPrime : ℕ := min d.j (d.N - d.j)
def InSmallBlock (i : Fin d.N) : Prop := if d.j ≤ d.N - d.j then i.val < d.j else d.j ≤ i.val
def TheoremHyp (u : Weight d) (g : ℝ) : Prop :=
  IsRegular d u ∧ 0 < g ∧ (∀ τ, g ≤ gap d τ u) ∧
    ∀ (τ : Fin d.f) (i l : Fin d.N), InSmallBlock d i → l ≠ i → g ≤ |u (τ, i) - u (τ, l)|
def bZero (u : Weight d) (g : ℝ) : ℝ := 4 * d.f * (d.N : ℝ) ^ 2 * (1 + ‖u‖ / g)
def lineF (u : Idx d → ℚ) : XPoly d := lineClass d u ^ (d.D + 1)
structure EndSystem where

  vol : ℝ
  vol_pos : 0 < vol

  level : ℕ
  level_pos : 0 < level
  two_dvd_level : 2 ∣ level

  f_pos : 0 < d.f

  frob : ℕ → Equiv.Perm (Emb d)
  frob_like : ∀ p : ℕ, p.Prime → ¬ p ∣ level → IsFrobLike d (frob p)

  PP : ℕ → XPoly d →ₗ[ℚ] ℝ

  hh : XPoly d →ₗ[ℚ] ℝ

  delta : ℕ → XPoly d →ₗ[ℚ] ℝ

  al : ℕ → Fin d.f → ℝ

  be : ℕ → Fin d.f → ℝ

  alC : ℕ → ℝ

  beC : ℕ → ℝ

  EE : ℕ → XPoly d →ₗ[ℚ] ℝ

  hB : ℕ → ℝ

  rd : ℝ
  one_le_rd : 1 ≤ rd

  lval : ℝ

  Mbar : ℕ → (Idx d → ℚ) → ℚ → ℝ

  Ptwo : ℕ → MvPolynomial (Option (Idx d)) ℝ

  shiftW : Idx d → ℚ
variable {d}
def primesIn (S : EndSystem d) (B0 B : ℕ) : Finset ℕ :=
  (Ioc B0 B).filter (fun p => p.Prime ∧ ¬ p ∣ S.level)
def primesAbove (S : EndSystem d) (B0 : ℕ) : Set ℕ := {p | p.Prime ∧ ¬ p ∣ S.level ∧ B0 < p}
def tau0 (S : EndSystem d) : Fin d.f := ⟨0, S.f_pos⟩
def kaNum (S : EndSystem d) (p : ℕ) : ℝ := kaP d p (S.frob p) (tau0 S)
def aB (S : EndSystem d) (B0 B : ℕ) : ℝ :=
  S.alC B - S.beC B + ∑ p ∈ primesIn S B0 B, Real.log p / ((p : ℝ) - 1)
def bB (S : EndSystem d) (B0 B : ℕ) : ℝ :=
  S.beC B - (1 / (d.N : ℝ)) * ∑ p ∈ primesIn S B0 B, kaNum S p * Real.log p
def restTot (S : EndSystem d) (B0 : ℕ) (Q : ℕ → Fin d.f → XPoly d) : ℝ :=
  ∑' p : primesAbove S B0, rest₂ d S.vol p (S.frob p) Q
def bigP (S : EndSystem d) (B : ℕ) (u : Idx d → ℚ) : ℝ := S.PP B (lineF d u)
def Eq81 (S : EndSystem d) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ S.level → ∀ (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d),
    IsHomDecomp d F Q →
      S.delta p F = -(Real.log p / ((p : ℝ) - 1)) * S.vol * (shSum d F : ℝ) +
        kaNum S p * Real.log p / (d.N : ℝ) * S.vol * (totSum d F : ℝ) + rest₂ d S.vol p (S.frob p) Q
def Prop6Additivity (S : EndSystem d) : Prop :=
  ∀ B0 B : ℕ, B0 < B → ∀ F : XPoly d, F.IsHomogeneous (d.D + 1) →
    S.PP B0 F = S.PP B F + ∑ p ∈ primesIn S B0 B, S.delta p F
def PropA (S : EndSystem d) : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ τ : Fin d.f,
    |S.al B τ - S.alC B| ≤ C * Real.log B / B ∧ |S.be B τ - S.beC B| ≤ C * Real.log B / B
def CorBPrime (S : EndSystem d) : Prop :=
  ∃ (B1 : ℕ) (C : ℝ), ∀ B : ℕ, B1 ≤ B →
    (∀ F : XPoly d, F.IsHomogeneous (d.D + 1) →
      S.PP B F = S.vol * (S.hh F - ∑ τ : Fin d.f, (S.al B τ - S.be B τ) * (shiftFl d τ F : ℝ) -
        ∑ τ : Fin d.f, S.be B τ * (totalFl d τ F : ℝ)) + S.EE B F) ∧
    ∀ m : Idx d →₀ ℕ, (m.sum fun _ e => e) = d.D + 1 →
      |S.EE B (monomial m 1)| ≤ C * Real.log B / B
structure HeightIdentityInputs (S : EndSystem d) : Prop where
  eq81 : Eq81 S
  additivity : Prop6Additivity S
  propA : PropA S
  corB : CorBPrime S
def FlagHeightVanishesAtWalls (S : EndSystem d) : Prop :=
  ∀ u : Idx d → ℚ, IsDominant d (uR d u) →
    0 ≤ S.hh (lineF d u) ∧ ((∃ τ, gap d τ (uR d u) = 0) → S.hh (lineF d u) = 0)
def FlagHeightZeroAtOne.Input (S : EndSystem d) : Prop :=
  ∀ (τ : Fin d.f) (Q : XPoly d), Q.IsHomogeneous d.D →
    S.hh (RestTerms.blockPowerSum d.f d.N 1 τ * Q) = 0
def InputPropF (S : EndSystem d) (B : ℕ) : Prop :=
  (∀ (τ : Fin d.f) (Q : XPoly d), Q.IsHomogeneous d.D →
    S.PP B (RestTerms.blockPowerSum d.f d.N 1 τ * Q) = S.hB B * S.vol * (intFl d Q : ℝ)) ∧
  |S.hB B| ≤ 4 * (d.N : ℝ) * (Real.log (B * S.rd) + |S.lval|)
def LimitLowerBoundInput (S : EndSystem d) (B0 : ℕ) (C7 : ℝ) : Prop :=
  ∀ A0 : ℝ, Tendsto (aB S B0) atTop (𝓝 A0) →
    -Real.log B0 - C7 - ∑ p ∈ S.level.primeFactors.filter (fun p => B0 < p),
        (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤ A0 ∧ A0 ≤ C7
def PrimeSumDecompositionBound (S : EndSystem d) (B0 : ℕ) (u : Idx d → ℚ) : Prop :=
  ∀ Q : ℕ → Fin d.f → XPoly d, IsHomDecomp d (lineF d u) Q →
    Summable (fun p : primesAbove S B0 => |rest₂ d S.vol p (S.frob p) Q|) ∧
      ∑' p : primesAbove S B0, |rest₂ d S.vol p (S.frob p) Q| ≤
        4 / ((d.f : ℝ) * d.N) * ((d.D : ℝ) + 1) * (S.vol * (degAt d u : ℝ)) * (jPrime d : ℝ) *
          ∑ τ : Fin d.f, spread d (uR d u) τ
def LimitPolynomialHypothesis (S : EndSystem d) (B : ℕ) : Prop :=
  ∀ lam : Idx d → ℚ,
    eval (fun o : Option (Idx d) => o.elim (0 : ℝ) (fun p => (lam p : ℝ))) (S.Ptwo B) = S.PP B (lineF d lam)
def UniformSmallShiftDominance (S : EndSystem d) (B : ℕ) (u : Idx d → ℚ) : Prop :=
  ∃ C3 s0 : ℝ, 0 < s0 ∧ ∀ s : ℚ, 0 < s → (s : ℝ) ≤ s0 → IsDominant d (uR d (u - s • S.shiftW)) →
    |S.Mbar B u s - eval (fun o : Option (Idx d) =>
      o.elim (s : ℝ) (fun p => ((u - s • S.shiftW) p : ℝ))) (S.Ptwo B)| ≤ C3 * s
def KaPSplit.Statement : Prop :=
  ∀ (d : IndexData) (p : ℕ) (φ : Equiv.Perm (Emb d)), p.Prime → IsFrobLike d φ → IsSplitFrob d φ →
    ∀ τ : Fin d.f, kaP d p φ τ = (d.j : ℝ) / ((p : ℝ) - 1)
def KaPInert.Statement : Prop :=
  ∀ (d : IndexData) (p : ℕ) (φ : Equiv.Perm (Emb d)), p.Prime → IsFrobLike d φ → IsInertFrob d φ →
    ∀ τ : Fin d.f, kaP d p φ τ = (((d.N - d.j : ℕ) : ℝ) * p + d.j) / ((p : ℝ) ^ 2 - 1)
def KaPBound.Statement : Prop :=
  ∀ (d : IndexData) (p : ℕ) (φ : Equiv.Perm (Emb d)), p.Prime → IsFrobLike d φ →
    ∀ τ : Fin d.f, 0 < kaP d p φ τ ∧ kaP d p φ τ ≤ (d.N : ℝ) / ((p : ℝ) - 1)
def RestPWellDefined.Statement : Prop :=
  ∀ (d : IndexData) (vol : ℝ) (p : ℕ) (φ : Equiv.Perm (Emb d)) (F : XPoly d)
    (Q Q' : ℕ → Fin d.f → XPoly d),
    RestTerms.IsPowerSumDecomposition d.f d.N F Q → RestTerms.IsPowerSumDecomposition d.f d.N F Q' →
      rest₂ d vol p φ Q = rest₂ d vol p φ Q'
def RestPBound.Statement : Prop :=
  ∀ (d : IndexData) (vol : ℝ) (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d),
    RestTerms.IsPowerSumDecomposition d.f d.N F Q →
    ∃ c : ℝ, ∀ (p : ℕ) (φ : Equiv.Perm (Emb d)), p.Prime →
      (∀ τ : Fin d.f, ∀ k ∈ Icc 2 d.N, Summable (restSeries d p φ Q τ k)) ∧
        |rest₂ d vol p φ Q| ≤ c * Real.log p / (p : ℝ) ^ 2
def RestSummable.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d) (B0 : ℕ) (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d),
    RestTerms.IsPowerSumDecomposition d.f d.N F Q →
      Summable (fun p : primesAbove S B0 => |rest₂ d S.vol p (S.frob p) Q|)
def HeightSumIdentity.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d), HeightIdentityInputs S → ∀ B0 : ℕ, ∃ B1 : ℕ,
    ∀ (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d), IsHomDecomp d F Q →
      ∃ C : ℝ, ∀ B : ℕ, B0 < B → B1 ≤ B →
        |S.PP B0 F - (S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) - bB S B0 B * (totSum d F : ℝ)) +
          ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q)| ≤ C * Real.log B / B
def ShTotIndependent.Statement : Prop :=
  ∀ d : IndexData, 0 < d.f →
    LinearIndependent ℚ (Sum.elim (shOn d) (totOn d)) ∧
      LinearIndependent ℚ ![∑ τ : Fin d.f, shOn d τ, ∑ τ : Fin d.f, totOn d τ]
def ShTotInvertiblePair.Statement : Prop :=
  ∀ d : IndexData, 0 < d.f →
    ∃ F1 F2 : XPoly d, F1.IsHomogeneous (d.D + 1) ∧ F2.IsHomogeneous (d.D + 1) ∧
      shSum d F1 * totSum d F2 - totSum d F1 * shSum d F2 ≠ 0
def LimitsExist.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d), HeightIdentityInputs S → ∀ B0 : ℕ,
    ∃ A0 b0 : ℝ, Tendsto (aB S B0) atTop (𝓝 A0) ∧ Tendsto (bB S B0) atTop (𝓝 b0)
def HeightTauIdentity.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d), HeightIdentityInputs S → ∀ (B0 : ℕ) (A0 b0 : ℝ),
    Tendsto (aB S B0) atTop (𝓝 A0) → Tendsto (bB S B0) atTop (𝓝 b0) →
    ∀ (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d), IsHomDecomp d F Q →
      S.PP B0 F = S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) + restTot S B0 Q
def HeightEvaluation.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d), HeightIdentityInputs S → ∀ (B0 : ℕ) (A0 b0 : ℝ),
    Tendsto (aB S B0) atTop (𝓝 A0) → Tendsto (bB S B0) atTop (𝓝 b0) →
    ∀ (u : Idx d → ℚ) (Q : ℕ → Fin d.f → XPoly d), IsHomDecomp d (lineF d u) Q →
      bigP S B0 u = S.vol * S.hh (lineF d u) + ((d.D : ℝ) + 1) * (S.vol * (degAt d u : ℝ)) *
          ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
            (d.N : ℝ) * b0 * ubar d (uR d u) τ) + restTot S B0 Q ∧
      bigP S B0 u = S.vol * S.hh (lineF d u) + ((d.D : ℝ) + 1) * (S.vol * (degAt d u : ℝ)) *
          ∑ τ : Fin d.f, (A0 * cTau d (uR d u) τ + ((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ) +
            restTot S B0 Q
def CBounds.Statement : Prop :=
  ∀ (d : IndexData) (u : Weight d), IsDominant d u → ∀ τ : Fin d.f,
    0 ≤ cTau d u τ ∧ cTau d u τ ≤ ∑ i : Fin d.N, |u (τ, i)|
def NormUbar.Statement : Prop :=
  ∀ (d : IndexData) (u : Weight d) (τ : Fin d.f), (d.N : ℝ) * |ubar d u τ| ≤ ∑ i : Fin d.N, |u (τ, i)|
def TermA.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d), FlagHeightVanishesAtWalls S → ∀ u : Idx d → ℚ, IsDominant d (uR d u) →
    0 ≤ S.vol * S.hh (lineF d u)
def TermB.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d) (u : Idx d → ℚ) (g : ℝ) (B0 : ℕ),
    TheoremHyp d (uR d u) g → B0 = ⌊bZero d (uR d u) g⌋₊ → PrimeSumDecompositionBound S B0 u →
    ∀ Q : ℕ → Fin d.f → XPoly d, IsHomDecomp d (lineF d u) Q →
      |restTot S B0 Q| ≤ 4 / ((d.f : ℝ) * d.N) * ((d.D : ℝ) + 1) * (S.vol * (degAt d u : ℝ)) *
        (jPrime d : ℝ) * ∑ τ : Fin d.f, spread d (uR d u) τ
def TermC.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d), HeightIdentityInputs S → FlagHeightZeroAtOne.Input S →
    ∀ (B0 : ℕ) (A0 b0 : ℝ), Tendsto (aB S B0) atTop (𝓝 A0) → Tendsto (bB S B0) atTop (𝓝 b0) →
      InputPropF S B0 →
        |(d.j : ℝ) * A0 + (d.N : ℝ) * b0| ≤ 4 * (d.N : ℝ) * (Real.log (B0 * S.rd) + |S.lval|)
def TermD.Statement : Prop :=
  ∀ C7 : ℝ, 0 ≤ C7 → ∃ C : ℝ, ∀ (d : IndexData) (S : EndSystem d) (B0 : ℕ) (A0 : ℝ),
    2 ≤ B0 → LimitLowerBoundInput S B0 C7 → Tendsto (aB S B0) atTop (𝓝 A0) →
      -C * Real.log B0 - C * ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) ≤ A0
def TheoremTUpper.Statement : Prop :=
  ∀ C7 : ℝ, 0 ≤ C7 → ∃ C : ℝ, ∀ (d : IndexData) (S : EndSystem d) (u : Idx d → ℚ) (g : ℝ) (B0 : ℕ),
    TheoremHyp d (uR d u) g → B0 = ⌊bZero d (uR d u) g⌋₊ →
    (S.level.primeFactors.card : ℝ) ≤ bZero d (uR d u) g →
    HeightIdentityInputs S → FlagHeightVanishesAtWalls S → FlagHeightZeroAtOne.Input S → InputPropF S B0 → LimitLowerBoundInput S B0 C7 →
    PrimeSumDecompositionBound S B0 u →
      -C * ((d.D : ℝ) + 1) * (S.vol * (degAt d u : ℝ)) *
          ((Real.log (bZero d (uR d u) g * S.rd) + |S.lval|) * ∑ p : Idx d, |(u p : ℝ)| +
            (jPrime d : ℝ) * ∑ τ : Fin d.f, spread d (uR d u) τ) ≤ bigP S B0 u
def NefAtBaseHeight.Statement : Prop :=
  ∀ d : IndexData, 0 < d.f → ∀ (u u'' : Weight d) (g C7 s : ℝ), 0 < g → 0 ≤ s →
    4 * d.f * (d.N : ℝ) ^ 2 * ‖u‖ + g ≤ (bZero d u g - 2) * g ∧
      (‖u''‖ ≤ ‖u‖ + C7 * s / 2 → (∀ τ, g - C7 * s ≤ gap d τ u'') →
        (bZero d u g - 2) * C7 * s + 2 * d.f * C7 * s ≤ g + 4 * d.f * ((d.N : ℝ) ^ 2 - 1) * ‖u‖ →
          ∀ τ, 4 * d.f * ‖u''‖ ≤ (bZero d u g - 2) * gap d τ u'')
def LimitTheorem.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Pt : MvPolynomial (Option σ) ℝ) (u w : σ → ℝ) (M : ℚ → ℝ) (C3 s0 : ℝ),
    0 < s0 →
    (∀ s : ℚ, 0 < s → (s : ℝ) ≤ s0 →
      |M s - eval (fun o : Option σ => o.elim (s : ℝ) (fun p => u p - s * w p)) Pt| ≤ C3 * s) →
    Tendsto M (𝓝[>] (0 : ℚ)) (𝓝 (eval (fun o : Option σ => o.elim (0 : ℝ) u) Pt))
def TheoremTLower.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d) (u : Idx d → ℚ) (g : ℝ) (B0 : ℕ),
    TheoremHyp d (uR d u) g → B0 = ⌊bZero d (uR d u) g⌋₊ → LimitPolynomialHypothesis S B0 → UniformSmallShiftDominance S B0 u →
      Tendsto (S.Mbar B0 u) (𝓝[>] (0 : ℚ)) (𝓝 (bigP S B0 u))
def HeightLimitIdentity.Statement : Prop :=
  ∀ (d : IndexData) (S : EndSystem d), HeightIdentityInputs S → FlagHeightZeroAtOne.Input S →
    ∀ (B0 : ℕ) (A0 b0 : ℝ), Tendsto (aB S B0) atTop (𝓝 A0) → Tendsto (bB S B0) atTop (𝓝 b0) →
    ∀ (τ : Fin d.f) (Q : XPoly d), Q.IsHomogeneous d.D → intFl d Q = 1 →
      (d.j : ℝ) * A0 + (d.N : ℝ) * b0 = -S.PP B0 (RestTerms.blockPowerSum d.f d.N 1 τ * Q) / S.vol
def uSample : Idx d1 → ℚ := fun p => if p.2.val = 0 then 1 else 0
end GroundTheory.Heights₂.Heights.TheoremB


