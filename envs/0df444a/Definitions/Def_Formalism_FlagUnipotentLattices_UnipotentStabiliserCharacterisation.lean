-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
-- name    : Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:41.980108+00:00
-- url     : https://prove2.me/theorems/74e8a869-238c-4acc-983c-dc20f2385f2d
-- title:
--   Unipotent Stabiliser Characterisation
-- statement:
--   Definitions and structural lemmas for Unipotent Stabiliser Characterisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/UnipotentStabiliserCharacterisation.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.ExpansionTerms
section PartA
open Finset Real MeasureTheory NumberField
noncomputable def TruncationCutoff (K L t : ℝ) : ℝ := if t = 0 then 1 else min 1 ((L / t) ^ K)
def CenteredPolydisc {ι : Type} (ro : ℝ) (D : ι → ℂ) : Set (ι → ℂ) := {x | ∀ v, ‖x v - D v‖ < ro / 2}
def IsNormSeparated {ι : Type} [Fintype ι] (ro : ℝ) (S : Finset (ι → ℂ)) : Prop :=
  ∀ D ∈ S, ∀ D' ∈ S, D ≠ D' → ro ^ Fintype.card ι ≤ ∏ v, ‖D v - D' v‖
def SeparatedPolydiscsDisjoint : Prop :=
  ∀ (ι : Type) [Fintype ι] (ro : ℝ) (D D' : ι → ℂ), 0 < ro → D ≠ D' →
    ro ^ Fintype.card ι ≤ ∏ v, ‖D v - D' v‖ → Disjoint (CenteredPolydisc ro D) (CenteredPolydisc ro D')
def IdealNormProductLowerBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), aa ≠ 0 → ∀ x : E, x ∈ aa → x ≠ 0 →
      √(FractionalIdeal.absNorm aa : ℝ) ≤ ∏ w : InfinitePlace E, w x
def AlgebraicIntegerNormGeOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K), x ≠ 0 →
    (1 : ℝ) ≤ ∏ w : InfinitePlace K, w (x : K) ^ w.mult
def InversePowerIntegralPi : Prop :=
  Integrable (fun x : ℂ => ((1 + ‖x‖ ^ 2) ^ 2)⁻¹) ∧ ∫ x : ℂ, ((1 + ‖x‖ ^ 2) ^ 2)⁻¹ = π
def SeparatedSetSumBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (ro : ℝ) (S : Finset (ι → ℂ)), 0 < ro → ro ≤ 1 → IsNormSeparated ro S →
    ∑ D ∈ S, ∏ v, ((1 + ‖D v‖ ^ 2) ^ 2)⁻¹ ≤ (16 / ro ^ 2) ^ Fintype.card ι
def IdealInversePowerSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), aa ≠ 0 → (FractionalIdeal.absNorm aa : ℝ) ≤ 1 →
    ∀ S : Finset E, (∀ D ∈ S, D ∈ aa) →
      ∑ D ∈ S, ∏ w : InfinitePlace E, ((1 + (w D) ^ 2) ^ 2)⁻¹ ≤
        16 ^ Fintype.card (InfinitePlace E) / (FractionalIdeal.absNorm aa : ℝ)
def RingInversePowerSum : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (S : Finset (𝓞 E)),
    ∑ D ∈ S, ∏ w : InfinitePlace E, ((1 + (w (D : E)) ^ 2) ^ 2)⁻¹ ≤ C ^ Fintype.card (InfinitePlace E)
def CutoffIntegralFormula : Prop :=
  ∀ K L : ℝ, 2 < K → 0 < L →
    Integrable (fun x : ℂ => TruncationCutoff K L ‖x‖) ∧ ∫ x : ℂ, TruncationCutoff K L ‖x‖ = π * L ^ 2 * (K / (K - 2))
def SeparatedCutoffSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (ro K : ℝ) (abelian₂ : ι → ℝ) (S : Finset (ι → ℂ)), 0 < ro → 2 < K →
    (∀ v, 0 < abelian₂ v) → IsNormSeparated ro S →
    ∑ sg ∈ S, ∏ v, TruncationCutoff K (abelian₂ v) ‖sg v‖ ≤
      ∏ v, (4 * (3 / 2 : ℝ) ^ K * (K / (K - 2)) * (max ro (abelian₂ v)) ^ 2 / ro ^ 2)
def IdealCutoffSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (K : ℝ) (abelian₂ : InfinitePlace E → ℝ), aa ≠ 0 → 2 < K →
    (∀ w, 0 < abelian₂ w) → ∀ S : Finset E, (∀ sg ∈ S, sg ∈ aa) →
      ∑ sg ∈ S, ∏ w : InfinitePlace E, TruncationCutoff K (abelian₂ w) (w sg) ≤
        (∏ w : InfinitePlace E, (4 * (3 / 2 : ℝ) ^ K * (K / (K - 2)) *
          (max ((FractionalIdeal.absNorm aa : ℝ) ^ (1 / (2 * (Fintype.card (InfinitePlace E) : ℝ)))) (abelian₂ w)) ^ 2)) /
          (FractionalIdeal.absNorm aa : ℝ)
def RingCutoffSumBound : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (abelian₂ : InfinitePlace E → ℝ), (∀ w, 0 < abelian₂ w) → ∀ S : Finset (𝓞 E),
      ∑ sg ∈ S, ∏ w : InfinitePlace E, TruncationCutoff 3 (abelian₂ w) (w (sg : E)) ≤
        C ^ Fintype.card (InfinitePlace E) * ∏ w : InfinitePlace E, (max 1 (abelian₂ w)) ^ 2
def GaussianLatticeCutoffSum : Prop :=
  ∀ (K abelian₂ : ℝ), 2 < K → 0 < abelian₂ → ∀ S : Finset GaussianInt,
    ∑ a ∈ S, TruncationCutoff K abelian₂ ‖(abelian₂ : ℂ) * GaussianInt.toComplex a‖ ≤ 4 * (3 / 2 : ℝ) ^ K * (K / (K - 2))
def ParitySign (s : ℕ) : ℤ := (-1) ^ (s * (s - 1) / 2)
def IndexedMinorEntry {F : Type} [Field F] {p : ℕ} (s : Fin p → ℕ) (t : Fin p → F) (a : Fin p) : F :=
  ∏ a' ∈ univ.filter (fun a' : Fin p => a' ≤ a), ((ParitySign (s a') : ℤ) : F) * t a' ^ s a'
def CompositionCountPowTwo : Prop := ∀ r : ℕ, Fintype.card (Composition (r + 1)) = 2 ^ r
def CompositionBlockProdBound : Prop :=
  ∀ (n : ℕ) (c : Composition n), ((c.blocks.prod : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) / Real.exp 1)
def BlockEndMinorFibreFinite : Prop :=
  ∀ (F : Type) [Field F] (p : ℕ) (s : Fin p → ℕ) (d : Fin p → F) (T : Finset (Fin p → F)),
    (∀ a, 1 ≤ s a) → (∀ t ∈ T, (∀ a, t a ≠ 0) ∧ ∀ a, IndexedMinorEntry s t a = d a) → T.card ≤ ∏ a, s a
noncomputable def blockMinorWeight {E : Type} [Field E] [NumberField E] {r : ℕ}
    (γ : Σ c : Composition (r + 1), (Fin c.length → E)) : ℝ :=
  ∏ a : Fin γ.1.length, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry γ.1.blocksFun γ.2 a)) ^ 2) ^ 2
def BlockEndMinorsIntegral {E : Type} [Field E] {r : ℕ} (γ : Σ c : Composition (r + 1), (Fin c.length → E)) : Prop :=
  ∀ a : Fin γ.1.length, IsIntegral ℤ (IndexedMinorEntry γ.1.blocksFun γ.2 a) ∧ IndexedMinorEntry γ.1.blocksFun γ.2 a ≠ 0
def BlockMinorSumExplicit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (r : ℕ)
    (S : Finset (Σ c : Composition (r + 1), (Fin c.length → E))), (∀ γ ∈ S, BlockEndMinorsIntegral γ) →
      ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ ≤ 2 ^ r * Real.exp (((r : ℝ) + 1) / Real.exp 1) *
        16 ^ (Fintype.card (InfinitePlace E) * (r + 1))
def BlockMinorSumPowSixtyFour : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (r : ℕ)
    (S : Finset (Σ c : Composition (r + 1), (Fin c.length → E))), (∀ γ ∈ S, BlockEndMinorsIntegral γ) →
      ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ ≤ 64 ^ (Fintype.card (InfinitePlace E) * (r + 1))
def BlockMinorSumPowerBound : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (r : ℕ)
    (S : Finset (Σ c : Composition (r + 1), (Fin c.length → E))), (∀ γ ∈ S, BlockEndMinorsIntegral γ) →
      ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ ≤ (C * r) ^ (Fintype.card (InfinitePlace E) * r)
def BlockMinorSumBoundCounterexample : Prop := ¬ BlockMinorSumPowerBound
def BlockMinorSumBound : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (r : ℕ), 1 ≤ r →
    ∀ S : Finset (Σ c : Composition (r + 1), (Fin c.length → E)), (∀ γ ∈ S, BlockEndMinorsIntegral γ) →
      ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ ≤ (C * r) ^ (Fintype.card (InfinitePlace E) * r)
def ProdMaxInvLeProdMax : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → ℝ), (∀ v, 0 < G v) → 1 ≤ ∏ v, G v →
    ∏ v, max 1 (1 / G v) ≤ ∏ v, max 1 (G v)
def NormGeOneMaxBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → ℝ) (D : ι → ℂ) (A : ℕ), (∀ v, 0 < G v) → 1 ≤ ∏ v, G v →
    (∀ v, G v ≤ ‖D v‖ ^ 2) →
    ∏ v, max 1 (1 / G v) ^ A ≤ ∏ v, max 1 (G v) ^ A ∧
      ∏ v, max 1 (G v) ^ A ≤ ∏ v, (1 + ‖D v‖ ^ 2) ^ A
def SumLeInvSumMulSup : Prop :=
  ∀ (α : Type) (S : Finset α) (w x : α → ℝ) (M : ℝ), (∀ γ ∈ S, 0 < w γ) →
    (∀ γ ∈ S, w γ ^ 2 * x γ ≤ M) → ∑ γ ∈ S, w γ * x γ ≤ (∑ γ ∈ S, 1 / w γ) * M
noncomputable def blockWeightPolynomial (r A' : ℕ) : MvPolynomial (Fin (r + 1) ⊕ Fin (r + 1)) ℝ :=
  (∏ l : Fin (r + 1), (1 + MvPolynomial.X (Sum.inl l) * MvPolynomial.X (Sum.inr l)) ^ 2) *
    (1 + MvPolynomial.X (Sum.inl (Fin.last r)) * MvPolynomial.X (Sum.inr (Fin.last r))) ^ A'
def WeightPolynomialCoefficients : Prop :=
  ∀ r A' : ℕ, (∀ m, 0 ≤ (blockWeightPolynomial r A').coeff m) ∧
    ∑ m ∈ (blockWeightPolynomial r A').support, (blockWeightPolynomial r A').coeff m = 4 ^ (r + 1) * 2 ^ A' ∧
    (blockWeightPolynomial r A').totalDegree ≤ 4 * (r + 1) + 2 * A'
def WeightEvalAtBlockEnds : Prop :=
  ∀ (r A' : ℕ) (d : Fin (r + 1) → ℂ) (Bs : Finset (Fin (r + 1))), (∀ l, l ∉ Bs → d l = 0) →
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) (Sum.elim d (fun l => star (d l))) (blockWeightPolynomial r A') =
      (((∏ l ∈ Bs, (1 + ‖d l‖ ^ 2) ^ 2) * (1 + ‖d (Fin.last r)‖ ^ 2) ^ A' : ℝ) : ℂ)
def SesquilinearTriangleBound : Prop :=
  ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (s : Finset ι) (a : ι → ℂ)
    (x : ι → V) (KK : ℝ), (∀ u v, B u v = star (B v u)) → (∀ u, 0 ≤ (B u u).re) →
    (∀ i ∈ s, (B (x i) (x i)).re ≤ KK) →
    (B (∑ i ∈ s, a i • x i) (∑ i ∈ s, a i • x i)).re ≤ (∑ i ∈ s, ‖a i‖) ^ 2 * KK
def BlockMinorProductBound : Prop :=
  ∀ (ι α : Type) [Fintype ι] (S : Finset α) (w x G d : α → ι → ℝ) (A : ℕ) (Kb Wb : ℝ), 0 ≤ Kb →
    (∀ γ ∈ S, ∀ v, 0 < w γ v ∧ 0 ≤ x γ v ∧ 0 < G γ v ∧ G γ v ≤ d γ v) →
    (∀ γ ∈ S, 1 ≤ ∏ v, G γ v) →
    (∀ γ ∈ S, ∀ v, w γ v ^ 2 * (1 + d γ v) ^ A * x γ v ≤ Kb * max 1 (1 / G γ v) ^ A) →
    ∑ γ ∈ S, (∏ v, w γ v)⁻¹ ≤ Wb →
    ∑ γ ∈ S, (∏ v, w γ v) * ∏ v, x γ v ≤ Wb * Kb ^ Fintype.card ι
def MomentUpwardHolder : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (r q : ℕ)
    (l : Fin (r + 1) → Ω → ℝ) (H0 R : ℝ),
    (∀ a, Measurable (l a)) → (∀ a ω, 0 < l a ω) → 0 ≤ H0 → 0 ≤ R →
    (∀ q' ≤ (r + 1) * q, ∫⁻ ω, ENNReal.ofReal (l 0 ω ^ (2 * q')) ∂μ ≤ ENNReal.ofReal (H0 ^ (2 * q'))) →
    (∀ c : Fin r, ∀ q' ≤ (r + 1) * q,
      ∫⁻ ω, ENNReal.ofReal ((l c.succ ω / l c.castSucc ω) ^ (2 * q')) ∂μ ≤ ENNReal.ofReal (R ^ (2 * q'))) →
    ∀ a : Fin (r + 1),
      ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (H0 ^ (2 * q) * R ^ (2 * q * a.val))
def MomentDownwardBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (r q : ℕ)
    (l : Fin (r + 1) → Ω → ℝ) (T R : ℝ),
    (∀ a, Measurable (l a)) → (∀ a ω, 0 < l a ω) → 1 ≤ T → 0 ≤ R →
    (∀ ω, T ≤ l (Fin.last r) ω ^ 2) →
    (∀ c : Fin r, ∀ q' ≤ (r + 1) * q,
      ∫⁻ ω, ENNReal.ofReal ((l c.succ ω / l c.castSucc ω) ^ (2 * q')) ∂μ ≤ ENNReal.ofReal (R ^ (2 * q'))) →
    ∀ a : Fin (r + 1),
      ∫⁻ ω, ENNReal.ofReal ((l a ω)⁻¹ ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (R ^ (2 * q * (r - a.val)))
def MomentMassBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (r q : ℕ)
    (l : Fin (r + 1) → Ω → ℝ) (H1 la : ℝ),
    (∀ a, Measurable (l a)) → (∀ a ω, 0 < l a ω) → 0 < H1 → 0 < la →
    (∀ a, ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (H1 ^ (2 * q))) →
    (∀ a, ∫⁻ ω, ENNReal.ofReal ((l a ω)⁻¹ ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (H1 ^ (2 * q))) →
    μ {ω | ∃ a, la * H1 ≤ max (l a ω) (l a ω)⁻¹} ≤ ENNReal.ofReal (2 * ((r : ℝ) + 1) / la ^ (2 * q))
def MomentProductBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (r q L : ℕ)
    (l : Fin (r + 1) → Ω → ℝ) (H1 : ℝ),
    (∀ a, Measurable (l a)) → (∀ a ω, 0 < l a ω) → 0 ≤ H1 → L ≤ r + 1 →
    (∀ a : Fin (r + 1), a.val < L →
      ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q * L)) ∂μ ≤ ENNReal.ofReal (H1 ^ (2 * q * L))) →
    ∫⁻ ω, ENNReal.ofReal ((∏ a ∈ univ.filter (fun a : Fin (r + 1) => a.val < L), l a ω) ^ (2 * q)) ∂μ ≤
      ENNReal.ofReal (H1 ^ (2 * q * L))
def MomentBound₂ : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (r q : ℕ)
    (l : Fin (r + 1) → Ω → ℝ) (H0 R T : ℝ),
    (∀ a, Measurable (l a)) → (∀ a ω, 0 < l a ω) → 1 ≤ H0 → 0 ≤ R → 1 ≤ T →
    (∀ q' ≤ (r + 1) * q, ∫⁻ ω, ENNReal.ofReal (l 0 ω ^ (2 * q')) ∂μ ≤ ENNReal.ofReal (H0 ^ (2 * q'))) →
    (∀ c : Fin r, ∀ q' ≤ (r + 1) * q,
      ∫⁻ ω, ENNReal.ofReal ((l c.succ ω / l c.castSucc ω) ^ (2 * q')) ∂μ ≤ ENNReal.ofReal (R ^ (2 * q'))) →
    (∀ ω, T ≤ l (Fin.last r) ω ^ 2) →
    (∀ a, ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal ((H0 * max 1 R ^ r) ^ (2 * q)) ∧
      ∫⁻ ω, ENNReal.ofReal ((l a ω)⁻¹ ^ (2 * q)) ∂μ ≤ ENNReal.ofReal ((H0 * max 1 R ^ r) ^ (2 * q))) ∧
    ∀ la : ℝ, 0 < la → μ {ω | ∃ a, la * (H0 * max 1 R ^ r) ≤ max (l a ω) (l a ω)⁻¹} ≤
      ENNReal.ofReal (2 * ((r : ℝ) + 1) / la ^ (2 * q))
def SumSqLeCardMulSumSq : Prop :=
  ∀ (V ι : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ) (v : ι → V),
    ‖∑ s, c s • v s‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ s, ‖c s‖ ^ 2 * ‖v s‖ ^ 2
def MomentRecursionBound : Prop :=
  ∀ (Ω ιc ιs : Type) [MeasurableSpace Ω] [Fintype ιc] [Fintype ιs] (ν : Measure Ω) (L : Ω → ENNReal)
    (X : ιc → Ω → ENNReal) (Ph : Ω → ENNReal) (Phs : ιc → ιs → Ω → ENNReal) (A : ιs → ENNReal)
    (Ns : ιc → ιs → ENNReal) (Nw Amax MMx QQ : ENNReal) (q : ℕ),
    Measurable L → (∀ c s, Measurable (Phs c s)) → (∀ g, L g = ∑ c, X c g) →
    (∀ c g, X c g * Ph g ≤ (Fintype.card ιs : ENNReal) * ∑ s, A s * Phs c s g) → (∀ s, A s ≤ Amax) →
    (∀ c s, ∫⁻ g, L g ^ q * Phs c s g ∂ν ≤ MMx * Ns c s) → (∀ c, ∑ s, Ns c s ≤ QQ * Nw) →
    ∫⁻ g, L g ^ (q + 1) * Ph g ∂ν ≤
      (Fintype.card ιs : ENNReal) * Amax * MMx * (Fintype.card ιc : ENNReal) * QQ * Nw
def MomentRecursionIterate : Prop :=
  ∀ (P ι : Type) (step : P → ι → P) (d : P → ℕ) (MM : ℕ → P → ℕ → ENNReal) (c : ENNReal) (q0 J : ℕ),
    (∀ μ s, d (step μ s) ≤ d μ + 1) → (∀ μ j, MM 0 μ j ≤ 1) →
    (∀ q μ j, d μ + 1 ≤ q0 → j + 2 ≤ J → MM (q + 1) μ j ≤ c * ⨆ s, MM q (step μ s) (j + 2)) →
    ∀ q μ j, d μ + q ≤ q0 → j + 2 * q ≤ J → MM q μ j ≤ c ^ q
def IteratedSuperharmonicBound : Prop :=
  ∀ (W ι : Type) [Fintype ι] (Eop : ι → W → W) (Φ : W → ℝ) (κ : ℝ), 0 ≤ κ →
    (∀ w, κ * Φ w ≤ ∑ i, Φ (Eop i w)) →
    ∀ (q : ℕ) (w : W), κ ^ q * Φ w ≤ ∑ σ : Fin q → ι, Φ ((List.ofFn σ).foldr Eop w)
def IteratedOperatorNormBound : Prop :=
  ∀ (W ι : Type) [Fintype ι] (Eop : ι → W → W) (Nw : W → ℝ) (Fil : ℕ → Set W) (c : ℕ → ℝ),
    (∀ j, 0 ≤ c j) → (∀ i j w, w ∈ Fil j → Eop i w ∈ Fil (j + 2)) →
    (∀ j w, w ∈ Fil j → ∑ i, Nw (Eop i w) ≤ c j * Nw w) →
    ∀ (q j : ℕ) (w : W), w ∈ Fil j →
      ∑ σ : Fin q → ι, Nw ((List.ofFn σ).foldr Eop w) ≤ (∏ i ∈ range q, c (j + 2 * i)) * Nw w
def SuperharmonicMomentBound : Prop :=
  ∀ (Ω W ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (Eop : ι → W → W)
    (Ph : W → Ω → ENNReal) (κ : Ω → ENNReal) (Nw : W → ENNReal) (Fil : ℕ → Set W) (c : ℕ → ENNReal),
    (∀ w, Measurable (Ph w)) → (∀ w, ∫⁻ g, Ph w g ∂ν = Nw w) →
    (∀ w g, κ g * Ph w g ≤ ∑ i, Ph (Eop i w) g) →
    (∀ i j w, w ∈ Fil j → Eop i w ∈ Fil (j + 2)) →
    (∀ j w, w ∈ Fil j → ∑ i, Nw (Eop i w) ≤ c j * Nw w) →
    ∀ (q j : ℕ) (w : W), w ∈ Fil j →
      ∫⁻ g, κ g ^ q * Ph w g ∂ν ≤ (∏ i ∈ range q, c (j + 2 * i)) * Nw w
def FormalDegreeSubsetSum : Prop :=
  ∀ (n l : ℕ) (tau ratio : Finset (Fin n) → ℝ) (H : ℝ), 0 ≤ H →
    (∀ I : Finset (Fin n), I.card = l → |tau I| ≤ H ^ l ∧ 0 ≤ ratio I ∧ ratio I ≤ (Real.exp 1 * n) ^ l) →
    ∑ I ∈ powersetCard l (univ : Finset (Fin n)), |tau I| * √(ratio I) ≤ (2 * (n : ℝ) ^ (3 / 2 : ℝ) * H) ^ l
def IteratedHighestWeightBound : Prop :=
  ∀ (V P Λ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup P] (jh : P → V) (Dop : Λ → Module.End ℂ V)
    (wt : Λ → ℕ) (N1 Ninf : P → ℕ) (lam : P) (Gam : ℝ) (c0 q0 : ℕ), 0 ≤ Gam →
    (∀ x y, N1 (x + y) ≤ N1 x + N1 y) → (∀ x y, Ninf (x + y) ≤ Ninf x + Ninf y) → N1 0 = 0 → Ninf 0 = 0 →
    (∀ μ l, N1 (μ - lam) + c0 ≤ q0 → ∃ a : P →₀ ℂ, Dop l (jh μ) = a.sum (fun ν c => c • jh (μ + ν)) ∧
      (a.sum fun _ c => ‖c‖) ≤ Gam ^ wt l ∧ ∀ ν ∈ a.support, N1 ν ≤ wt l ∧ Ninf ν ≤ 1) →
    ∀ (μ : P) (al : List Λ), N1 (μ - lam) + (al.map wt).sum + c0 ≤ q0 →
      ∃ a : P →₀ ℂ, (al.map Dop).prod (jh μ) = a.sum (fun ν c => c • jh (μ + ν)) ∧
        (a.sum fun _ c => ‖c‖) ≤ Gam ^ (al.map wt).sum ∧
        ∀ ν ∈ a.support, N1 ν ≤ (al.map wt).sum ∧ Ninf ν ≤ al.length
def LemSSupBound : Prop :=
  ∀ (φ : ℂ → ℂ) (x M : ℝ), Continuous φ → Integrable φ → 0 < x →
    (∀ s : ℂ, ‖∫ c : ℂ, Complex.exp (2 * Complex.I * ((s * c).im : ℂ)) * φ c‖ ≤ M * TruncationCutoff 3 x ‖s‖) →
    ∀ c, ‖φ c‖ ≤ 3 / π * x ^ 2 * M
def BpAssembly : Prop :=
  ∀ (nγ jg JFp JFm βp βm jj b T' G c2 K3 : ℝ) (n0 p : ℕ), 0 ≤ nγ → 0 < b → 0 < T' → 0 < G → 0 ≤ c2 →
    jg ≤ (3 * b) ^ (2 * n0) * (T' / G) ^ n0 * (G ^ (2 * p))⁻¹ * (JFp + JFm) →
    nγ * JFp ≤ c2 * βp → nγ * JFm ≤ c2 * βm →
    βp ≤ (T' ^ n0)⁻¹ * K3 * jj → βm ≤ (T' ^ n0)⁻¹ * K3 * jj →
    nγ * jg ≤ 2 * (3 * b) ^ (2 * n0) * c2 * K3 * (G ^ (2 * p + n0))⁻¹ * jj
def BpMaxG : Prop :=
  ∀ (G : ℝ) (a A : ℕ), 0 < G → a ≤ A → (G ^ a)⁻¹ ≤ max 1 (1 / G) ^ A
end PartA
section PartB
open Finset Matrix Polynomial
open scoped ComplexConjugate TensorProduct
def IsLowerUnitriangular {d : ℕ} {R : Type*} [Zero R] [One R] (l : Matrix (Fin d) (Fin d) R) : Prop :=
  (∀ i, l i i = 1) ∧ ∀ i j, i < j → l i j = 0
def IsUpperUnitriangular {d : ℕ} {R : Type*} [Zero R] [One R] (u : Matrix (Fin d) (Fin d) R) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0
def leadingPrincipalMinor {d : ℕ} {R : Type*} [CommRing R] (Z : Matrix (Fin d) (Fin d) R) (q : ℕ) : R :=
  (Z.submatrix (fun i : {i : Fin d // (i : ℕ) < q} => i.1) (fun i : {i : Fin d // (i : ℕ) < q} => i.1)).det
def blockAntidiagonalMatrix {d : ℕ} {R : Type*} [Zero R] (c : Composition d) (t : Fin c.length → R) :
    Matrix (Fin d) (Fin d) R := fun i j =>
  if c.index i = c.index j ∧
      (i : ℕ) + (j : ℕ) + 1 = c.sizeUpTo (c.index i : ℕ) + c.sizeUpTo ((c.index i : ℕ) + 1)
  then t (c.index i) else 0
def mixedMinor {d : ℕ} {R : Type*} [CommRing R] (Z : Matrix (Fin d) (Fin d) R) (i j' : Fin d) : R :=
  (Z.submatrix (fun a : Fin ((i : ℕ) + 1) => Fin.castLE (Nat.succ_le_of_lt i.isLt) a)
    (fun b : Fin ((i : ℕ) + 1) =>
      if (b : ℕ) < (i : ℕ) then Fin.castLE (Nat.succ_le_of_lt i.isLt) b else j')).det
def LeadingMinorUnipotentInvariant : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (Z l u : Matrix (Fin d) (Fin d) R) (q : ℕ),
    IsLowerUnitriangular l → IsUpperUnitriangular u → leadingPrincipalMinor (l * Z * u) q = leadingPrincipalMinor Z q
def LeadingMinorVanishesOffBlockEnds : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (c : Composition d) (t : Fin c.length → R) (q : ℕ),
    q ≤ d → (∀ p : ℕ, q ≠ c.sizeUpTo p) → leadingPrincipalMinor (blockAntidiagonalMatrix c t) q = 0
def LeadingMinorAtBlockEnd : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (c : Composition d) (t : Fin c.length → R) (p : ℕ),
    leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) =
      ∏ a ∈ univ.filter (fun a : Fin c.length => (a : ℕ) < p),
        (-1) ^ ((c.blocksFun a).choose 2) * t a ^ (c.blocksFun a)
def MixedMinorVanishing : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (c : Composition d) (t : Fin c.length → R)
    (l u : Matrix (Fin d) (Fin d) R), IsLowerUnitriangular l → IsUpperUnitriangular u →
    ∀ i j' : Fin d, (i : ℕ) = c.sizeUpTo (c.index i : ℕ) → c.index j' = c.index i →
      ((j' : ℕ) + 1 < c.sizeUpTo ((c.index i : ℕ) + 1) → mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = 0) ∧
      ((j' : ℕ) + 1 = c.sizeUpTo ((c.index i : ℕ) + 1) →
        mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = leadingPrincipalMinor (blockAntidiagonalMatrix c t) (i : ℕ) * t (c.index i))
def UnipotentStabiliserInverse : Prop :=
  ∀ (K : Type) [Field K] (d : ℕ) (c : Composition d) (t : Fin c.length → K), (∀ a, t a ≠ 0) →
    ∀ l u : Matrix (Fin d) (Fin d) K, IsLowerUnitriangular l → IsUpperUnitriangular u →
      (l * blockAntidiagonalMatrix c t * u = blockAntidiagonalMatrix c t ↔
        (∀ i j, c.index i ≠ c.index j → u i j = 0) ∧
          l = blockAntidiagonalMatrix c (fun _ => (1 : K)) * u⁻¹ * blockAntidiagonalMatrix c (fun _ => (1 : K)))
def ConjugatedUnitriangularLower : Prop :=
  ∀ (K : Type) [Field K] (d : ℕ) (c : Composition d) (u : Matrix (Fin d) (Fin d) K), IsUpperUnitriangular u →
    (∀ i j, c.index i ≠ c.index j → u i j = 0) →
      IsLowerUnitriangular (blockAntidiagonalMatrix c (fun _ => (1 : K)) * u⁻¹ * blockAntidiagonalMatrix c (fun _ => (1 : K)))
def OrbitIntegralEntries : Prop :=
  ∀ (K : Type) [Field K] (O : Subring K) (d : ℕ) (c : Composition d) (t : Fin c.length → K),
    (∀ a, t a ≠ 0) → ∀ l u : Matrix (Fin d) (Fin d) K, IsLowerUnitriangular l → IsUpperUnitriangular u →
      (∀ i j, (l * blockAntidiagonalMatrix c t * u) i j ∈ O) →
        (∀ p : ℕ, leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) ∈ O ∧ leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) ≠ 0) ∧
        ∀ a : Fin c.length, leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo (a : ℕ)) * t a ∈ O
def BlockEndMinorsFixUpToRoots : Prop :=
  ∀ (K : Type) [Field K] (d : ℕ) (c : Composition d) (t t' : Fin c.length → K),
    (∀ a, t a ≠ 0) → (∀ a, t' a ≠ 0) →
    (∀ p : ℕ, leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) = leadingPrincipalMinor (blockAntidiagonalMatrix c t') (c.sizeUpTo p)) →
      ∀ a, t a ^ (c.blocksFun a) = t' a ^ (c.blocksFun a)
noncomputable def E6co (d : ℕ) (δ : ℝ) (i : ℕ) : ℝ :=
  (-1) ^ (d + i) * (d.choose i : ℝ) / ((d.factorial : ℝ) * δ ^ d)
def FiniteDifferenceLeadingCoeff : Prop :=
  ∀ (d : ℕ) (y0 δ : ℝ), 0 < δ → ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (a : Fin (d + 1) → V),
    a (Fin.last d) =
      ∑ i : Fin (d + 1), E6co d δ (i : ℕ) • ∑ k : Fin (d + 1), (y0 + ((i : ℕ) : ℝ) * δ) ^ (k : ℕ) • a k
def FiniteDifferenceCoeffSum : Prop :=
  ∀ (d : ℕ) (δ : ℝ), 0 < δ →
    ∑ i : Fin (d + 1), |E6co d δ (i : ℕ)| = 2 ^ d / ((d.factorial : ℝ) * δ ^ d) ∧
    (2 ≤ δ → ∑ i : Fin (d + 1), |E6co d δ (i : ℕ)| ≤ 1)
noncomputable def shiftedGridPoint (r : ℕ) (y0 : ℝ) (ν i : ℕ) : ℝ := y0 + 5 * (((ν : ℝ)) * (2 * (r : ℝ) + 1) + (i : ℝ))
def GridsInInterval : Prop :=
  ∀ (r : ℕ) (α β : ℝ), 30 * ((r : ℝ) + 1) ^ 2 + 2 ≤ β - α →
    (∀ ν i : ℕ, ν < 3 * (r + 1) → i ≤ 2 * r →
      α < shiftedGridPoint r (α + 1) ν i ∧ shiftedGridPoint r (α + 1) ν i + 1 < β) ∧
    (∀ ν i ν' i' : ℕ, i ≤ 2 * r → i' ≤ 2 * r → (ν, i) ≠ (ν', i') →
      5 ≤ |shiftedGridPoint r (α + 1) ν i - shiftedGridPoint r (α + 1) ν' i'| ∧
      4 ≤ |shiftedGridPoint r (α + 1) ν i + 1 - shiftedGridPoint r (α + 1) ν' i'|)
def LeadingCoefficientFromGrid : Prop :=
  ∀ (r d ν : ℕ) (y0 : ℝ), d ≤ 2 * r →
    (∑ i : Fin (d + 1), |E6co d 5 (i : ℕ)| ≤ 1) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (a : Fin (d + 1) → V),
      a (Fin.last d) =
        ∑ i : Fin (d + 1), E6co d 5 (i : ℕ) • ∑ k : Fin (d + 1), (shiftedGridPoint r y0 ν (i : ℕ)) ^ (k : ℕ) • a k
def BlockGramDeterminant : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (T T' : ℝ),
    (Matrix.fromBlocks ((-(T : ℂ)) • Matrix.single (Fin.last r) (Fin.last r) (1 : ℂ)) Z Zᴴ
        ((-(T' : ℂ)) • Matrix.single (Fin.last r) (Fin.last r) (1 : ℂ))).det =
      (-1) ^ (r + 1) *
        (((Complex.normSq Z.det : ℝ) : ℂ) - (T : ℂ) * (T' : ℂ) * ((Complex.normSq (leadingPrincipalMinor Z r) : ℝ) : ℂ))
def UnipotentStabiliserCharacterisation : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    ∀ p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      p ∈ Formalism.QuantumDeterminants.Sset k r z ↔
        (p ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
          ∀ a : Fin (r + 1), ∃ co : Fin (r + 1) → ℂ,
            p *ᵥ Formalism.QuantumDeterminants.fvec k r z a =
              Formalism.QuantumDeterminants.fvec k r z a + ∑ b ∈ univ.filter (fun b => b < a), co b • Formalism.QuantumDeterminants.fvec k r z b)
def StabiliserPairMatrices : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a a' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
    p ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
    (∀ b, p *ᵥ Formalism.QuantumDeterminants.fvec k r z b = ∑ e, a e b • Formalism.QuantumDeterminants.fvec k r z e) →
    (∀ b, p *ᵥ (g *ᵥ Formalism.QuantumDeterminants.fvec k r z' b) = ∑ e, a' e b • (g *ᵥ Formalism.QuantumDeterminants.fvec k r z' e)) →
      aᴴ * Formalism.QuantumDeterminants.Zhat k r z z' g * a' = Formalism.QuantumDeterminants.Zhat k r z z' g
def StabiliserComplementRank : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), 0 < Formalism.QuantumDeterminants.Gf k r z z' g →
      LinearIndependent ℂ (Formalism.QuantumDeterminants.gramVec k r z z' g) ∧
      ∀ x : Fin (2 * r + k + 1) → ℂ, x ≠ 0 →
        (∀ i, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x (Formalism.QuantumDeterminants.gramVec k r z z' g i) = 0) →
          0 < (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x x).re
def BlockDiagonalStabiliser : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ (c : Composition (r + 1)) (t : Fin c.length → ℂ), (∀ a, t a ≠ 0) →
      Formalism.QuantumDeterminants.Zhat k r z z' g = blockAntidiagonalMatrix c t →
      ∀ p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
        (p ∈ Formalism.QuantumDeterminants.Sset k r z ∧ g⁻¹ * p * g ∈ Formalism.QuantumDeterminants.Sset k r z') ↔
          (p ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
            ∃ a' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUpperUnitriangular a' ∧
              (∀ i j, c.index i ≠ c.index j → a' i j = 0) ∧
              (∀ b, p *ᵥ (g *ᵥ Formalism.QuantumDeterminants.fvec k r z' b) = ∑ e, a' e b • (g *ᵥ Formalism.QuantumDeterminants.fvec k r z' e)) ∧
              (∀ b, p *ᵥ Formalism.QuantumDeterminants.fvec k r z b =
                ∑ e, (blockAntidiagonalMatrix c (fun _ => (1 : ℂ)) * a'⁻¹ * blockAntidiagonalMatrix c (fun _ => (1 : ℂ)))ᴴ e b • Formalism.QuantumDeterminants.fvec k r z e))
def StabiliserFromGramPair : Prop := UnipotentStabiliserCharacterisation → StabiliserPairMatrices → UnipotentStabiliserInverse → ConjugatedUnitriangularLower → BlockDiagonalStabiliser
def DualVectorNormSq : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ x y, h y x = conj (h x y)) →
    ∀ (r : ℕ) (y f' : Fin (r + 1) → V) (T T' : ℝ), T' ≠ 0 →
      (∀ a b, h (y a) (y b) = if a = Fin.last r ∧ b = Fin.last r then -(T : ℂ) else 0) →
      (∀ a b, h (f' a) (f' b) = if a = Fin.last r ∧ b = Fin.last r then -(T' : ℂ) else 0) →
      ∀ (x0 om : V) (al : ℂ),
        x0 ∈ Submodule.span ℂ (f' '' {b | b ≠ Fin.last r}) → (∀ b, h om (f' b) = 0) →
        (∑ a, (Matrix.of fun a b => h (y a) (f' b)).adjugate (Fin.last r) a • y a) = x0 + al • f' (Fin.last r) + om →
          h om om =
            (((Complex.normSq (Matrix.of fun a b => h (y a) (f' b)).det : ℝ) : ℂ) -
              (T : ℂ) * (T' : ℂ) *
                ((Complex.normSq (leadingPrincipalMinor (Matrix.of fun a b => h (y a) (f' b)) r) : ℝ) : ℂ)) / (T' : ℂ)
def SignedParsevalIdentity : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ)
    (xi : Module.Basis (Fin n) ℂ V) (ep : Fin n → ℝ), (∀ c, ep c = 1 ∨ ep c = -1) →
    (∀ c c', h (xi c) (xi c') = if c = c' then (ep c : ℂ) else 0) →
      ∀ v, ∑ c, (ep c : ℂ) * ((Complex.normSq (h v (xi c)) : ℝ) : ℂ) = h v v
def PolarisedParsevalIdentity : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ)
    (xi : Module.Basis (Fin n) ℂ V) (ep : Fin n → ℝ), (∀ c, ep c = 1 ∨ ep c = -1) →
    (∀ c c', h (xi c) (xi c') = if c = c' then (ep c : ℂ) else 0) →
      ∀ v w, ∑ c, (ep c : ℂ) * h v (xi c) * conj (h w (xi c)) = h v w
def CauchyBinetHermitianGram : Prop :=
  ∀ (n l : ℕ) (ep : Fin n → ℂ) (x y : Fin l → Fin n → ℂ),
    (Matrix.of fun a b : Fin l => ∑ i, ep i * x b i * conj (y a i)).det =
      ∑ I : {I : Finset (Fin n) // I.card = l},
        (∏ i ∈ I.1, ep i) * (Matrix.of fun a b : Fin l => x b (I.1.orderEmbOfFin I.2 a)).det *
          conj ((Matrix.of fun a b : Fin l => y b (I.1.orderEmbOfFin I.2 a)).det)
def PartialTraceScalarCommutator : Prop :=
  ∀ (R : Type) [Ring R] (n : ℕ) (x : R) (A : Matrix (Fin n) (Fin n) R),
    (Matrix.scalar (Fin n) x * A - A * Matrix.scalar (Fin n) x).trace = x * A.trace - A.trace * x
def PartialTraceTensorCommutator : Prop :=
  ∀ (k R : Type) [CommRing k] [Ring R] [Algebra k R] (n : ℕ) (X : Matrix (Fin n) (Fin n) k)
    (A : Matrix (Fin n) (Fin n) R),
    (X.map (algebraMap k R) * A - A * X.map (algebraMap k R)).trace = 0
def TensorFormPolarisation : Prop :=
  ∀ (W V : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (Q : (W ⊗[ℂ] V) →ₗ[ℂ] (W ⊗[ℂ] V) →ₗ⋆[ℂ] ℂ),
    (∀ (w : W) (ξ : V), Q (w ⊗ₜ[ℂ] ξ) (w ⊗ₜ[ℂ] ξ) = 0) → Q = 0
noncomputable def lagrangeBasisPoly {K ι : Type*} [Field K] [DecidableEq ι] (S : Finset ι) (om : ι → K) (s : ι) : K[X] :=
  ∏ s' ∈ S.erase s, (C (om s - om s')⁻¹ * (X - C (om s')))
def LagrangeProjectorFormula : Prop :=
  ∀ (K M : Type) [Field K] [AddCommGroup M] [Module K M] (Om : Module.End K M) (n : ℕ) (om : Fin n → K),
    Function.Injective om → ∀ (s t : Fin n) (x : M), Om x = om t • x →
      Polynomial.aeval Om (lagrangeBasisPoly univ om s) x = if t = s then x else 0
def TensorFormProjectorIdentity : Prop :=
  ∀ (W V : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (B : (W ⊗[ℂ] V) →ₗ[ℂ] (W ⊗[ℂ] V) →ₗ⋆[ℂ] ℂ), (∀ x, (∀ y, B x y = 0) → x = 0) →
    ∀ (n : ℕ) (pr : Fin n → Module.End ℂ (W ⊗[ℂ] V)) (d : ℝ) (ds rho : Fin n → ℝ),
      (∀ s t, pr s * pr t = if s = t then pr s else 0) → ∑ s, pr s = 1 → 0 < d → (∀ s, 0 < ds s) →
      (∀ (w : W) (ξ : V), B (w ⊗ₜ[ℂ] ξ) (w ⊗ₜ[ℂ] ξ) / (d : ℂ) =
        ∑ s, ((rho s / ds s : ℝ) : ℂ) * B (pr s (w ⊗ₜ[ℂ] ξ)) (w ⊗ₜ[ℂ] ξ)) →
      ∀ s, pr s ≠ 0 → ds s = rho s * d
def PolarisedFormBound : Prop := TensorFormPolarisation → TensorFormProjectorIdentity
def IsSelfAdjointInvolution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V) : Prop :=
  (∀ x, θ (θ x) = x) ∧ ∀ x y, inner ℂ (θ x) y = inner ℂ x (θ y)
noncomputable def majorantHermitianForm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V) (x y : V) : ℂ :=
  inner ℂ (θ y) x
noncomputable def majorantDistance {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} (y : Fin n → V)
    (a : Fin n) : ℝ :=
  Metric.infDist (y a) (Submodule.span ℂ (y '' {b | b < a}) : Set V)
def MajorantNormBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ x : V, ‖majorantHermitianForm θ x x‖ ≤ ‖x‖ ^ 2
def LastDistanceLowerBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ (r : ℕ) (y : Fin (r + 1) → V) (T : ℝ),
      (∀ a b, majorantHermitianForm θ (y a) (y b) = if a = Fin.last r ∧ b = Fin.last r then -(T : ℂ) else 0) →
        T ≤ majorantDistance y (Fin.last r) ^ 2
def GramDetEqProdDistances : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (l : ℕ) (y : Fin l → V),
    (Matrix.of fun a b => inner ℂ (y a) (y b)).det = ((∏ a, majorantDistance y a ^ 2 : ℝ) : ℂ)
def RankTwoOperatorSkewHermitian : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ x y, h y x = conj (h x y)) →
    ∀ e v x y : V, h (h x v • e - h x e • v) y + h x (h y v • e - h y e • v) = 0
def MajorantPhaseChoice : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ (u y1 : V) (S : Set V), u ≠ 0 → (∀ w ∈ S, inner ℂ u w = 0) → inner ℂ u y1 = ((‖u‖ ^ 2 : ℝ) : ℂ) →
      ‖(Complex.I / (‖u‖ : ℂ)) • θ u‖ = 1 ∧
      (∀ w ∈ S, majorantHermitianForm θ w ((Complex.I / (‖u‖ : ℂ)) • θ u) = 0) ∧
      majorantHermitianForm θ y1 ((Complex.I / (‖u‖ : ℂ)) • θ u) = -Complex.I * (‖u‖ : ℂ)
def SkewOperatorFrobeniusBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ V) (e v : V),
      ∑ a, ∑ b, ‖inner ℂ (bs a) (majorantHermitianForm θ (bs b) v • e - majorantHermitianForm θ (bs b) e • v)‖ ^ 2 ≤ 4 * ‖e‖ ^ 2 * ‖v‖ ^ 2
def DiagonalResolventLowerBound : Prop :=
  ∀ (H ι : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι] (bs : OrthonormalBasis ι ℂ H)
    (D : H →ₗ[ℂ] H) (δ : ι → ℂ) (ζ : ℂ) (d : ℝ), (∀ i, D (bs i) = δ i • bs i) → (∀ i, d ≤ ‖ζ - δ i‖) →
      ∀ x, d * ‖x‖ ≤ ‖ζ • x - D x‖
def PerturbedResolventLowerBound : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (D O : H →ₗ[ℂ] H) (VV : Submodule ℂ H) (ζ : ℂ) (d ε : ℝ),
    (∀ x, d * ‖x‖ ≤ ‖ζ • x - D x‖) → (∀ x ∈ VV, ‖O x‖ ≤ ε * ‖x‖) →
      ∀ x ∈ VV, (d - ε) * ‖x‖ ≤ ‖ζ • x - (D + O) x‖
def OffDiagonalSumBound : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] (n : ℕ) (v : Fin n → Fin n → H),
    ∑ b, ‖∑ c ∈ univ.erase b, v b c‖ ^ 2 ≤ ((n : ℝ) - 1) * ∑ c, ∑ b ∈ univ.erase c, ‖v b c‖ ^ 2
def OffDiagonalOperatorBound : Prop :=
  ∀ (n j b bs : ℝ), 1 ≤ n → 0 ≤ j → 0 ≤ bs → j + 2 ≤ b / (8704 * n) → 8704 * n ^ 3 ≤ b → bs ≤ 2.02 * b →
    (n - 1) * (8 * (bs + j + 2) * (n ^ 2 + j + 2)) ≤ (b / 16) ^ 2
def CircleAvoidsSpectrum : Prop :=
  ∀ (b δ t : ℝ) (ζ : ℂ), ‖ζ + ((b / 16 : ℝ) : ℂ)‖ = 9 * b / 16 →
    ((-b / 8 - δ ≤ t ∧ t ≤ δ) ∨ (b - δ ≤ t ∧ t ≤ 2 * b + δ)) → b / 2 - δ ≤ ‖ζ - (t : ℂ)‖
def RieszProjectorContour : Prop :=
  ∀ (E ι : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
    (T : E →ₗ[ℂ] E) (p : ι → E →ₗ[ℂ] E) (lam : ι → ℂ) (In : Finset ι) (c : ℂ) (R M : ℝ), 0 < R →
    (∀ x, ∑ i, p i x = x) → (∀ i x, T (p i x) = lam i • p i x) →
    (∀ i ∈ In, ‖lam i - c‖ < R) → (∀ i, i ∉ In → R < ‖lam i - c‖) →
    (∀ ζ : ℂ, ‖ζ - c‖ = R → ∀ x, ‖x‖ ≤ M * ‖ζ • x - T x‖) →
      ∀ x, ‖∑ i ∈ In, p i x‖ ≤ R * M * ‖x‖
def ClusterProjectorNormBound : Prop :=
  ∀ (H ι κ : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι] [Fintype κ]
    (bs : OrthonormalBasis ι ℂ H) (D O : H →ₗ[ℂ] H) (δ : ι → ℝ) (VV : Submodule ℂ H) (b dl : ℝ)
    (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (In : Finset κ), 0 < b → dl ≤ b / 32 →
    (∀ i, D (bs i) = (δ i : ℂ) • bs i) →
    (∀ i, (-b / 8 - dl ≤ δ i ∧ δ i ≤ dl) ∨ (b - dl ≤ δ i ∧ δ i ≤ 2 * b + dl)) →
    (∀ x ∈ VV, ‖O x‖ ≤ b / 16 * ‖x‖) → (∀ x ∈ VV, (D + O) x ∈ VV) →
    (∀ x ∈ VV, ∑ i, p i x = x) → (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ (D + O) (p i x) = lam i • p i x) →
    (∀ i ∈ In, ‖lam i + ((b / 16 : ℝ) : ℂ)‖ < 9 * b / 16) → (∀ i, i ∉ In → 9 * b / 16 < ‖lam i + ((b / 16 : ℝ) : ℂ)‖) →
      ∀ x ∈ VV, ‖∑ i ∈ In, p i x‖ ≤ 18 / 13 * ‖x‖
def ClusterNormBound : Prop := DiagonalResolventLowerBound → PerturbedResolventLowerBound → CircleAvoidsSpectrum → RieszProjectorContour → ClusterProjectorNormBound
def NodeProjectorLagrangeFormula : Prop :=
  ∀ (K E ι : Type) [Field K] [AddCommGroup E] [Module K E] [DecidableEq ι]
    (T : Module.End K E) (p : ι → Module.End K E) (lam : ι → K) (Nd : Finset ι) (s : ι), s ∈ Nd →
    Set.InjOn lam (Nd : Set ι) → (∀ i x, T (p i x) = lam i • p i x) →
      ∀ x, Polynomial.aeval T (lagrangeBasisPoly Nd lam s) (∑ i ∈ Nd, p i x) = p s x
def NodeProjectorNormBound : Prop :=
  ∀ (E ι : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [DecidableEq ι]
    (T : E →ₗ[ℂ] E) (p : ι → E →ₗ[ℂ] E) (lam : ι → ℂ) (Nd : Finset ι) (s : ι) (Bd Cn : ℝ), s ∈ Nd →
    (∀ i x, T (p i x) = lam i • p i x) →
    (∀ j ∈ Nd.erase s, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ Nd.erase s, ∀ x, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) →
    (∀ x, ‖∑ i ∈ Nd, p i x‖ ≤ Cn * ‖x‖) →
      ∀ x, ‖p s x‖ ≤ Cn * Bd ^ (Nd.erase s).card * ‖x‖
end PartB
section PartC
open Finset
def WIL {K : ℕ} (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) : Prop :=
  ∀ i : Fin K, rho i ≤ u i.castSucc - 1 / 2 ∧ u i.succ + 1 / 2 ≤ rho i
def WInterl {K : ℕ} (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) : Prop :=
  StrictAnti u ∧ (∀ i j, ∃ z : ℤ, u i - u j = (z : ℝ)) ∧
    (∀ i j, ∃ z : ℤ, rho i - u j = (z : ℝ) + 1 / 2) ∧ WIL u rho
noncomputable def wPlus {K : ℕ} (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin (K + 1)) : ℝ :=
  (∏ i : Fin K, |u l + 1 / 2 - rho i|) / ∏ i ∈ univ.erase l, |u l - u i|
noncomputable def wMinus {K : ℕ} (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin (K + 1)) : ℝ :=
  (∏ i : Fin K, |u l - 1 / 2 - rho i|) / ∏ i ∈ univ.erase l, |u l - u i|
def ResolventPartialFractions : Prop :=
  ∀ (F : Type) [Field F] (K : ℕ) (u : Fin (K + 1) → F) (r : Fin K → F) (x : F),
    Function.Injective u → (∀ l, x ≠ u l) →
    (∏ i, (x - r i)) / ∏ l, (x - u l) =
      ∑ l, ((∏ i, (u l - r i)) / ∏ j ∈ univ.erase l, (u l - u j)) / (x - u l)
def WignerSquareFromPartialFractions : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (w : Fin (K + 1) → ℝ),
    Function.Injective u → (∀ l, 0 ≤ w l) →
    (∀ x : ℝ, (∀ l, x ≠ u l) →
      ∑ l, w l / (x - u l) = (∏ i, (x - rho i + 1 / 2)) / ∏ l, (x - u l)) →
    ∀ l, w l = wPlus u rho l
def ResidueNonnegOfInterlacing : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ), WInterl u rho → ∀ l,
    (∏ i, (u l + 1 / 2 - rho i)) / ∏ j ∈ univ.erase l, (u l - u j) = wPlus u rho l
def BranchingCoefficientsSumOne : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ), WInterl u rho →
    ∑ l, wPlus u rho l = 1 ∧ ∑ l, wMinus u rho l = 1
def LoweringEqRaisingReversed : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ),
    (∀ l, wMinus u rho l = wPlus (fun i => -u i.rev) (fun i => -rho i.rev) l.rev) ∧
    (WInterl u rho → WInterl (fun i => -u i.rev) (fun i => -rho i.rev))
def RaisingCoefficientVanishing : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ), WInterl u rho → ∀ l,
    (wPlus u rho l ≠ 0 ↔ WIL (u + Pi.single l 1) rho) ∧
    (wPlus u rho l = 0 ↔ ∃ i : Fin K, i.succ = l ∧ rho i = u l + 1 / 2)
def LoweringCoefficientVanishing : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ), WInterl u rho → ∀ l,
    (wMinus u rho l ≠ 0 ↔ WIL (u - Pi.single l 1) rho) ∧
    (wMinus u rho l = 0 ↔ ∃ i : Fin K, i.castSucc = l ∧ rho i = u l - 1 / 2)
def RaisingCoefficientLowerBound : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ), WInterl u rho → ∀ l, wPlus u rho l ≠ 0 →
    1 / (max 1 (u 0 - u l) * max 1 (u l - u (Fin.last K))) ≤ wPlus u rho l
def LoweringCoefficientLowerBound : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ), WInterl u rho → ∀ l, wMinus u rho l ≠ 0 →
    1 / (max 1 (u 0 - u l) * max 1 (u l - u (Fin.last K))) ≤ wMinus u rho l
def WignerCoefficientLowerBound : Prop :=
  ∃ C : ℝ, ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (b : ℝ), WInterl u rho → 2 ≤ b →
    (∀ i, |u i| ≤ b) → ∀ l,
      (wPlus u rho l ≠ 0 → b ^ (-C) ≤ wPlus u rho l) ∧ (wMinus u rho l ≠ 0 → b ^ (-C) ≤ wMinus u rho l)
def CoordinateTypesCovered : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin K) (n0 : ℕ), WInterl u rho →
    2 * (n0 : ℝ) + 1 ≤ u l.castSucc - u l.succ →
    WIL (u + Pi.single l.succ (n0 : ℝ)) rho ∨ WIL (u - Pi.single l.castSucc (n0 : ℝ)) rho
def IntermediateParameterOccurs : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin K) (n0 : ℕ), WInterl u rho →
    (WIL (u + Pi.single l.succ (n0 : ℝ)) rho →
      ∀ j : ℕ, j ≤ n0 → WInterl (u + Pi.single l.succ (j : ℝ)) rho) ∧
    (WIL (u - Pi.single l.castSucc (n0 : ℝ)) rho →
      ∀ j : ℕ, j ≤ n0 → WInterl (u - Pi.single l.castSucc (j : ℝ)) rho)
noncomputable def WProdPlus {K : ℕ} (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin K) (n0 : ℕ) : ℝ :=
  ∏ j ∈ range n0, wPlus (u + Pi.single l.succ (j : ℝ)) rho l.succ
noncomputable def WProdMinus {K : ℕ} (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin K) (n0 : ℕ) : ℝ :=
  ∏ j ∈ range n0, wMinus (u - Pi.single l.castSucc (j : ℝ)) rho l.castSucc
def WignerProductLowerBound : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin K) (n0 : ℕ) (b : ℝ), WInterl u rho →
    1 ≤ b → (n0 : ℝ) ≤ b → (∀ i, |u i| ≤ b) →
    (WIL (u + Pi.single l.succ (n0 : ℝ)) rho → ((3 * b) ^ (2 * n0))⁻¹ ≤ WProdPlus u rho l n0) ∧
    (WIL (u - Pi.single l.castSucc (n0 : ℝ)) rho → ((3 * b) ^ (2 * n0))⁻¹ ≤ WProdMinus u rho l n0)
noncomputable def hsSq {m n : Type} [Fintype m] [Fintype n] (X : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖X i j‖ ^ 2
def TypeAdaptedFrobeniusBound : Prop :=
  ∀ (a N p q : ℕ) (J : Matrix (Fin a) (Fin N) ℂ) (Ap : Matrix (Fin N) (Fin p) ℂ) (Am : Matrix (Fin N) (Fin q) ℂ)
    (dp dm : Fin N → ℝ) (c : ℝ), 0 < c →
    Ap * Ap.conjTranspose = Matrix.diagonal (fun i => ((dp i : ℝ) : ℂ)) →
    Am * Am.conjTranspose = Matrix.diagonal (fun i => ((dm i : ℝ) : ℂ)) →
    (∀ i, c ≤ dp i ∨ c ≤ dm i) →
    hsSq J ≤ c⁻¹ * (hsSq (J * Ap) + hsSq (J * Am))
def TypeDecompositionNormBound : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (l : Fin K) (n0 : ℕ) (b G T' : ℝ) (R : Finset (Fin K → ℝ))
    (a : (Fin K → ℝ) → ℝ), (∀ rho ∈ R, WInterl u rho) → (∀ rho ∈ R, 0 ≤ a rho) →
    2 * (n0 : ℝ) + 1 ≤ u l.castSucc - u l.succ → 1 ≤ b → (n0 : ℝ) ≤ b → (∀ i, |u i| ≤ b) → 0 < G → 0 < T' →
    ∑ rho ∈ R, a rho ≤ (3 * b) ^ (2 * n0) * (T' / G) ^ n0 *
      ((G / T') ^ n0 * ∑ rho ∈ R, WProdPlus u rho l n0 * a rho +
        (G / T') ^ n0 * ∑ rho ∈ R, WProdMinus u rho l n0 * a rho)
def WignerNormBound : Prop := CoordinateTypesCovered → WignerProductLowerBound → TypeDecompositionNormBound
def DegRatioMinus : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), Function.Injective μ →
    (∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) → Function.Injective (μ - Pi.single s 1) →
    Formalism.QuantumDeterminants.fdegHC (μ - Pi.single s 1) / Formalism.QuantumDeterminants.fdegHC μ =
      ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s')
def DegVand : Prop :=
  ∀ (n : ℕ) (P : Set (Fin n → ℝ)) (d : (Fin n → ℝ) → ℝ),
    (∀ μ ∈ P, Function.Injective μ ∧ ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) → (∀ μ ∈ P, 0 < d μ) →
    (∀ μ ∈ P, ∀ s, μ + Pi.single s 1 ∈ P →
      d (μ + Pi.single s 1) / d μ = ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')) →
    ∀ μ ν, Relation.EqvGen (fun x y => x ∈ P ∧ y ∈ P ∧ ∃ s, y = x + Pi.single s 1) μ ν → μ ∈ P →
      d μ / Formalism.QuantumDeterminants.fdegHC μ = d ν / Formalism.QuantumDeterminants.fdegHC ν
def DegStepBound : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), Function.Injective μ → (∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) →
    (Function.Injective (μ + Pi.single s 1) →
      1 / (n : ℝ) ≤ ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') ∧
      ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') ≤ n) ∧
    (Function.Injective (μ - Pi.single s 1) →
      1 / (n : ℝ) ≤ ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s') ∧
      ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s') ≤ n)
def DegSetBound : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (I : Finset (Fin n)), StrictAnti μ → (∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) →
    (∀ a b, a < b → 2 ≤ μ a - μ b) →
    ((n : ℝ) ^ I.card)⁻¹ ≤
        Formalism.QuantumDeterminants.fdegHC (fun a => μ a + if a ∈ I then 1 else 0) / Formalism.QuantumDeterminants.fdegHC μ ∧
      Formalism.QuantumDeterminants.fdegHC (fun a => μ a + if a ∈ I then 1 else 0) / Formalism.QuantumDeterminants.fdegHC μ ≤ (n : ℝ) ^ I.card
def NineOneCount : Prop :=
  ∀ n l : ℕ, (powersetCard l (univ : Finset (Fin n))).card ≤ n ^ l
def FormalDegreeAtRoot : Prop :=
  ∀ (n k : ℕ) (μ : Fin n → ℂ) (u u' : Fin k → ℂ) (T T' al alp : ℂ) (s : Fin n),
    (∀ s', s' ≠ s → μ s ≠ μ s') → (∀ s', s' ≠ s → μ s - 1 ≠ μ s') →
    -(alp * ∏ s' ∈ univ.erase s, (μ s' - μ s + 1)) * (al * ∏ s' ∈ univ.erase s, (μ s' - μ s)) =
      -(T * T') * ∏ i, ((-μ s + 1 / 2 + u i) * (-μ s + 1 / 2 + u' i)) →
    alp * al = T * T' * (∏ i, (μ s - 1 / 2 - u i)) * (∏ i, (μ s - 1 / 2 - u' i)) /
      ∏ s' ∈ univ.erase s, ((μ s - μ s') * (μ s - 1 - μ s'))
def FormalDegreeCoefficientIdentity : Prop :=
  ∀ (n k : ℕ) (μ : Fin n → ℝ) (u : Fin k → ℝ) (Tt A : ℝ) (s : Fin n),
    (∀ s', s' ≠ s → μ s ≠ μ s') → (∀ s', s' ≠ s → μ s - 1 ≠ μ s') → 0 ≤ A → 0 ≤ Tt →
    A * A * ∏ s' ∈ univ.erase s, (|μ s - 1 - μ s'| / |μ s - μ s'|) =
      Tt * Tt * (∏ i, |μ s - 1 / 2 - u i|) * (∏ i, |μ s - 1 / 2 - u i|) /
        ∏ s' ∈ univ.erase s, (|μ s - μ s'| * |μ s - 1 - μ s'|) →
    A = Tt * (∏ i, |μ s - 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |μ s - 1 - μ s'|
def FormalDegreeHypotheses (k M : ℕ) (lam mu : Fin (k + M) → ℝ) (u : Fin k → ℝ) (b bv ga q0 : ℝ) : Prop :=
  StrictAnti lam ∧ (∀ a c, ∃ z : ℤ, lam a - lam c = (z : ℝ)) ∧
  (∀ a i, ∃ z : ℤ, lam a - u i = (z : ℝ) + 1 / 2) ∧
  (∀ i : Fin k, lam (Fin.castAdd M i) < u i) ∧
  (∀ i j : Fin k, (i : ℕ) + 1 = (j : ℕ) → u j < lam (Fin.castAdd M i)) ∧
  (∀ a : Fin (k + M), (a : ℕ) + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8) ∧
  (∀ a : Fin (k + M), k ≤ (a : ℕ) + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv) ∧
  (∀ a, |lam a| ≤ b) ∧ (∀ i, |u i| ≤ b) ∧
  (∀ a c : Fin (k + M), a < c → (c : ℕ) + 1 < k → ga ≤ lam a - lam c) ∧ 4 ≤ ga ∧
  (∀ a, ∃ z : ℤ, mu a - lam a = (z : ℝ)) ∧ StrictAnti mu ∧
  ∑ a, |mu a - lam a| ≤ q0 ∧ q0 ≤ ga / 8 ∧ q0 ≤ bv / 4 ∧ q0 ≤ b
def supL2RatioMajorant : Prop :=
  ∀ (k M : ℕ) (lam mu : Fin (k + M) → ℝ) (u : Fin k → ℝ) (b bv ga q0 : ℝ) (s : Fin (k + M)),
    1 ≤ k → 1 ≤ M → FormalDegreeHypotheses k M lam mu u b bv ga q0 → (∀ s', s' ≠ s → mu s - 1 ≠ mu s') →
    (∏ i, |mu s - 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s - 1 - mu s'| ≤
      if (s : ℕ) + 1 < k then 64 * Real.exp 1 * Real.sqrt k * b ^ 3 else 16 * Real.exp 1 * b ^ 2
def ShiftedFormalDegreeBound : Prop :=
  ∀ (k M : ℕ) (lam mu : Fin (k + M) → ℝ) (u : Fin k → ℝ) (b bv ga q0 : ℝ) (s : Fin (k + M)),
    1 ≤ k → 1 ≤ M → FormalDegreeHypotheses k M lam mu u b bv ga q0 → (∀ s', s' ≠ s → mu s + 1 ≠ mu s') →
    (∏ i, |mu s + 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s + 1 - mu s'| ≤
      if (s : ℕ) + 1 < k then 64 * Real.exp 1 * Real.sqrt k * b ^ 3 else 16 * Real.exp 1 * b ^ 2
def FormalDegreeUpperBound' : Prop :=
  ∃ C : ℕ, ∀ (k M : ℕ) (lam mu : Fin (k + M) → ℝ) (u : Fin k → ℝ) (b bv ga q0 T ka : ℝ) (r : ℕ)
    (s : Fin (k + M)),
    1 ≤ k → 1 ≤ M → FormalDegreeHypotheses k M lam mu u b bv ga q0 → (C : ℝ) * ((k + M : ℕ) : ℝ) ^ 7 ≤ bv → 0 ≤ T → 0 ≤ ka →
    ((∀ s', s' ≠ s → mu s - 1 ≠ mu s') →
      T * ka ^ (2 * r) * (∏ i, |mu s - 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s - 1 - mu s'| ≤
        T * ka ^ (2 * r) * b ^ C) ∧
    ((∀ s', s' ≠ s → mu s + 1 ≠ mu s') →
      T * ka ^ (2 * r) * (∏ i, |mu s + 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s + 1 - mu s'| ≤
        T * ka ^ (2 * r) * b ^ C)
def SignCloudRoots : Prop :=
  ∀ (n c : ℕ) (ε : Fin n → Bool), (∀ a : Fin n, (a : ℕ) < c → ε a = true) →
    ∀ s t : Fin n, (s : ℕ) < c → t ≠ s →
      ¬ ∃ N : Fin n → Fin n → ℕ,
        (Pi.single t 1 - Pi.single s 1 : Fin n → ℤ) =
          ∑ a, ∑ b, if a < b ∧ ε a ≠ ε b then (N a b : ℤ) • (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) else 0
def ONormText : Prop :=
  ∀ C1 : ℝ, 0 ≤ C1 → ∃ C : ℝ, 0 < C ∧ ∀ (n j : ℕ) (bv : ℝ), 1 ≤ n → C * (n : ℝ) ^ 7 ≤ bv →
    (j : ℝ) ≤ bv / (C * (n : ℝ) ^ 2) →
    (n : ℝ) * (C1 * bv * ((j : ℝ) + (n : ℝ) ^ 2)) ≤ (bv / 16) ^ 2
def RangeArith : Prop :=
  ∀ c C C1 : ℝ, 0 < c → 0 < C → 0 < C1 → ∃ C' : ℝ, ∀ (k m : ℕ) (h gap : ℝ), 1 ≤ m →
    C' * k * (m : ℝ) ^ ((9 : ℝ) / 2) ≤ h → C' * k * (m : ℝ) ^ 4 ≤ gap →
    C1 * k * (m : ℝ) ^ 4 ≤ min (c * h * (m : ℝ) ^ (-(1 : ℝ) / 2)) gap / C
def BPrimeConstants : Prop :=
  ∀ (C0 Cn : ℕ) (C2 C3 C' : ℝ), 0 ≤ C2 → 0 ≤ C3 → 0 ≤ C' → ∃ C4 C5 : ℝ,
    ∀ (r n0 p : ℕ) (b abelian₂ G : ℝ), 2 ≤ b → 0 < G → 0 ≤ abelian₂ → n0 ≤ Cn * (r + 1) ^ 2 → p ≤ C0 * (r + 1) →
      abelian₂ ≤ b ^ (C' * ((2 * r + 2 : ℕ) : ℝ)) →
      2 * (3 * b) ^ (2 * n0) * (C2 * abelian₂ ^ 2) ^ (r + 1) *
          b ^ (2 * C3 * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p + n0 : ℕ) : ℝ)) * (G ^ (2 * p + n0))⁻¹ ≤
        b ^ (C4 * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * (max 1 (1 / G)) ^ (C5 * ((2 * r + 2 : ℕ) : ℝ) ^ 2)
end PartC
section PartD
open Finset
noncomputable def NormalisingPolynomial (n : ℕ) (a : ℕ → ℝ) (Y : ℝ) : ℝ := ∏ i ∈ range n, (Y + a i)
noncomputable def shiftedAbsProduct (n : ℕ) (lam : ℕ → ℝ) (c Y : ℝ) : ℝ := ∏ s ∈ range n, (|Y + lam s| + c)
noncomputable def denominatorPolynomial (k : ℕ) (T T' : ℝ) (u u'' : ℕ → ℝ) (Y : ℝ) : ℝ :=
  -(T * T') * ∏ i ∈ range k, ((Y + 1 / 2 + u i) * (Y + 1 / 2 + u'' i))
noncomputable def NormalisingDenominator (k : ℕ) (u u'' : ℕ → ℝ) (Y : ℝ) : ℝ :=
  ∏ i ∈ range k, (|Y + 1 / 2 + u i| * |Y + 1 / 2 + u'' i|)
def WeakInterlacing (k : ℕ) (lam u : ℕ → ℝ) : Prop :=
  (∀ i, i < k → lam i < u i) ∧ (∀ i, i + 1 < k → u (i + 1) < lam i)
def InIntCoset (n : ℕ) (a : ℕ → ℝ) (c : ℝ) : Prop := ∀ i, i < n → ∃ z : ℤ, a i = (z : ℝ) + c
structure NormalisationHypotheses (k r : ℕ) (lam u u' : ℕ → ℝ) (b c : ℝ) : Prop where
  lam_coset : InIntCoset (k + 2 * r + 1) lam (((k : ℝ) + 2 * r) / 2)
  u_coset : InIntCoset k u (((k : ℝ) - 1) / 2)
  u'_coset : InIntCoset k u' (((k : ℝ) - 1) / 2)
  interl : WeakInterlacing k lam u
  interl' : WeakInterlacing k lam u'
  lam_le : ∀ s, s < k + 2 * r + 1 → |lam s| ≤ b
  u_le : ∀ i, i < k → |u i| ≤ b
  u'_le : ∀ i, i < k → |u' i| ≤ b
  b_three : 3 ≤ b
  b_k : Real.exp 1 * k ≤ b
  b_c : c + 2 ≤ b
  c_one : 1 ≤ c
  gaps : ∀ s, s + 1 < k + 2 * r + 1 → 2 * c ≤ lam s - lam (s + 1)
def SecondTypeCases (k : ℕ) (u u' u'' : ℕ → ℝ) (j : ℕ) : Prop :=
  (∀ i, i < k → u'' i = u' i) ∨
  ((∀ i, i < k → u' i = u i) ∧ ∃ l n0 : ℕ, l + 1 < k ∧ 2 * (n0 : ℝ) + 1 ≤ u l - u (l + 1) ∧
    ((j = l + 1 ∧ ∀ i, i < k → u'' i = u i + if i = l + 1 then (n0 : ℝ) else 0) ∨
     (j = l ∧ ∀ i, i < k → u'' i = u i - if i = l then (n0 : ℝ) else 0)))
def LiesOnCut (k : ℕ) (u u'' : ℕ → ℝ) (j : ℕ) (Y : ℝ) : Prop :=
  j < k ∧ min (u j) (u'' j) + 2 ≤ -Y ∧ -Y ≤ max (u j) (u'' j) - 2
def CutDenominatorsAtLeastOne : Prop :=
  ∀ (k r : ℕ) (lam u u' u'' : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y →
    ∀ i, i < k → 2 ≤ |Y + u i| ∧ 2 ≤ |Y + u'' i|
def DenominatorPosOnCut : Prop :=
  ∀ (k r : ℕ) (lam u u' u'' : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y T T' : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y → 0 < T → 0 < T' →
    0 < denominatorPolynomial k T T' u u'' Y
def StrictInterlacing (k : ℕ) (u rho : ℕ → ℝ) : Prop := ∀ i, i + 1 < k → rho i < u i ∧ u (i + 1) < rho i
def InterlacingAvoidsCutInterval : Prop :=
  ∀ (k : ℕ) (u u'' rho : ℕ → ℝ) (j : ℕ), j < k → StrictInterlacing k u rho → StrictInterlacing k u'' rho →
    ∀ i, i + 1 < k → rho i < min (u j) (u'' j) ∨ max (u j) (u'' j) < rho i
def InterlacingPolynomialOneSign : Prop :=
  ∀ (k : ℕ) (u u'' rho : ℕ → ℝ) (j : ℕ) (Y Y' d d' : ℝ),
    StrictInterlacing k u rho → StrictInterlacing k u'' rho → LiesOnCut k u u'' j Y → LiesOnCut k u u'' j Y' →
    (d = -1 ∨ d = 0 ∨ d = 1) → (d' = -1 ∨ d' = 0 ∨ d' = 1) →
    0 < NormalisingPolynomial (k - 1) rho (Y + d) * NormalisingPolynomial (k - 1) rho (Y' + d')
def MajorantDominatesPolynomial : Prop :=
  ∀ (n : ℕ) (lam lam' : ℕ → ℝ) (D Y : ℝ), 0 ≤ D → (∀ s, s < n → |lam' s - lam s| ≤ D) →
    |NormalisingPolynomial n lam' Y| ≤ shiftedAbsProduct n lam (D + 1) Y ∧ 1 ≤ shiftedAbsProduct n lam (D + 1) Y
def HarmonicProductBound : Prop :=
  ∀ (K : ℕ) (x : ℝ), 0 ≤ x → x ≤ 1 → ∏ j ∈ range K, (1 + x / ((j : ℝ) + 1)) ≤ (K : ℝ) + 1
def NormalisationSingleBracket : Prop :=
  ∀ (k r : ℕ) (lam u u' u'' : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y d : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y → (d = 0 ∨ d = 1) →
    shiftedAbsProduct (k + 2 * r + 1) lam c (Y + d)
      ≤ (2 + c) ^ 2 * (Real.exp 1 * k) ^ 2 * (3 * b) ^ (2 * r + 2) * ∏ i ∈ range k, |Y + 1 / 2 + u i| ∧
    shiftedAbsProduct (k + 2 * r + 1) lam c (Y + d)
      ≤ (2 + c) ^ 2 * (Real.exp 1 * k) ^ 2 * (3 * b) ^ (2 * r + 3) * ∏ i ∈ range k, |Y + 1 / 2 + u'' i|
def NormalisationConstantsBound : Prop :=
  ∀ (k m : ℕ) (b c : ℝ), 3 ≤ b → Real.exp 1 * k ≤ b → c + 2 ≤ b → 1 ≤ c →
    (2 + c) ^ 4 * (Real.exp 1 * k) ^ 4 * (3 * b) ^ (2 * m + 1) ≤ b ^ (4 * m + 14)
def CloudEntryPairing : Prop :=
  ∀ (k r : ℕ) (lam u u' u'' : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y →
    shiftedAbsProduct (k + 2 * r + 1) lam c Y * shiftedAbsProduct (k + 2 * r + 1) lam c (Y + 1)
      ≤ b ^ (4 * (2 * r + 2) + 14) * NormalisingDenominator k u u'' Y
def MajorantSquareBound : Prop :=
  ∀ (k r : ℕ) (lam u u' u'' : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y →
    shiftedAbsProduct (k + 2 * r + 1) lam c Y ^ 2 ≤ b ^ (4 * (2 * r + 2) + 14) * NormalisingDenominator k u u'' Y
def N1aq : Prop :=
  ∀ (k r : ℕ) (lam u u' u'' : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y T T' : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y → 0 < T → 0 < T' →
    shiftedAbsProduct (k + 2 * r + 1) lam c Y * shiftedAbsProduct (k + 2 * r + 1) lam c (Y + 1) / denominatorPolynomial k T T' u u'' Y
      ≤ b ^ (11 * (2 * r + 2)) / (T * T')
def NormalisationIdentity : Prop :=
  ∃ C : ℝ, ∀ (k r : ℕ) (lam u u' u'' : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y T T' : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y → 1 ≤ T → 1 ≤ T' →
    Real.sqrt (shiftedAbsProduct (k + 2 * r + 1) lam c Y * shiftedAbsProduct (k + 2 * r + 1) lam c (Y + 1) / denominatorPolynomial k T T' u u'' Y)
      ≤ b ^ (C * (2 * (r : ℝ) + 2))
def HalfIntegralInterlacing (k : ℕ) (u rho : ℕ → ℝ) : Prop := ∀ i, i + 1 < k → rho i ≤ u i - 1 / 2 ∧ u (i + 1) + 1 / 2 ≤ rho i
def LiftInputBound : Prop :=
  ∀ (k : ℕ) (u u'' rho : ℕ → ℝ) (j : ℕ) (Y : ℝ), HalfIntegralInterlacing k u rho → HalfIntegralInterlacing k u'' rho → LiesOnCut k u u'' j Y →
    |NormalisingPolynomial (k - 1) rho (Y + 1)| ≤ Real.sqrt (NormalisingDenominator k u u'' Y)
def LiftBlockBoundExplicit : Prop :=
  ∀ (k r : ℕ) (lam u u' u'' rho : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y T T' : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y → HalfIntegralInterlacing k u rho → HalfIntegralInterlacing k u'' rho →
    0 < T → 0 < T' →
    shiftedAbsProduct (k + 2 * r + 1) lam c Y * |NormalisingPolynomial (k - 1) rho (Y + 1)| / denominatorPolynomial k T T' u u'' Y
      ≤ b ^ (6 * (2 * r + 2)) / (T * T')
def LiftBlockPowerBound : Prop :=
  ∃ C : ℝ, ∀ (k r : ℕ) (lam u u' u'' rho : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y T T' : ℝ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y → HalfIntegralInterlacing k u rho → HalfIntegralInterlacing k u'' rho →
    1 ≤ T → 1 ≤ T' →
    shiftedAbsProduct (k + 2 * r + 1) lam c Y * |NormalisingPolynomial (k - 1) rho (Y + 1)| / denominatorPolynomial k T T' u u'' Y
      ≤ b ^ (C * (2 * (r : ℝ) + 2))
def FlagLatticeEnergyBound : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (n : ℕ) (lam : ℕ → ℝ) (lam' : ι → ℕ → ℝ) (e : ι → ℝ) (Yw : κ → ℝ)
    (D sg : ℝ), 0 ≤ D → (sg = 1 ∨ sg = -1) → (∀ x s, s < n → |lam' x s - lam s| ≤ D) → (∀ x, 0 ≤ e x) →
    |∑ x, (∏ a, sg * NormalisingPolynomial n (lam' x) (Yw a)) * e x| ≤ (∏ a, shiftedAbsProduct n lam (D + 1) (Yw a)) * ∑ x, e x
def SpacedProductLowerBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (plus : ι → Bool) (x : ι → ℝ) (N : ℕ), 1 ≤ N → Fintype.card ι ≤ N →
    (∀ a, 4 ≤ |x a|) →
    (∀ t : ℕ, 1 ≤ t → (univ.filter fun a => 4 * (t : ℝ) ≤ |x a| ∧ |x a| < 4 * (t : ℝ) + 4).card ≤ 2) →
    1 / (Real.exp 1 * N) ≤ ∏ a, (if plus a then (x a + 1) / x a else x a / (x a - 1)) ∧
    ∏ a, (if plus a then (x a + 1) / x a else x a / (x a - 1)) ≤ Real.exp 1 * N
def GridLettersSpacing : Prop :=
  ∀ (ι : Type) [Fintype ι] (plus : ι → Bool) (z : ι → ℤ), Function.Injective z → (∀ a, z a ≠ 0) →
    (∀ a, (4 : ℝ) ≤ |if plus a then -5 * (z a : ℝ) else 5 * (z a : ℝ) + 1|) ∧
    ∀ t : ℕ, 1 ≤ t → (univ.filter fun a =>
      4 * (t : ℝ) ≤ |if plus a then -5 * (z a : ℝ) else 5 * (z a : ℝ) + 1| ∧
      |if plus a then -5 * (z a : ℝ) else 5 * (z a : ℝ) + 1| < 4 * (t : ℝ) + 4).card ≤ 2
def ScaleParameterBound : Prop :=
  ∀ C0 C2 : ℝ, 0 ≤ C0 → 0 ≤ C2 → ∃ C : ℝ,
    ∀ (k r : ℕ) (lam u u' u'' : ℕ → ℝ) (b c : ℝ) (j : ℕ) (Y T T' qw : ℝ) (N : ℕ),
    NormalisationHypotheses k r lam u u' b c → SecondTypeCases k u u' u'' j → LiesOnCut k u u'' j Y →
    b ^ (-(C2 * (2 * (r : ℝ) + 2))) ≤ T → b ^ (-(C2 * (2 * (r : ℝ) + 2))) ≤ T' →
    1 ≤ N → (N : ℝ) ≤ b → denominatorPolynomial k T T' u u'' Y / (Real.exp 1 * N) ≤ qw →
    Real.sqrt (C0 * (shiftedAbsProduct (k + 2 * r + 1) lam c Y * shiftedAbsProduct (k + 2 * r + 1) lam c (Y + 1)) / qw)
      ≤ b ^ (C * (2 * (r : ℝ) + 2))
def LeadingPrincipalMinor {R : Type*} [CommRing R] {d : ℕ} (Z : Matrix (Fin d) (Fin d) R) (l : ℕ) (h : l ≤ d) : R :=
  (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det
def LeadingMinorDiagonalScaling : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (Z : Matrix (Fin d) (Fin d) R) (al be : Fin d → R) (l : ℕ) (h : l ≤ d),
    LeadingPrincipalMinor (Matrix.diagonal al * Z * Matrix.diagonal be) l h =
      (∏ a : Fin l, al (Fin.castLE h a) * be (Fin.castLE h a)) * LeadingPrincipalMinor Z l h
noncomputable def HeightScaledMatrix (r : ℕ) (kap tau tau' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.diagonal (fun a : Fin (r + 1) => ((tau * kap ^ (r - (a : ℕ)) : ℝ) : ℂ)) * Z *
    Matrix.diagonal (fun b : Fin (r + 1) => ((tau' * kap ^ (r - (b : ℕ)) : ℝ) : ℂ))
noncomputable def gramDiscriminant (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (T T' : ℝ) : ℝ :=
  Complex.normSq (LeadingPrincipalMinor Z (r + 1) le_rfl) - T * T' * Complex.normSq (LeadingPrincipalMinor Z r (Nat.le_succ r))
def GramCoefficientScaling : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (kap tau tau' : ℝ), 0 < kap → 0 < tau → 0 < tau' →
    ∀ (l0 : ℕ) (h : l0 + 1 ≤ r + 1),
      LeadingPrincipalMinor (HeightScaledMatrix r kap tau tau' Z) (l0 + 1) h / LeadingPrincipalMinor (HeightScaledMatrix r kap tau tau' Z) l0 (Nat.le_of_succ_le h) =
        ((tau * tau' * kap ^ (2 * (r - l0)) : ℝ) : ℂ) * (LeadingPrincipalMinor Z (l0 + 1) h / LeadingPrincipalMinor Z l0 (Nat.le_of_succ_le h))
def GramDiscriminantFrameScaling : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (kap tau tau' T T' : ℝ),
    gramDiscriminant r (HeightScaledMatrix r kap tau tau' Z) (tau ^ 2 * T) (tau' ^ 2 * T') =
      (tau * tau') ^ (2 * (r + 1)) * kap ^ (2 * r * (r + 1)) * gramDiscriminant r Z T T'
def GramDiscriminantScaling : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (kap tau tau' T T' : ℝ), 0 < kap → 0 < tau → 0 < tau' →
    Complex.normSq (LeadingPrincipalMinor (HeightScaledMatrix r kap tau tau' Z) (r + 1) le_rfl /
        LeadingPrincipalMinor (HeightScaledMatrix r kap tau tau' Z) r (Nat.le_succ r)) - (tau ^ 2 * T) * (tau' ^ 2 * T') =
      (tau * tau') ^ 2 *
        (Complex.normSq (LeadingPrincipalMinor Z (r + 1) le_rfl / LeadingPrincipalMinor Z r (Nat.le_succ r)) - T * T')
def UnipotentCoordinateScaling : Prop :=
  ∀ (r : ℕ) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (kap tau : ℝ), 0 < kap → 0 < tau → ∀ a b : Fin (r + 1),
    (Matrix.diagonal (fun a : Fin (r + 1) => (((tau * kap ^ (r - (a : ℕ)))⁻¹ : ℝ) : ℂ)) * X *
      Matrix.diagonal (fun b : Fin (r + 1) => ((tau * kap ^ (r - (b : ℕ)) : ℝ) : ℂ))) a b =
      ((kap ^ (-(((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) : ℝ) : ℂ) * X a b
def FrameScaleProduct : Prop :=
  ∀ (r : ℕ) (kap tau : ℝ), 0 < kap → 0 < tau →
    ∏ l ∈ range (r + 1), ((tau ^ 2 * kap ^ (2 * (r - l))) ^ 2)⁻¹ =
      (tau ^ (4 * (r + 1)))⁻¹ * (kap ^ (2 * r * (r + 1)))⁻¹
def RootHeightsSum : Prop :=
  ∀ s : ℕ, ∑ b ∈ range s, ∑ a ∈ range b, ((b : ℚ) - a) = ((s : ℚ) ^ 3 - s) / 6
def StabiliserRootCount : Prop :=
  ∀ (r : ℕ) (c : Composition (r + 1)),
    2 * (c.blocks.map fun s : ℕ => (s : ℤ) * ((s : ℤ) - 1) / 2).sum ≤ (r : ℤ) * (r + 1) ∧
    (c.blocks.map fun s : ℕ => (s : ℤ) * ((s : ℤ) - 1) / 2).sum ≤ (r : ℤ) ^ 2
def dimensionIndex (k r l : ℚ) : ℚ := k + 1 + 2 * (r + 1 - l)
def BlockIndexRelations : Prop :=
  ∀ k r i j s x : ℚ, j = i - 1 + s →
    dimensionIndex k r (j - x) = dimensionIndex k r j + 2 * x ∧ dimensionIndex k r (r + 1) = k + 1 ∧
    (∀ a b : ℚ, a + b = i + j → (r + 1 - a) + (r + 1 - b) = 2 * (r + 1 - j) + s - 1) ∧
    2 * s * (k - 1) + 4 * s * (r + 1 - j) + 2 * s * (s - 1) = 2 * s * (dimensionIndex k r j + s - 3)
def kappaExponentFirst (s : ℕ) (A M : ℚ) : ℚ := 2 * s * (M + s - 3) * (2 * A + s - 1)
def kappaExponentSecond (s : ℕ) (A M : ℚ) : ℚ := ∑ x ∈ range s, 2 * (M - 1 + 2 * x) * (2 * (A + x))
def SecondPowerCoefficientFormula : Prop :=
  ∀ (s : ℕ) (A M : ℚ),
    kappaExponentSecond s A M = 2 * s * (M - 1) * (2 * A + s - 1) + 4 * A * s * (s - 1) + 8 * ∑ x ∈ range s, (x : ℚ) ^ 2
def KappaExponentDifference : Prop :=
  ∀ (s : ℕ) (A M : ℚ), kappaExponentSecond s A M - kappaExponentFirst s A M = 4 * A * s + s * (s - 1) * (2 * s + 8) / 3
def KappaExponentTotal : Prop :=
  ∀ (s : ℕ) (A M : ℚ),
    kappaExponentFirst s A M + 2 * ((s : ℚ) ^ 3 - s) / 3 - kappaExponentSecond s A M = -4 * A * s - 2 * s * (s - 1) ∧
    -4 * A * s - 2 * s * (s - 1) = -∑ x ∈ range s, 4 * (A + x)
def TauExponentBlock : Prop :=
  ∀ (s : ℕ) (M : ℚ),
    ∑ x ∈ range s, 4 * (M - 1 + 2 * x) = 4 * s * (M + s - 2) ∧
    4 * s * (M + s - 3) - ∑ x ∈ range s, 4 * (M - 1 + 2 * x) = -4 * s
def TauExponentCentralBlock : Prop :=
  ∀ (s : ℕ) (k : ℚ), 2 ≤ s →
    (∑ x ∈ Ico 1 s, 4 * (k + 2 * x)) + 4 * (k - 1) + 4 = 4 * s * (k + s - 1) ∧
    4 * s * (k + s - 2) - ((∑ x ∈ Ico 1 s, 4 * (k + 2 * x)) + 4 * (k - 1) + 4) = -4 * s
def TauExponentUnitBlock : Prop := ∀ k : ℚ, 4 * (k - 1) - 4 * k = -4 * 1
noncomputable def F2la (r : ℕ) (kap th : ℝ) (l : ℕ) : ℝ := th * kap ^ (2 * ((r : ℝ) + 1 - l))
noncomputable def dimensionIndexReal (k r l : ℕ) : ℝ := (k : ℝ) + 1 + 2 * ((r : ℝ) + 1 - l)
noncomputable def CompositionWeightExponent (k r : ℕ) (c : Composition (r + 1)) (a : Fin c.length) : ℝ :=
  2 * (c.blocksFun a : ℝ) * (dimensionIndexReal k r (c.sizeUpTo ((a : ℕ) + 1)) + (c.blocksFun a : ℝ) - 3)
def BlockWeightExponent : Prop :=
  ∀ (k r s j : ℕ) (kap th : ℝ), 0 < kap → 0 < th → s ≤ j → j ≤ r + 1 →
    (th * kap ^ (2 * ((r : ℝ) + 1 - j) + (s : ℝ) - 1)) ^ (2 * (s : ℝ) * (dimensionIndexReal k r j + (s : ℝ) - 3)) *
        kap ^ (2 * ((s : ℝ) ^ 3 - (s : ℝ)) / 3) /
        ∏ x ∈ range s, F2la r kap th (j - x) ^ (2 * (dimensionIndexReal k r (j - x) - 1)) =
      ∏ x ∈ range s, F2la r kap th (j - x) ^ (-2 : ℝ)
def FrameMeasureFormula : Prop :=
  ∀ (k r : ℕ) (c : Composition (r + 1)) (kap th DD : ℝ) (wt wt' : Fin c.length → ℝ) (Jg Jg' Jn Jn' : ℝ),
    0 < kap → 0 < th → 0 < DD → (∀ a, 0 < wt a) → 0 ≤ Jg → 0 < Jn →
    (∀ a, wt' a = th * kap ^ (2 * ((r : ℝ) + 1 - c.sizeUpTo ((a : ℕ) + 1)) + (c.blocksFun a : ℝ) - 1) * wt a) →
    Jg' = DD ^ 2 * (∏ a, kap ^ (2 * ((c.blocksFun a : ℝ) ^ 3 - (c.blocksFun a : ℝ)) / 3)) * Jg →
    Jn' = DD ^ 2 * (∏ l ∈ Icc 1 r, F2la r kap th l ^ (2 * (dimensionIndexReal k r l - 1))) * th ^ (2 * (k : ℝ)) * Jn →
    (∏ a, wt' a ^ CompositionWeightExponent k r c a) * Jg' / Jn' =
      (∏ l ∈ Icc 1 (r + 1), F2la r kap th l ^ (-2 : ℝ)) * ((∏ a, wt a ^ CompositionWeightExponent k r c a) * Jg / Jn)
def UnitFrameProperties : Prop :=
  ∀ (r : ℕ) (ka : ℝ), 0 < ka →
    (∀ a, a ≤ r → ka ^ r * (ka⁻¹) ^ (r - a) = ka ^ a) ∧
    (ka ^ r) ^ 2 = ka ^ (2 * r) ∧
    (ka ^ r * ka ^ r) ^ (2 * (r + 1)) * (ka⁻¹) ^ (2 * r * (r + 1)) = ka ^ (2 * r * (r + 1)) ∧
    ((ka ^ r) ^ (4 * (r + 1)))⁻¹ * ((ka⁻¹) ^ (2 * r * (r + 1)))⁻¹ = (ka ^ (2 * r * (r + 1)))⁻¹
def FrameChangeFactorSize : Prop :=
  ∀ C0 : ℝ, 0 ≤ C0 → ∃ C : ℝ, ∀ (r : ℕ) (b kap tau : ℝ), 1 ≤ b → 0 < kap → 0 < tau →
    kap ≤ b ^ C0 → kap⁻¹ ≤ b ^ C0 →
    tau ^ 2 ≤ b ^ (C0 * (2 * (r : ℝ) + 2)) → (tau ^ 2)⁻¹ ≤ b ^ (C0 * (2 * (r : ℝ) + 2)) →
    b ^ (-(C * (2 * (r : ℝ) + 2) ^ 2)) ≤ (tau ^ (4 * (r + 1)))⁻¹ * (kap ^ (2 * r * (r + 1)))⁻¹ ∧
    (tau ^ (4 * (r + 1)))⁻¹ * (kap ^ (2 * r * (r + 1)))⁻¹ ≤ b ^ (C * (2 * (r : ℝ) + 2) ^ 2)
def MaxInvGramScaling : Prop :=
  ∀ (C0 C1 m b ph G : ℝ), 0 ≤ C0 → 0 ≤ C1 → 0 ≤ m → 1 ≤ b → 0 < ph → 0 < G → ph⁻¹ ≤ b ^ (C0 * m ^ 2) →
    max 1 (1 / (ph * G)) ^ (C1 * m ^ 2) ≤ b ^ (C0 * C1 * m ^ 4) * max 1 (1 / G) ^ (C1 * m ^ 2)
end PartD
end Formalism.HermitianLatticeCounting.ExpansionTerms


