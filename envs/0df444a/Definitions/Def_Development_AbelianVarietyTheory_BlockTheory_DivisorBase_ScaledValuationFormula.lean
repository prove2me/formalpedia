-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledValuationFormula
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledValuationFormula
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:57.121801+00:00
-- url     : https://prove2.me/theorems/7ec13a40-73a2-4823-9a39-94fa0dee5209
-- title:
--   Scaled Valuation Formula
-- statement:
--   Definitions and structural lemmas for Scaled Valuation Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ScaledValuationFormula.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula
open Formalism.DivisionValues Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K]
def primePow (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
def scaledAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) (B : Submodule (𝓞 K) (Fin d → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (primePow w n) B)
def ValGE_vw {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) (Fin d → K)) (y : Fin d → K)
    (c : ℝ) : Prop :=
  ∃ n : ℤ, c ≤ (n : ℝ) ∧ y ∈ scaledAt w n B
def DenLE_vw {d d' : ℕ} (w : HeightOneSpectrum (𝓞 K)) (φ : Matrix (Fin d') (Fin d) K)
    (A : Submodule (𝓞 K) (Fin d → K)) (B : Submodule (𝓞 K) (Fin d' → K)) (c : ℝ) : Prop :=
  ∃ a : ℤ, (a : ℝ) ≤ c ∧ ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A, φ.mulVec x ∈ scaledAt w (-a) B
def dualCoord {d : ℕ} (MM : Submodule (𝓞 K) (Fin d → K)) : Submodule (𝓞 K) (Fin d → K) where
  carrier := {y | ∀ x ∈ MM, y ⬝ᵥ x ∈ Set.range (algebraMap (𝓞 K) K)}
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    rintro y z hy hz x hx
    obtain ⟨a, ha⟩ := hy x hx
    obtain ⟨c, hc⟩ := hz x hx
    exact ⟨a + c, by rw [map_add, ha, hc, add_dotProduct]⟩
  smul_mem' := by
    rintro r y hy x hx
    obtain ⟨a, ha⟩ := hy x hx
    exact ⟨r * a, by rw [map_mul, ha, smul_dotProduct, Algebra.smul_def]⟩
def bound (C f m N L b Sig0 : ℝ) : ℝ :=
  C * f * b * N * m * (m * L + m * Sig0) + C * f * m ^ 2 * N ^ 2 * (L + Sig0) * b
def sigZero {P : Type} (S0 : Finset P) (e q : P → ℕ) : ℝ := ∑ v ∈ S0, (e v : ℝ) * Real.log (q v : ℝ)
variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
def ClauseA (S : IndefData Df) {d : ℕ} (MV : Submodule (𝓞 K) (Fin d → K))
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (dF : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Df.Mt (S.μ w)),
    ValGE_vw w MV ((v (S.μ w)).mulVec F) (-dF w)
def FormulaTwo (S : IndefData Df) {d : ℕ} (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K)
    (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), r (S.μ w) ≠ 0 ∧
    PSI * S.ι (S.μ w) * Df.Pq (S.μ w) = (r (S.μ w))⁻¹ • v (S.μ w)
def ClauseAConsequence (S : IndefData Df) {d : ℕ} (MV : Submodule (𝓞 K) (Fin d → K))
    (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K) (dF : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), DenLE_vw w PSI S.RR MV ((vw w (r (S.μ w)) : ℝ) + dF w)
omit [StarRing K] in

def ClauseB (dF : HeightOneSpectrum (𝓞 K) → ℝ) (B : ℝ) : Prop :=
  (Function.support dF).Finite ∧ ∑ᶠ w : HeightOneSpectrum (𝓞 K), 2 * lw w * dF w ≤ B
def DenominatorsLE (S : IndefData Df) [∀ t, Submodule.IsLattice K (Df.Mt t)] {d : ℕ}
    (MV : Submodule (𝓞 K) (Fin d → K)) [Submodule.IsLattice K MV]
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (B : ℝ) : Prop :=
  ∃ dF : HeightOneSpectrum (𝓞 K) → ℝ,
    ClauseA S MV v dF ∧
    (∀ (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K), FormulaTwo S v PSI r → ClauseAConsequence S MV PSI r dF) ∧
    ClauseB dF B
def FP (S : IndefData Df) [∀ t, Submodule.IsLattice K (Df.Mt t)] {d : ℕ}
    (MV : Submodule (𝓞 K) (Fin d → K)) [Submodule.IsLattice K MV]
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (C : ℝ) (f m N : ℕ) (L b Sig0 : ℝ) : Prop :=
  DenominatorsLE S MV v (bound C f m N L b Sig0)
def LatticeValuationBound' (S : IndefData Df) [∀ t, Submodule.IsLattice K (Df.Mt t)] {d : ℕ}
    (MM : Submodule (𝓞 K) (Fin d → K)) [Submodule.IsLattice K (dualCoord MM)]
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (C : ℝ) (f m N : ℕ) (L : ℝ)
    {P : Type} (S0 : Finset P) (e q : P → ℕ) : Prop :=
  FP S (dualCoord MM) v C f m N L (Real.exp L) (sigZero S0 e q)
def FPFamily (Ix : ℝ → Type) (K : ∀ x, Ix x → Type) [∀ x i, Field (K x i)] [∀ x i, NumberField (K x i)]
    [∀ x i, StarRing (K x i)] (Bs : ∀ x i, DefBase (K x i)) (Df : ∀ x i, DefSide (Bs x i))
    (S : ∀ x i, IndefData (Df x i)) [∀ x i t, Submodule.IsLattice (K x i) ((Df x i).Mt t)]
    (d : ∀ x, Ix x → ℕ) (MV : ∀ x i, Submodule (𝓞 (K x i)) (Fin (d x i) → K x i))
    [∀ x i, Submodule.IsLattice (K x i) (MV x i)]
    (v : ∀ x i t, Matrix (Fin (d x i)) (Fin ((Df x i).nV t)) (K x i))
    (f m N : ∀ x, Ix x → ℕ) (L b Sig0 : ∀ x, Ix x → ℝ) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Ix x,
    FP (S x i) (MV x i) (v x i) C (f x i) (m x i) (N x i) (L x i) (b x i) (Sig0 x i)
end GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula


