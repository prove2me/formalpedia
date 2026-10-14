-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0124
-- name    : PNT_ZeroFree_433_0124
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:10:41.44531+00:00
-- url     : https://prove2.me/theorems/459eb4fe-53a7-4e6a-974f-d98aa04bd899
-- title:
--   Zero-free region foundations: Eisenstein.QuotientTopology [0124]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.QuotientTopology
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/QuotientTopology.lean#L81-L732

import Definitions.Def_PNT_ZeroFree_433_0120
import Definitions.Def_PNT_ZeroFree_433_0122
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/QuotientTopology.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators


namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory


open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label)
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (outerWindow)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})


theorem globalSecondRawSource_eq
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (q : Ideal O × Ideal O × Ideal O) (hfixed : ∀ x∈s,globalSecondFixedTriple p x=q)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) (hR : 0 < R) :
    globalSecondRawSource p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ (fixedTripleMask m q)
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R := by
  obtain ⟨C,hC,hsep⟩ := postCommonSmoothPair_uniform_fixed_tests p hp hcop hg A₁ A₂ W V M hM hV 0 0
  obtain ⟨b,hb,hid⟩ := hsep R hR
  unfold globalSecondRawSource globalSecondSource
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg (fun a : ℂ => w x * a)
  rw [hid (globalSecondRawPool F x) Ψ₁ Ψ₂ (globalSecondRawMask p m x) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂,
    hid F Ψ₁ Ψ₂ (fixedTripleMask m q) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂]
  simp only [separatedPostCommon,globalSecondRawPool,globalSecondRawMask,
    globalSecondRawRow_fixed_pool p hp hcop hg hinj,hfixed x hx]

theorem globalSecondRawSource_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ (R : ℝ),0 < R → ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondRawSource p hp hcop hg s w F Ψ₁ Ψ₂ m
          A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := globalSecondSource_uniform_transfer p hp hcop hg hinj
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  rw [globalSecondRawSource_eq p hp hcop hg hinj A₁ A₂ W V M hM hV s w q hfixed
    F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ R hR]
  exact htrans R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw

end


end SecondPassArithmetic

end

end OAI

end


