-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1
-- name    : PNT_ZeroFree_433_0260_parallel2_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:17:23.951432+00:00
-- url     : https://prove2.me/theorems/57b8bb4f-0105-4515-901c-41c211144ed0
-- title:
--   Zero-free region foundations: Eisenstein.SourceMellinInversion [0260_parallel2_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceMellinInversion.lean#L346-L433

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0019
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0197_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceMellinInversion.lean
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical


open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss


open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

abbrev CompletedMellinIndex := NonzeroIdeal×NonzeroIdeal

def completedMellinLength (p : CompletedMellinIndex) : ℝ :=
  (Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3

def completedMellinCoefficient (Ψ : ActualEisensteinCubic.O→*ℂ) (p : CompletedMellinIndex) : ℂ :=
  columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*cubeWeight Ψ p.2.1

lemma nonzeroIdeal_norm_pos (I : NonzeroIdeal) : 0<(Ideal.absNorm I.1:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>I.2 (Ideal.absNorm_eq_zero_iff.mp h))

lemma completedMellinLength_pos (p : CompletedMellinIndex) : 0<completedMellinLength p :=
  mul_pos (nonzeroIdeal_norm_pos p.1) (pow_pos (nonzeroIdeal_norm_pos p.2) 3)

lemma completedMellinCoefficient_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (p : CompletedMellinIndex) : ‖completedMellinCoefficient Ψ p‖≤1 := by
  rw [completedMellinCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_right (columnWeight_div_sqrt_norm_le_one Ψ hΨ p.1.1)
    (norm_nonneg _)).trans (by simpa only [one_mul] using cubeWeight_norm_le_one Ψ hΨ p.2.1)

lemma nonzeroIdeal_norm_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun I : NonzeroIdeal=>(Ideal.absNorm I.1:ℝ)^(-σ)) := by
  have h := (fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ)).subtype (fun I=>I≠0)
  apply h.congr
  intro I
  change ‖fullIdealWeight (σ:ℂ) I.1‖=(Ideal.absNorm I.1:ℝ)^(-σ)
  rw [fullIdealWeight,if_neg I.2]
  simpa only [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (nonzeroIdeal_norm_pos I) (-(σ:ℂ)))

lemma completedMellinLength_rpow (p : CompletedMellinIndex) (σ : ℝ) :
    (completedMellinLength p)^(-σ)=
      (Ideal.absNorm p.1.1:ℝ)^(-σ)*(Ideal.absNorm p.2.1:ℝ)^(-(3*σ)) := by
  rw [completedMellinLength,Real.mul_rpow (nonzeroIdeal_norm_pos p.1).le
    (pow_nonneg (nonzeroIdeal_norm_pos p.2).le _),←Real.rpow_natCast_mul (nonzeroIdeal_norm_pos p.2).le]
  congr 1
  congr 1
  ring

theorem completedMellinCoefficient_summable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (σ : ℝ) (hσ : 1<σ) :
    Summable (fun p=>‖completedMellinCoefficient Ψ p‖*(completedMellinLength p)^(-σ)) := by
  have hI := nonzeroIdeal_norm_rpow_summable σ hσ
  have hJ := nonzeroIdeal_norm_rpow_summable (3*σ) (by linarith)
  have hp := hI.mul_of_nonneg hJ (fun I=>Real.rpow_nonneg (nonzeroIdeal_norm_pos I).le _)
    (fun J=>Real.rpow_nonneg (nonzeroIdeal_norm_pos J).le _)
  apply hp.of_nonneg_of_le
  · intro p; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (completedMellinLength_pos p).le _)
  · intro p
    rw [←completedMellinLength_rpow]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (completedMellinLength_pos p).le _)
      (completedMellinCoefficient_norm_le_one Ψ hΨ p)

def completedDirichletSeries (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) : ℂ :=
  ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
    (completedMellinLength p:ℂ)^(1/2-s)

theorem completedT_eq_mellin_index (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=∑'p : CompletedMellinIndex,
      completedMellinCoefficient Ψ p*Vstar W (completedMellinLength p/X) := by
  have hfull := completedT_summable Ψ W hW X hX
  have hinj : Function.Injective (fun p : CompletedMellinIndex=>(p.1.1,p.2.1)) := by
    intro p q h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hsub := hfull.comp_injective hinj
  calc
    completedT Ψ W X=∑'I : NonzeroIdeal,∑'J : Ideal ActualEisensteinCubic.O,summand Ψ W X I.1 J := by
      symm
      unfold completedT
      apply tsum_subtype_eq_of_support_subset
        (s:={I:Ideal ActualEisensteinCubic.O|I≠0}) (f:=fun I:Ideal ActualEisensteinCubic.O=>∑'J:Ideal ActualEisensteinCubic.O,summand Ψ W X I J)
      intro I hI hz
      subst I
      exact hI (by simp only [summand_zero_left,tsum_zero])
    _=∑'I : NonzeroIdeal,∑'J : NonzeroIdeal,summand Ψ W X I.1 J.1 := by
      apply tsum_congr
      intro I
      symm
      apply tsum_subtype_eq_of_support_subset
        (s:={J:Ideal ActualEisensteinCubic.O|J≠0}) (f:=fun J:Ideal ActualEisensteinCubic.O=>summand Ψ W X I.1 J)
      intro J hJ hz
      subst J
      exact hJ (summand_zero_right Ψ W X I.1)
    _=∑'p : CompletedMellinIndex,summand Ψ W X p.1.1 p.2.1 := hsub.tsum_prod.symm
    _=_ := rfl


end


end CompletedGauss


end

end OAI

end


