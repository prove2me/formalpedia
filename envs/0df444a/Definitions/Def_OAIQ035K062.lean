-- Prove2me | Definitions.Def_OAIQ035K062
-- name    : OAIQ035K062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:15:03.707586+00:00
-- url     : https://prove2.me/theorems/dcde3a8d-1daf-414c-98e6-716bf76129bb
-- title:
--   Definitions bundle OAIQ035K062 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 62 declarations of OpenAI's Lean: 41 definitions, 1 inductive type or structure and 20 theorems. The definitions and types are `OAI.MetricKMedian.Instance.computedPseudo`, `OAI.MetricKMedian.Instance.fractionalRound`, `OAI.MetricKMedian.Instance.nonzeroRound`, `OAI.MetricKMedian.InstanceProgram.fractionalInput`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input`, `OAI.MetricKMedian.Preparation.FractionalRefinement.scan`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.law`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.tables`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Input.encode`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Input.raw`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.view`, `OAI.MetricKMedian.Preparation.RationalUnitInput.scan`, `OAI.MetricKMedian.SparseBundles.Program.columnsProgram`, `OAI.MetricKMedian.SparseGridRounding.Program.Input.encode`, `OAI.MetricKMedian.SparseOuterLaw.Program.Raw`, `OAI.MetricKMedian.SparseOuterLaw.law`, `OAI.MetricKMedian.SparsePrepared.Program.Input.ker`, `OAI.MetricKMedian.SparsePrepared.Program.Input.kernels`, `OAI.MetricKMedian.SparsePrepared.Program.Input.μ`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.encode`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.raw`, `OAI.MetricKMedian.SparsePrepared.Program.KernelRaw`, `OAI.MetricKMedian.SparsePrepared.Program.StateRaw`, `OAI.MetricKMedian.SparsePrepared.Program.activationData`, `OAI.MetricKMedian.SparsePrepared.Program.bundleData`, `OAI.MetricKMedian.SparsePrepared.Program.pieces`, `OAI.MetricKMedian.SparsePrepared.Program.totalData`, `OAI.MetricKMedian.SparsePrepared.law`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.encode`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.raw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput.raw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelRaw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Raw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.StateRaw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.attach`, `OAI.MetricKMedian.SparseSignedPreparation.Program.beta`, `OAI.MetricKMedian.SparseSignedPreparation.Program.inputRows`, `OAI.MetricKMedian.SparseSignedPreparation.Program.view`, `OAI.MetricKMedian.SparseSignedPreparation.law` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_RationalFractionalScan`, `KMedian_Geometry_RationalUnitScan`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Process_CountListOperations`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_InstanceComputedPseudo`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_InstanceFractionalRound`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Rounding_TargetSubsetProgram`, `KMedian_Sparse_SparseBernoulliRun`, `KMedian_Sparse_SparseBernoulliSubsets`, `KMedian_Sparse_SparseBernoulliSupport`, `KMedian_Sparse_SparseCountRun`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseSignedRounding`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K005`, `OAIQ035K006`, `OAIQ035K007`, `OAIQ035K008`, `OAIQ035K009`, `OAIQ035K010`, `OAIQ035K014`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K027`, `OAIQ035K029`, `OAIQ035K030`, `OAIQ035K031`, `OAIQ035K032`, `OAIQ035K038`, `OAIQ035K039`, `OAIQ035K041`, `OAIQ035K046`, `OAIQ035K047`, `OAIQ035K050`, `OAIQ035K051`, `OAIQ035K055`, `OAIQ035K056` and `OAIQ035K057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K066`, `OAIQ035K067` and `OAIQ035K068`; the statements `OAI.MetricKMedian.Instance.computedPseudo_spec`, `OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec` and `OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec`; the proofs of `OAI.MetricKMedian.Instance.computedPseudo_spec`, `OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec`, `OAI.MetricKMedian.SparseBernoulli.count_mean`, `OAI.MetricKMedian.SparseBernoulli.quadratic_variance`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_lower` and `OAI.MetricKMedian.SparseEnumeratedBatch.pair_le`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K007
import Definitions.Def_OAIQ035K008
import Definitions.Def_OAIQ035K009
import Definitions.Def_OAIQ035K010
import Definitions.Def_OAIQ035K014
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K019
import Definitions.Def_OAIQ035K020
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K022
import Definitions.Def_OAIQ035K027
import Definitions.Def_OAIQ035K029
import Definitions.Def_OAIQ035K030
import Definitions.Def_OAIQ035K031
import Definitions.Def_OAIQ035K032
import Definitions.Def_OAIQ035K038
import Definitions.Def_OAIQ035K039
import Definitions.Def_OAIQ035K041
import Definitions.Def_OAIQ035K046
import Definitions.Def_OAIQ035K047
import Definitions.Def_OAIQ035K050
import Definitions.Def_OAIQ035K051
import Definitions.Def_OAIQ035K055
import Definitions.Def_OAIQ035K056
import Definitions.Def_OAIQ035K057

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem run_spec (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    let μ := run (d := d) p hp n
    μ.length ≤ (n+1)^d+1 ∧ ∀ f : Fin d → Fin (n+1),
      μ.moment (fun q => monomial q f)=∏ i ∈ used f, p i := by
  refine ⟨run_length p hp n,fun f => ?_⟩
  rw [run_moment p hp n (le_refl n) f]
  simp only [target,Fin.isLt,ite_eq_left]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem subset_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    (run (d := d) p hp n).moment (fun q => ∏ i ∈ S, flag q i)=∏ i ∈ S, p i := by
  have hh := (run_spec (d := d) p hp).2 (tuple S)
  simpa only [monomial,used_tuple S hS] using hh

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCounts
open Finset
variable {n m : ℕ}

theorem run_length (ν : Fin m → SparseIntegerLaw ((Fin n → ℕ))) (t : ℕ) :
    (run ν t).length ≤ n*m+(n*m)*(n*m)+1 := by
  induction t with
  | zero => change 1 ≤ _; omega
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · exact ((run ν t).prodCompress_spec (ν ⟨t,ht⟩)
        (fun G S => next G S ⟨t,ht⟩) features).1
    · exact ih

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem single_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (i : Fin n) : (run (d := 2) p hp n).moment (fun q => flag q i)=p i := by
  simpa only [prod_singleton] using subset_moment p hp {i} (by simp : ({i} : Finset (Fin n)).card ≤ 2)

theorem fixed (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (a : Fin (run (d := 2) p hp n).length) (i : Fin n) (hi : p i=0 ∨ p i=1) :
    flag (run (d := 2) p hp n).states[a.val] i=p i := by
  have hm := single_moment p hp i
  rcases hi with hi | hi
  · have hh := (run (d := 2) p hp n).zero_indicator (fun q => q i=true)
      (hm.trans hi) a (run_positive p hp n a)
    simp only [flag,ite_eq_right hh,hi]
  · have hh := (run (d := 2) p hp n).one_indicator (fun q => q i=true)
      (hm.trans hi) a (run_positive p hp n a)
    simp only [flag,ite_eq_left hh,hi]

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedTerminal
open Finset RationalWeightedStep RationalSignedStep
variable {n : ℕ}

theorem terminal_spec (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (hpair : ¬Active u p)
    (a : Fin (terminal u p hp).length) :
    let q := (terminal u p hp).states[a.val]
    (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧ (fractional q).card ≤ 1 ∧
    (∑ i, u i*point q i) ≤ (∑ i, u i*point p i)+1 := by
  dsimp only
  change Fin (SparseBernoulli.run (d := 2) (point p) hp n).length at a
  have he := SparseIntegerLaw.map_states (SparseBernoulli.run (d := 2) (point p) hp n) (state u p) a
  change (terminal u p hp).states[a.val]=_ at he
  rw [he]
  apply state_spec u p hp hu hpair
  intro i hi
  apply SparseBernoulli.fixed _ hp a i
  have hr := MarginalRounding.nonfractional_integral
    (fun i => by change 0 ≤ (point p i : ℝ); exact_mod_cast (hp i).1 : ∀ i, 0 ≤ realPoint p i)
    (fun i => by change (point p i : ℝ) ≤ 1; exact_mod_cast (hp i).2 : ∀ i, realPoint p i ≤ 1)
    (show i ∉ MarginalRounding.fractional (realPoint p) by simpa only [real_fractional] using hi)
  change (point p i : ℝ)=0 ∨ (point p i : ℝ)=1 at hr
  exact_mod_cast hr

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

theorem round_invariants (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (hu : ∀ i, 0 < u i → u i ≤ 1)
    (a : Fin (round u p hp).length) :
    let q := (round u p hp).states[a.val]
    (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧ (fractional q).card ≤ 1 ∧
    (∑ i, u i*point q i) ≤ (∑ i, u i*point p i)+1 := by
  obtain ⟨b,c,hbc⟩ := ((SparseSignedPartial.run u p n).bindCompress_spec
    (kernel u p hp) features).2.1 a
  dsimp only
  change (round u p hp).states[a.val]=_ at hbc
  rw [hbc]
  have hh := RationalSignedTerminal.terminal_spec u (SparseSignedPartial.run u p n).states[b.val]
    (SparseSignedPartial.run_invariants u p hp n b).1 hu
    (SparseSignedPartial.run_terminal u p hp b) c
  dsimp only at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.trans_eq
    (congrArg (fun z : ℚ => z+1) (SparseSignedPartial.run_invariants u p hp n b).2.1)⟩

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

def law (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) :
    SparseIntegerLaw (State n m) :=
  let μ := SparseSignedRounding.round (signed D c) p hp
  μ.bindIndexed (fun a => kernel D μ.states[a.val]
    (SparseSignedRounding.round_invariants (signed D c) p hp (fun e _ =>
      (sub_le_self _ (Nat.cast_nonneg _)).trans (hc e).2) a).1)

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

abbrev law (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) : SparseIntegerLaw (State n m) :=
  SparseSignedPreparation.law D c (fraction q) (SparseGridRounding.fraction_unit q hq) hc

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

def law (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) :
    SparseIntegerLaw (State n m × SparseCounts.Table f n) :=
  (SparseOuterLaw.law D c q hc hq).bindIndexed
    (fun a => kernel D q Δ P y p (SparseOuterLaw.law D c q hc hq).states[a.val])

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

def law := SparsePrepared.law (RationalSuppliers.D D.A) a
  (q D.y D.P D.A D.c D.γ qR.g) qR.Δ D.P D.y D.p a_bounds
  (q_nonneg D.y D.P D.A D.c D.γ qR.g D.hy D.hc0 D.hγ.le (FixedParameters.positive qR).le)

def tables : List (Fin (f+n*f) → ℕ) :=
  (D.law qR).states.toList.map (counts D.y D.P D.A D.c D.γ qR.g)

def scan (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ) (B : ℚ) :=
  qR.roundList df dc (original (f:=f) (n:=n)) (D.tables qR) B

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalUnitScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalUnitInput
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (U : RationalUnitInput f j) (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ)

def scan (B : ℚ) : Option (Finset (Fin f)) := (U.suppliers R p).scan p.round U.df U.dc B

end MetricKMedian.Preparation.RationalUnitInput
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalFractionalScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c b, dist (client c) (i b)=(dc c b:ℝ))
    (hcc : ∀ c c', dist (client c) (client c')=(dd c c':ℝ))
    {η τ : ℝ} (p : RationalAllParameters η τ)

def scan (B : ℚ) : Option (Finset (Fin f)) :=
  let U := unitInput a k ha hj dc dd df hdc hdd hds
  let R := realization a k ha hj dc dd df hdc hdd hds i client hdf hc hcc
  (U.scan R p B).map (fun O => O.image (original a k ha hj dc))

end MetricKMedian.Preparation.FractionalRefinement
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)

 theorem outsideData_view {f n : ℕ} (S : Data f n) (i : Fin f) :
    outsideData (supplierView S) i.val=decide (i∈SupplierStars.outside S.P) := by
  apply Bool.eq_iff_iff.mpr
  simp only [outsideData,supplierView,List.all_map,Function.comp_def,id_eq,List.all_eq_true,List.mem_ofFn,
    forall_exists_index,forall_apply_eq_imp_iff,setView,List.getElem?_ofFn,dite_eq_left i.isLt,
    Option.getD_some,Fin.eta,decide_eq_true_eq,SupplierStars.outside,
    mem_filter,mem_univ,true_and]
  simp

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitRepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
def view {f j : ℕ} (U : RationalUnitInput f j) : Raw :=
  ((List.ofFn U.y,List.ofFn (fun c => setView (U.F c))),
    (List.ofFn (fun c => List.ofFn (U.dc c)),(List.ofFn (fun c => List.ofFn (U.dd c)),List.ofFn (fun a => List.ofFn (U.df a)))))
abbrev Input.raw (x : Input) := view x.U
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_LastFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

@[fun_prop] theorem lastRaw_poly : Poly lastRaw := by
  unfold lastRaw
  have hp : Poly (fun x : Row × Data Row => x.2.2.map RoundingList.Last.probability) := by apply list_map <;> fun_prop
  have he : Poly (fun x : Row × Data Row => x.2.2.flatMap (fun p => [RoundingList.Last.endpoint false p,RoundingList.Last.endpoint true p])) := by
    apply list_flatMap <;> fun_prop
  exact pair (by fun_prop) (pair (comp (⟨branchLawProgram⟩ : Poly branchLawData) (pair (by fun_prop) hp)) he)
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_TargetSubsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
def prepare (x : Raw) : List ℚ × List ℚ := (x.1.map (fun _ => 1),x.1.map (fun b => if b then x.2 else 0))
@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply pair <;> apply list_map <;> fun_prop
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)

def prepare (x : Raw) : List SparseTargetSubset.Program.Raw :=
  (indices x.2.2).map (fun e => (x.2.1[e]?.getD [],x.2.2[e]?.getD 0))
@[fun_prop] theorem prepare_poly : Poly prepare := by unfold prepare; apply list_map <;> fun_prop
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

@[fun_prop] theorem boolState_poly : Poly boolState := by
  unfold boolState
  apply list_map
  · fun_prop
  · exact comp (f:=fun xs : Row => List.range xs.length) (g:=fun x : (Row × Row) × List Bool => x.1.1) list_indices (by fun_prop)

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
abbrev StateRaw := QRow × (Table × Row)
def view {n m : ℕ} (s : SparseSignedPreparation.State n m) : StateRaw :=
  (s.1.toList,(SparseGraph.ListOperation.view s.2.1,List.ofFn s.2.2))
abbrev KernelRaw := List Unit × (Table × QRow)
def KernelInput.raw (x : KernelInput) : KernelRaw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),x.p.toList))

def attach (x : QRow × Data (Table × Row)) : Data StateRaw := (x.2.1,x.2.2.map (fun s => (x.1,s)))
@[fun_prop] theorem attach_poly : Poly attach := by
  unfold attach; apply pair
  · fun_prop
  · apply list_map <;> fun_prop

abbrev Raw := List Unit × (Table × (QRow × QRow))
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),(List.ofFn x.c,x.p.toList)))
abbrev Input.encode (x : Input) := enc x.raw

def beta (x : Raw) : QRow :=
  (SparseGraph.ListOperation.indices x.2.2.1).map (fun e => x.2.2.1[e]?.getD 0-
    (Completion.Rational.BestProgram.card (x.2.1[e]?.getD []):ℚ))
@[fun_prop] theorem beta_poly : Poly beta := by unfold beta; apply list_map <;> fun_prop

def inputRows (x : Raw × QRow × Data QRow) : List KernelRaw :=
  x.2.2.2.map (fun p => (x.1.1,(x.1.2.1,p)))
@[fun_prop] theorem inputRows_poly : Poly inputRows := by unfold inputRows; apply list_map <;> fun_prop

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedDataOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView indices)
abbrev StateRaw := SparseSignedPreparation.Program.StateRaw

abbrev KernelRaw := BaseRaw × StateRaw
def KernelInput.raw (x : KernelInput) : KernelRaw := (x.base,SparseSignedPreparation.Program.view x.z)
abbrev KernelInput.encode (x : KernelInput) := enc x.raw

def activationData (x : KernelRaw) (e j : ℕ) : ℕ :=
  (if (x.1.1[e]?.getD [])[j]?.getD false then ⌊x.1.2.1[e]?.getD 0⌋₊ else 0)+
    if (x.2.2.1[e]?.getD [])[j]?.getD false then 1 else 0
def totalData (x : KernelRaw) (j : ℕ) : ℕ :=
  x.1.2.2.2.2.2-min ((indices x.1.2.1).map (fun e => activationData x e j)).sum (x.1.2.2.2.2.2/2)
def pieces (x : KernelRaw) : List (List ℚ) :=
  (indices x.1.2.2.2.2.1).map (fun j => (indices x.1.2.2.2.1).map (fun i =>
    if (x.1.2.2.1[j]?.getD [])[i]?.getD false then
      (totalData x j:ℚ)*x.1.2.2.2.1[i]?.getD 0/x.1.2.2.2.2.1[j]?.getD 0 else 0))
@[fun_prop] theorem activationData_poly : Poly (fun x : KernelRaw × (ℕ × ℕ) => activationData x.1 x.2.1 x.2.2) := by
  unfold activationData; fun_prop
@[fun_prop] theorem totalData_poly : Poly (fun x : KernelRaw × ℕ => totalData x.1 x.2) := by
  unfold totalData
  have h : Poly (fun x : KernelRaw × ℕ => ((indices x.1.1.2.1).map (fun e => activationData x.1 e x.2)).sum) := by
    apply comp nat_list_sum
    apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem pieces_poly : Poly pieces := by
  unfold pieces
  apply list_map
  · apply list_map <;> fun_prop
  · fun_prop

end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseCounts.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

 theorem edges_view {n m : ℕ} (G : SparseCounts.Table n m) :
    edges (List.replicate n (),view G)=List.ofFn (edgeCode G) := by
  simp only [edges,indices,List.length_replicate,RoundingList.range_finRange,view,
    List.flatMap_def,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map]
  simp only [List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some]
  rw [RoundingList.ofFn_product]
  rfl

end MetricKMedian.SparseCounts.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_GridRoundingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram SparseCounts.Program

noncomputable def columnsProgram : PolyProgram QInput.encode (encodeList SparseGridRounding.Program.Input.encode) QInput.columns :=
  (snd (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun x => by
    change qt (List.ofFn (fun i => List.ofFn (x.column i).q))=
      encodeList SparseGridRounding.Program.Input.encode (List.ofFn x.column)
    rw [show List.ofFn (fun i => List.ofFn (x.column i).q)=
      (List.ofFn x.column).map (fun c => List.ofFn c.q) by rw [List.map_ofFn]; rfl]
    exact RoundingProgram.encodeList_map qr (fun c : SparseGridRounding.Program.Input => List.ofFn c.q) _)

end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def bundleData (x : KernelRaw) : List Unit × List (List ℚ) := (x.1.2.2.2.1.map (fun _ => ()),pieces x)
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
abbrev Raw := SparseSignedPreparation.Program.Raw
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)
def Input.μ (x : Input) := SparseOuterLaw.law x.D x.c x.q x.hc x.hq
def Input.ker (x : Input) (i : Fin x.μ.length) : KernelInput :=
  ⟨x.n,x.m,x.f,x.D,x.q,x.P,x.y,x.p,x.Δ,x.μ.states[i.val],x.hy,x.hp⟩
def Input.kernels (x : Input) := List.ofFn x.ker

end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.FractionalRefinement.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
structure Input extends Program.Input where
  m : ℕ
  metric : PseudoMetricSpace (Fin m)
  facility : Fin f → Fin m
  client : Fin j → Fin m
  hdf : ∀ b b', @dist _ metric.toDist (facility b) (facility b')=(df b b':ℝ)
  hc : ∀ c b, @dist _ metric.toDist (client c) (facility b)=(dc c b:ℝ)
  hcc : ∀ c c', @dist _ metric.toDist (client c) (client c')=(dd c c':ℝ)
  B : ℚ
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceFractionalRound
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Instance
open Finset Preparation

 def fractionalRound (I : Instance) (a : TruncatedLP.FractionalData I.facilities.card I.clients.card)
    (ha : a.Valid I.k) (hj : I.clients.Nonempty) {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) :
    Option (Finset (Fin I.n)) :=
  letI := I.pseudoMetric
  (FractionalRefinement.scan a I.k ha (card_pos.mpr hj) I.indexedDistance I.clientDistance I.facilityDistance
    I.indexedDistance_nonneg I.clientDistance_self I.clientDistance_comm
    (I.facilities.orderEmbOfFin rfl) (I.clients.orderEmbOfFin rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) p (I.k+C)).map
    (fun O => O.image (I.facilities.orderEmbOfFin rfl))

end MetricKMedian.Instance
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceComputedPseudo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Instance
open Finset Preparation

 theorem nonzeroFractional_spec (I : Instance) (h : ¬I.zeroTest) (r : ℕ) (hr : 0 < r) :
    let a := I.computedFractional r hr (I.nonzero_clients h)
    a.Valid I.k ∧ (a.value I.indexedDistance:ℝ)≤(1+3/(r:ℝ))*optimum I := by
  simpa only [dite_eq_right h] using I.initialPhase_spec r hr

 def nonzeroRound (I : Instance) (h : ¬I.zeroTest) (r : ℕ) (hr : 0 < r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) : Option (Finset (Fin I.n)) :=
  I.fractionalRound (I.computedFractional r hr (I.nonzero_clients h))
    (I.nonzeroFractional_spec h r hr).1 (I.nonzero_clients h) p C

 def computedPseudo (I : Instance) (r : ℕ) (hr : 0 < r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) : Finset (Fin I.n) :=
  if h : I.zeroTest then I.zeroOutput
  else (I.nonzeroRound h r hr p C).getD {I.facilities.min' I.facilities_nonempty}

end MetricKMedian.Instance
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
variable (r : ℕ) (hr : 0 < r)
def fractionalInput (I : Nonzero) : FractionalRefinement.Program.Input :=
  ⟨I.val.facilities.card,I.val.clients.card,I.val.k,I.val.computedFractional r hr (I.val.nonzero_clients I.property),
    (I.val.nonzeroFractional_spec I.property r hr).1,card_pos.mpr (I.val.nonzero_clients I.property),
    I.val.indexedDistance,I.val.clientDistance,I.val.facilityDistance,I.val.indexedDistance_nonneg,
    I.val.clientDistance_self,I.val.clientDistance_comm⟩
end MetricKMedian.InstanceProgram
end

end OAI
end


