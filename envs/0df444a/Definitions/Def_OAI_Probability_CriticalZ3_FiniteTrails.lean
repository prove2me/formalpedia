-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
-- name    : OAI_Probability_CriticalZ3_FiniteTrails
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:23:40.683807+00:00
-- url     : https://prove2.me/theorems/69b1f6c7-ecab-4208-a19c-10d616f9b3fd
-- title:
--   Balanced directed edge sets decompose into closed trails
-- statement:
--   Tools for decomposing a finite balanced directed boundary into cycles.
--
--   1. **Successor.** If finitely many directed edges $d$ with tails and heads in $V$ are balanced, i.e. every vertex has as many incoming as outgoing edges, then choosing at each vertex a bijection from incoming to outgoing edges gives a permutation $\sigma$ of the edges with
--   $$
--   \mathrm{tail}(\sigma(d))=\mathrm{head}(d).
--   $$
--   2. **Cycles.** The orbit of $d$ under $\sigma$ has length its minimal period, which is positive, and it is enumerated by $\{0,\dots,\mathrm{period}-1\}$; it forms a closed edge-simple trail.
--   3. **Cyclic successor.** On $\{0,\dots,n-1\}$ with $n>0$, the next index is $i+1\bmod n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/FiniteTrails.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/FiniteTrails.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uD uV

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

/-! Finite balanced directed boundaries admit closed edge-simple trails.
This is used only for the planar contour dependency of the main proof. -/
open Classical Function
namespace FiniteTrails
variable {D : Type uD} {V : Type uV} [Fintype D]

noncomputable def successor (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v}) :
    Equiv.Perm D :=
  (Equiv.sigmaFiberEquiv head).symm.trans
    ((Equiv.sigmaCongrRight (fun v => Fintype.equivOfCardEq (hbal v))).trans
      (Equiv.sigmaFiberEquiv tail))

theorem period_pos (σ : Equiv.Perm D) (d : D) : 0 < minimalPeriod σ d :=
  minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts d)

noncomputable def cycleEquiv (σ : Equiv.Perm D) (d : D) :
    Fin (minimalPeriod σ d) ≃ {e // σ.SameCycle d e} := by
  let f : Fin (minimalPeriod σ d) → {e // σ.SameCycle d e} := fun i =>
    ⟨σ^[i.val] d,by
      rw [←Equiv.Perm.coe_pow]
      exact Equiv.Perm.SameCycle.rfl.pow_right⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply Fin.ext
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp (congrArg Subtype.val hij)
  · intro e
    obtain ⟨k,hk⟩ := e.property.exists_nat_pow_eq
    refine ⟨⟨k % minimalPeriod σ d,Nat.mod_lt _ (period_pos σ d)⟩,?_⟩
    apply Subtype.ext
    change σ^[k % minimalPeriod σ d] d = e.val
    rw [iterate_mod_minimalPeriod_eq,←Equiv.Perm.coe_pow]
    exact hk

def next {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩

end FiniteTrails

end OAI


