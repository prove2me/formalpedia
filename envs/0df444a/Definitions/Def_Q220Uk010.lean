-- Prove2me | Definitions.Def_Q220Uk010
-- name    : Q220Uk010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:52:26.606136+00:00
-- url     : https://prove2.me/theorems/dafc2b85-7bd9-42bb-9241-fcca231eb94f
-- title:
--   Definitions bundle Q220Uk010 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 8 definitions and 16 theorems. The definitions and types are `OAI.UniformKServer.RuntimeCertificate.bound`, `OAI.UniformKServer.RuntimeCertificate.needA`, `OAI.UniformKServer.RuntimeCertificate.needR`, `OAI.UniformKServer.RuntimeCertificate.needU`, `OAI.UniformKServer.RuntimeCertificate.time`, `OAI.UniformKServer.TreeRounding.PublicInput.charge`, `OAI.UniformKServer.TreeRounding.PublicInput.potential`, `OAI.UniformKServer.TreeRounding.PublicInput.transport`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`UniformKServer_ActualPublicFlow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/ActualPublicFlow.lean), [`UniformKServer_PublicFlow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/PublicFlow.lean), [`UniformKServer_PublicRounding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/PublicRounding.lean), [`UniformKServer_RoundingChain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/RoundingChain.lean), [`UniformKServer_RoundingKernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/RoundingKernel.lean), [`UniformKServer_RuntimeExistence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/RuntimeExistence.lean).
--
--   **Imports.** It imports the published bundle `Def_UniformKServer`; the bundle `Q220Uk007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q220Uk011`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk007

section
-- module Solutions.Q220_UK.UniformKServer_RoundingChain
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Chosen joint repairs form one adapted Markov chain on a fixed finite state
space. The choices use the old distribution and current geometric data only. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]

theorem chosenStep_bound (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b : Allocation S k) (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (P : Distribution a) :
    (chosenStep w hw hsep a b f g G hG hgeo P).joint.expect (fun st=>stateDistance f g st.1 st.2)≤
      G*132*variation w a b+∑ v,park S b.amount v*commonDistance a b f g v :=
  Classical.choose_spec (distribution_step w hw hsep a b f g G hG hgeo P)

namespace ChainInput
variable (D : ChainInput S k X Ω)

theorem chosen_congr (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b a' b' : Allocation S k) (f g f' g' : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (hgeo' : ∀ u v,0<park S a'.amount u → 0<park S b'.amount v → u≠v →
      dist (f' u) (g' v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (P : Distribution a) (Q : Distribution a')
    (ha : a=a') (hb : b=b') (hf : f=f') (hg : g=g') (hp : P.law=Q.law) :
    (chosenStep w hw hsep a b f g G hG hgeo P).joint=
      (chosenStep w hw hsep a' b' f' g' G hG hgeo' Q).joint ∧
    (chosenStep w hw hsep a b f g G hG hgeo P).next.law=
      (chosenStep w hw hsep a' b' f' g' G hG hgeo' Q).next.law := by
  subst a'; subst b'; subst f'; subst g'
  have := Distribution.ext hp
  subst Q
  exact ⟨rfl,rfl⟩

theorem distribution_causal (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) :
    (D.distribution t ω).law=(D.distribution t v).law := by
  induction t with
  | zero =>
    have hi (a b : Allocation S k) (hab : a=b) :
        (Classical.choice (distribution_initial a)).law=(Classical.choice (distribution_initial b)).law := by
      subst b
      rfl
    exact hi _ _ (D.allocation_causal 0 ω v he)
  | succ t ih =>
    exact (chosen_congr D.weight D.weight_nonneg D.weight_separated _ _ _ _ _ _ _ _
      D.factor D.factor_nonneg (D.geometry t ω) (D.geometry t v) _ _
      (D.allocation_causal t ω v (D.refines t ω v he)) (D.allocation_causal (t+1) ω v he)
      (D.anchors_causal t ω v (D.refines t ω v he)) (D.anchors_causal (t+1) ω v he)
      (ih (D.refines t ω v he))).2

theorem joint_causal (t : ℕ) (ω v : Ω) (he : (D.filtration (t+1)).r ω v) :
    D.joint t ω=D.joint t v :=
  (chosen_congr D.weight D.weight_nonneg D.weight_separated _ _ _ _ _ _ _ _
    D.factor D.factor_nonneg (D.geometry t ω) (D.geometry t v) _ _
    (D.allocation_causal t ω v (D.refines t ω v he)) (D.allocation_causal (t+1) ω v he)
    (D.anchors_causal t ω v (D.refines t ω v he)) (D.anchors_causal (t+1) ω v he)
    (D.distribution_causal t ω v (D.refines t ω v he))).1

theorem second (t : ℕ) (ω : Ω) (F : State S k→ℝ) :
    (D.joint t ω).expect (F ∘ Prod.snd)=(D.distribution (t+1) ω).law.expect F :=
  (D.step t ω (D.distribution t ω)).second F

theorem cost_bound (t : ℕ) (ω : Ω) :
    (D.joint t ω).expect (fun st=>stateDistance (D.anchors t ω) (D.anchors (t+1) ω) st.1 st.2)≤
      D.factor*132*variation D.weight (D.allocation t ω) (D.allocation (t+1) ω)+
        ∑ v,park S (D.allocation (t+1) ω).amount v*
          commonDistance (D.allocation t ω) (D.allocation (t+1) ω) (D.anchors t ω) (D.anchors (t+1) ω) v :=
  chosenStep_bound D.weight D.weight_nonneg D.weight_separated _ _ _ _
    D.factor D.factor_nonneg (D.geometry t ω) _

end ChainInput
end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundingKernel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The adapted joint repair gives genuine conditional state transitions, with
both marginal identities and their exact transport expectation. -/
namespace UniformKServer.TreeRounding.ChainInput
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]
variable (D : ChainInput S k X Ω)

theorem second_law (t : ℕ) (ω : Ω) :
    (D.joint t ω).map Prod.snd=(D.distribution (t+1) ω).law := by
  apply FiniteProbability.Law.ext_expect
  intro f
  rw [Law.expect_map]
  exact D.second t ω f

theorem kernel_causal (t : ℕ) (ω v : Ω) (he : (D.filtration (t+1)).r ω v) :
    D.kernel t ω=D.kernel t v := by
  funext s
  unfold kernel
  rw [D.joint_causal t ω v he]

end UniformKServer.TreeRounding.ChainInput

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PublicRounding
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Causal rounded distributions are realized without exposing the hidden
trajectory. Only an observed request prefix selects the conditional rows. -/
namespace UniformKServer.TreeRounding
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]

namespace PublicInput
variable {D : ChainInput S k X Ω} (O : PublicInput D)

omit [Fintype X] in
theorem kernel_trace (t : ℕ) (ω : Ω) :
    O.input.kernel (O.trace t ω) (O.request t ω)=D.kernel t ω := by
  change D.kernel (O.trace t ω).length (O.pick (O.trace t ω++[O.request t ω]))=_
  rw [O.trace_length,←O.trace_snoc]
  exact D.kernel_causal t _ _ (O.pick_related (t+1) ω)

omit [Fintype X] in
theorem location_trace (t : ℕ) (ω : Ω) :
    O.input.location (O.trace t ω)=fun s i=>D.anchors t ω (s.realization.tuple i) := by
  funext s i
  change D.anchors (O.trace t ω).length (O.pick (O.trace t ω)) _=_
  rw [O.trace_length,D.anchors_causal t _ _ (O.pick_related t ω)]

theorem initial_first (s : Fin k→X) (ω : Ω) :
    (O.initial s).map Prod.fst=(D.distribution 0 ω).law := by
  have hh : (D.filtration 0).r O.default ω := O.reflects 0 _ _ (by rw [O.trace_zero,O.trace_zero])
  rw [initial,Law.map_comp]
  change (D.distribution 0 O.default).law.map id=_
  rw [Law.map_id,D.distribution_causal 0 _ _ hh]

def potential (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) : ℝ :=
  ((O.input.model hk).process (O.initial s) (O.trace t ω)).expect (O.input.potential (O.trace t ω))

def charge (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) : ℝ :=
  O.input.charge hk ((O.input.model hk).process (O.initial s) (O.trace t ω)) (O.trace t ω) (O.request t ω)

def transport (_O : PublicInput D) (t : ℕ) (ω : Ω) : ℝ :=
  (D.joint t ω).expect (fun st=>stateDistance (D.anchors t ω) (D.anchors (t+1) ω) st.1 st.2)

theorem potential_nonneg (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) :
    0≤O.potential hk s t ω := by
  apply Law.expect_nonneg
  intro v
  exact LazyFinance.mismatch_nonneg _ _

theorem potential_initial (hk : 0<k) (s : Fin k→X) (ω : Ω) (Δ : ℝ)
    (hdiam : ∀ x y : X,dist x y≤Δ) : O.potential hk s 0 ω≤k*Δ := by
  rw [potential,O.trace_zero]
  exact O.input.initial_potential _ s Δ hdiam

end PublicInput
end UniformKServer.TreeRounding

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PublicFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A rounded private process gives a literal nonnegative configuration/action
flow with legal zero-marginal rows and the same expected movement. -/
namespace UniformKServer.TreeRounding.PublicInput
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]
attribute [local instance] OAI.UniformKServer.TreeRounding.PublicInput.configEq
variable {D : ChainInput S k X Ω} (O : PublicInput D)

theorem flow_valid (hk : 0<k) (s : Fin k→X) (H : ℕ) :
    RealFlow.Valid (O.flow hk s) (fun c r j=>Function.update c j r) allowed s H := by
  apply MarkovFlow.Model.valid
  · exact LazyMarkov.Input.initial_marginal _ s
  · intro w r c v
    exact O.input.legal hk w r c v

theorem flow_trace (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) :
    RealFlow.flowCost (O.flow hk s) (fun c r j=>dist (c j) r) [] (O.trace t ω)=
      ∑ u∈range t,O.charge hk s u ω := by
  induction t with
  | zero => simp only [O.trace_zero,RealFlow.flowCost,sum_range_zero]
  | succ t ih =>
    rw [O.trace_snoc,RealFlow.flowCost_append,ih,sum_range_succ]
    congr 1
    simp only [RealFlow.flowCost,List.nil_append,add_zero]
    rfl

end UniformKServer.TreeRounding.PublicInput

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPublicFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Law-dependent but genuinely online configuration/action flows for the
actual pilot, partition, allocation, anchor, and rounding construction. -/

namespace UniformKServer.PartitionTree
open Finset FiniteProbability TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.configEq
theorem component_valid (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) : RealFlow.Valid (componentFlow A D hk z hdiam ω₀ hpublic s)
      (fun c r j=>Function.update c j r) PublicInput.allowed s N :=
  (publicInput A D hk z hdiam ω₀ hpublic).flow_valid (by omega) s N

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RuntimeExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RuntimeCertificate
open RawProgram RawCertificate RawFinite
open scoped Classical

def time (u r a : ℕ) : ℕ := Classical.choose (LiteralBound.exists_time u r a)

def needA (u r a : ℕ) : ℕ := max
  (chosen (unpack u) (requestToken r) a).bits.length (time u (requestToken r) a)
def needR (b u r : ℕ) : ℕ := max ((natCode (r+1)).length+1)
  ((Finset.range (2^(b+1))).sup (needA u r))
def needU (n b u : ℕ) : ℕ := max (u.bits.length+1) ((Finset.range n).sup (needR b u))
def bound (n b : ℕ) (S : List ℕ) : ℕ := max (b+1) (S.toFinset.sup (needU n b))

end UniformKServer.RuntimeCertificate

end

end OAI
end


