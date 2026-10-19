-- Prove2me | Definitions.Def_OAIQWEGC000
-- name    : OAIQWEGC000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T02:04:48.374267+00:00
-- url     : https://prove2.me/theorems/492a3d13-45ac-4286-ad53-944ecffa951d
-- title:
--   OpenAI Erdős–Gallai cycle-decomposition split: definitions bundle
-- statement:
--   This is the definitions bundle of the split of OpenAI's proof of `OAI.ErdosGallai.erdos_gallai`. That theorem says the edges of every graph on $n$ vertices can be partitioned into $O(n)$ cycles and single edges (the Erdős–Gallai cycle-decomposition conjecture).
--
--   The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/CycleDecomposition`. The source is OpenAI, *A linear cycle-and-edge decomposition of every graph*, OpenAI Math Release, September 24, 2026, result family 181, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0. The definitions are ported to Lean 4.33.1 and Mathlib 0df444a. They include:
--   - the decomposition cost `decompositionCost`, defined in the main development and again in its batch copy;
--   - cut expansion and vertex expansion;
--   - the path pieces, arms and frames of Lovász's argument;
--   - the scale hierarchy, layers and assigned pieces;
--   - the sampling and routing constructions;
--   - the constants of the cost regrouping.
--
--   The bundle also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   The definitions of the published statement (`CycleOrSingleEdge`, `EdgeDecomposition`, `MainStatement`) are not repeated. The bundle imports them from the published bundle `Def_CycleDecomposition`. It imports no other bundle.
--
--   Modules: `BatchEndpoints`, `BatchIndexing`, `BatchPathDeletion`, `BatchPreparation`, `BatchResolution`, `BatchRouting`, `CollisionEstimates`, `CostRegrouping`, `CoupledResolution`, `CycleLifting`, `Decomposition`, `DepthFirstSearch`, `EdgeSplitting`, `EndpointPartition`, `ExpansionBoxes`, `Lovasz`, `Main`, `Pairing`, `PathDeletion`, `Representatives`, `ReservoirCycles`, `ReservoirRemainder`, `ReservoirSampling`, `Routing`, `Sampling`, `SamplingCuts`, `ScaleDecomposition`, `ScaleExtraction`, `ScaleHierarchy`, `Templates`, `UniformLayers`.
-- source:
--   OpenAI, A linear cycle-and-edge decomposition of every graph, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 181; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/CycleDecomposition at commit adc7f12

import Mathlib
import Definitions.Def_CycleDecomposition

section
-- module Solutions.OAIQW_ErdosGallai.Compat
namespace OAI.ErdosGallai
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434


end OAI.ErdosGallai
end

section
-- module Solutions.OAIQW_ErdosGallai.Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15

section

namespace ErdosGallai.Sampling
open MeasureTheory ProbabilityTheory Finset Real

section ProductSamples
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

noncomputable def sampleMeasure (V : Type cycleUniverse5) [Fintype V] (p : unitInterval) : Measure (V → Bool) :=
  Measure.pi (fun _ : V => bernoulliMeasure true false p)

instance sampleMeasure_probability (p : unitInterval) : IsProbabilityMeasure (sampleMeasure V p) := by
  unfold sampleMeasure
  infer_instance

def sampleVertices (ω : V → Bool) : Finset V := Finset.univ.filter (fun v => ω v = true)

def sampleIndicator (v : V) (ω : V → Bool) : ℝ := if ω v then 1 else 0

noncomputable def blockIndicator (S : Finset V) : (V → Bool) → ℝ :=
  {ω | S ⊆ sampleVertices ω}.indicator (fun _ => 1)

end ProductSamples

end ErdosGallai.Sampling
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.SamplingCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7

section
namespace ErdosGallai.Sampling
open Finset MeasureTheory ProbabilityTheory Real
open scoped symmDiff
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

noncomputable def cutColor (e : V × V) : ℕ :=
  (Fintype.equivFin V e.1).val + (Fintype.equivFin V e.2).val

def neighborsIn (P : SimpleGraph V) [DecidableRel P.Adj] (v : V) (A : Finset V) :=
  A.filter (P.Adj v)

def neighborhoodUnion (P : SimpleGraph V) [DecidableRel P.Adj] (S : Finset V) : Finset V :=
  S.biUnion (fun v => neighborsIn P v Finset.univ)

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

def witnessFamily (P : SimpleGraph V) [DecidableRel P.Adj] (s : ℕ) : Finset (Finset V) :=
  ((((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s))).image (neighborhoodUnion P)

def SampleGood (P : SimpleGraph V) [DecidableRel P.Adj] (p h τ : ℝ) (ω : V → Bool) : Prop :=
  ((sampleVertices ω).card : ℝ) ≤ 2*p*Fintype.card V ∧
    (∀ v, p*h/2 ≤ ((neighborsIn P v (sampleVertices ω)).card : ℝ)) ∧
    CutExpansionOn P (sampleVertices ω) τ

end ErdosGallai.Sampling

end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ReservoirSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
namespace ErdosGallai.Sampling

def samplingScaleError (c p D : ℝ) : ℝ :=
  exp (-p/3 * D^(9/10 : ℝ)) +
    D^(51/50 : ℝ) * exp (-(p*c/8) * D^(9/10 : ℝ)) +
    (2*(4/c+2)) * (D^(23/20 : ℝ) * exp (-(p^3*c^2/512) * D^(39/50 : ℝ)))

def SamplingScaleReady (c p D : ℝ) (r : ℕ) : Prop :=
  let h := c*D^(9/10 : ℝ)
  let τ := D^(37/50 : ℝ)
  let M := D^(1/100 : ℝ)
  2 ≤ r ∧ τ < p*h/4 ∧ M ≤ h ∧ (r : ℝ)*exp (-p*M/4) < 1/2 ∧
    4*τ/(p*h)+4*τ*M/h ≤ 1/2 ∧
    τ+r*(4*τ/(p*h)+4*τ*M/h) ≤ p^2*h/8 ∧
    exp (-p*r/3) + r*exp (-p*h/8) +
      2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) * (r : ℝ)^⌈4*r*M/h⌉₊ *
        exp (-p^3*h^2/(256*r)) ≤ samplingScaleError c p D

end ErdosGallai.Sampling

open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Sampling

def reservoirLabelPMF (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) : PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (if i = 3 then 1-3*(p : ℝ) else (p : ℝ))) (by
    rw [Fin.sum_univ_four]
    simp only [show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
      show (2 : Fin 4) ≠ 3 by decide, ↓reduceIte,  ]
    rw [← ENNReal.ofReal_add p.property.1 p.property.1,
      ← ENNReal.ofReal_add (by linarith [p.property.1]) p.property.1,
      ← ENNReal.ofReal_add (by linarith [p.property.1]) (by linarith)]
    norm_num [show (p : ℝ)+(p : ℝ)+(p : ℝ)+(1-3*(p : ℝ)) = 1 by ring])

def labelIs (i : Fin 3) (j : Fin 4) : Bool := decide (j = i.castSucc)

end ErdosGallai.Sampling

namespace ErdosGallai.Sampling
open Finset MeasureTheory ProbabilityTheory
noncomputable section
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

def reservoirSample (i : Fin 3) (ω : V → Fin 4) : V → Bool := fun v => labelIs i (ω v)

def reservoirMeasure (V : Type cycleUniverse2) [Fintype V] (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) :
    Measure (V → Fin 4) := Measure.pi (fun _ : V => (reservoirLabelPMF p hp).toMeasure)

instance reservoirMeasure_probability (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) :
    IsProbabilityMeasure (reservoirMeasure V p hp) := by unfold reservoirMeasure; infer_instance

universe u

end
end ErdosGallai.Sampling

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.EdgeSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Splitting
open MeasureTheory ProbabilityTheory Finset Real

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

def edgeColorMeasure (V : Type cycleUniverse5) [Fintype V] (l : ℕ) [NeZero l] :
    Measure (Sym2 V → Fin l) :=
  Measure.pi (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure)

instance edgeColorMeasure_probability (l : ℕ) [NeZero l] :
    IsProbabilityMeasure (edgeColorMeasure V l) := by
  unfold edgeColorMeasure
  infer_instance

def colorIndicator {l : ℕ} (i : Fin l) (e : Sym2 V) (ω : Sym2 V → Fin l) : ℝ :=
  if ω e = i then 1 else 0

def colorGraph (P : SimpleGraph V) {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    SimpleGraph V where
  Adj x y := P.Adj x y ∧ ω s(x,y) = i
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact P.irrefl h.1⟩

instance colorGraph_decidable (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    DecidableRel (colorGraph P ω i).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

end

open Filter Asymptotics
open scoped Topology

noncomputable def edgeSplittingScaleError (c : ℝ) (l : ℕ) (D : ℝ) : ℝ :=
  (l : ℝ) * (Real.exp (D^(51/50 : ℝ) * Real.exp ((-(c / (8*l))) * D^(9/10 : ℝ))) - 1)

universe u

end ErdosGallai.Splitting

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Representatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section

namespace ErdosGallai
noncomputable section
open Finset Real Filter
attribute [local instance] Classical.propDecidable

noncomputable def reservoirProbability (η : ℝ) : ℝ := min (η/12) (1/12)
noncomputable def reservoirExpansionCoefficient (c : ℝ) : ℝ := min c 1 / 6

universe u

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Routing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

def avoidGraph (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    SimpleGraph V where
  Adj v w := P.Adj v w ∧ s(v, w) ∉ F ∧ v ∉ W ∧ w ∉ W
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2.1, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨by intro v h; exact P.irrefl h.1⟩

noncomputable def walkBall (G : SimpleGraph V) (s : V) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ p : G.Walk s v, p.length ≤ t)

@[simp] lemma mem_walkBall {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (s v : V) (t : ℕ) :
    v ∈ walkBall G s t ↔ ∃ p : G.Walk s v, p.length ≤ t := by
  classical
  simp [walkBall]

noncomputable def routingG (r h : ℝ) : ℕ := ⌈8 * (r / h) * Real.logb 2 (2 * r)⌉₊

noncomputable def routingDepth (r : ℝ) : ℕ := ⌈Real.logb 2 r⌉₊

noncomputable def routingLength (r h : ℝ) : ℕ := 2 * routingG r h * (1 + routingDepth r)

def incidentEdges (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  F.filter (fun e => v ∈ e)

noncomputable def saturated (F : Finset (Sym2 V)) (h : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => h / 8 ≤ ((incidentEdges F v).card : ℝ))

def pathInterior {P : SimpleGraph V} {s t : V} (q : P.Walk s t) : Finset V :=
  q.support.toFinset \ {s, t}

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

def endpointLoad (A : Finset I) (x y : I → V) (v : V) : ℕ :=
  (A.filter (fun i => x i = v ∨ y i = v)).card

noncomputable def usedEdges (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) : Finset (Sym2 V) :=
  A.biUnion (fun i => (q i).edges.toFinset)

noncomputable def teamInterior (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) : Finset V :=
  (A.filter (fun j => team j = team i)).biUnion (fun j => pathInterior (q j))

structure PartialRoutes (P : SimpleGraph V) (x y : I → V) (team : I → T)
    (Z : I → Finset V) (L : ℕ) (h : ℝ) (A : Finset I)
    (q : ∀ i, P.Walk (x i) (y i)) : Prop where
  simple : ∀ i ∈ A, (q i).IsPath
  short : ∀ i ∈ A, (q i).length ≤ L
  avoids : ∀ i ∈ A, Disjoint (pathInterior (q i)) (Z i)
  edge_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset
  team_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))
  degree : ∀ v, ((incidentEdges (usedEdges A q) v).card : ℝ) ≤ h / 8 + 2 + endpointLoad A x y v

end Families
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ReservoirCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

def endpointOccurrence {I : Type cycleUniverse3} {V : Type cycleUniverse4} (x y : I → V) (a : I × Fin 2) : V :=
  if a.2 = 0 then x a.1 else y a.1

end
end ErdosGallai

namespace ErdosGallai
open SimpleGraph

variable {V : Type cycleUniverse11} {G : SimpleGraph V} {x y a b : V}

def reservoirReturn (P : G.Walk a b) (hx : G.Adj x a) (hy : G.Adj y b) :
    G.Walk y x := .cons hy (P.reverse.concat hx.symm)

end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ReservoirRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section

namespace ErdosGallai
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

lemma exists_reservoir_avoided {V : Type cycleUniverse6} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (x y : V) :
    ∃ i, x ∉ W i ∧ y ∉ W i := by
  by_contra hno
  have h : ∀ i, x ∈ W i ∨ y ∈ W i := by
    intro i
    by_contra! hi
    exact hno ⟨i,hi⟩
  have h01 := Set.disjoint_left.mp (hW (show (0 : Fin 3) ≠ 1 by decide))
  have h02 := Set.disjoint_left.mp (hW (show (0 : Fin 3) ≠ 2 by decide))
  have h12 := Set.disjoint_left.mp (hW (show (1 : Fin 3) ≠ 2 by decide))
  rcases h 0 with hx0 | hy0 <;>
    rcases h 1 with hx1 | hy1 <;>
    rcases h 2 with hx2 | hy2
  all_goals first
    | exact h01 hx0 hx1
    | exact h02 hx0 hx2
    | exact h12 hx1 hx2
    | exact h01 hy0 hy1
    | exact h02 hy0 hy2
    | exact h12 hy1 hy2

lemma exists_edge_reservoir_avoided {V : Type cycleUniverse7} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) :
    ∃ i, ∀ v ∈ e, v ∉ W i := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨i,hx,hy⟩ := exists_reservoir_avoided W hW x y
    refine ⟨i,?_⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hx
    · exact hy

noncomputable def reservoirColor {V : Type cycleUniverse8} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) : Fin 3 :=
  (exists_edge_reservoir_avoided W hW e).choose

def complementaryReservoirGraph {V : Type cycleUniverse10} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ reservoirColor W hW s(x,y) = i
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def reservoirInternal {V : Type cycleUniverse13} (P : SimpleGraph V) (W : Set V) : Set (Sym2 V) :=
  {e | e ∈ P.edgeSet ∧ ∀ v ∈ e, v ∈ W}

noncomputable def reservoirSpokes {V : Type cycleUniverse14} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) : Finset (Sym2 V) :=
  (Wᶜ ×ˢ univ).image (fun z => s(z.1,r z))

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def edgeRestriction {V : Type cycleUniverse22} (G : SimpleGraph V) (E : Set (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ s(x,y) ∈ E
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

def completedEdges {V : Type cycleUniverse26} {I : Type cycleUniverse27} (C : I → Set (Sym2 V)) : Set (Sym2 V) := ⋃ i, C i

def residualInternalGraph {V : Type cycleUniverse28} {B : Type cycleUniverse29} {I : Type cycleUniverse30} (G : SimpleGraph V)
    (R : B → Set (Sym2 V)) (C : I → Set (Sym2 V)) (b : B) : SimpleGraph V :=
  edgeRestriction G (R b \ completedEdges C)

def unusedSpokes {V : Type cycleUniverse31} {I : Type cycleUniverse32} [Fintype V] (S : Set (Sym2 V))
    (C : I → Set (Sym2 V)) : Finset (Sym2 V) := (S \ completedEdges C).toFinset

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

noncomputable def allReservoirSpokes {V : Type cycleUniverse50} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) : Finset (Sym2 V) :=
  univ.biUnion (fun b => reservoirSpokes (W b) (r b))

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Lovasz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56 cycleUniverse57 cycleUniverse58 cycleUniverse59 cycleUniverse60 cycleUniverse61 cycleUniverse62 cycleUniverse63 cycleUniverse64 cycleUniverse65 cycleUniverse66 cycleUniverse67 cycleUniverse68 cycleUniverse69 cycleUniverse70 cycleUniverse71 cycleUniverse72 cycleUniverse73 cycleUniverse74 cycleUniverse75 cycleUniverse76 cycleUniverse77 cycleUniverse78 cycleUniverse79 cycleUniverse80 cycleUniverse81 cycleUniverse82 cycleUniverse83 cycleUniverse84 cycleUniverse85

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Lovasz
universe u
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

def StarActive {V : Type cycleUniverse1} (S : Set V) (R : V → V → Prop) (v : V) : Prop :=
  ∃ a ∈ S, Relation.ReflTransGen R a v

structure PathPiece {V : Type cycleUniverse9} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

structure Piece {V : Type cycleUniverse11} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : (walk.IsPath ∧ 0 < walk.length) ∨
    ∃ h : finish = start, (walk.copy rfl h).IsCycle

namespace Piece
variable {V : Type cycleUniverse12} {G : SimpleGraph V}

def ofPath (p : PathPiece G) : Piece G :=
  ⟨p.start, p.finish, p.walk, Or.inl ⟨p.isPath, p.positive⟩⟩

def ofCycle {v : V} (p : G.Walk v v) (h : p.IsCycle) : Piece G :=
  ⟨v, v, p, Or.inr ⟨rfl, h⟩⟩

end Piece

structure Arm {V : Type cycleUniverse13} (G : SimpleGraph V) (x : V) where
  near : V
  far : V
  adj : G.Adj x near
  walk : G.Walk near far
  isPath : walk.IsPath
  avoids : x ∉ walk.support

namespace Arm
variable {V : Type cycleUniverse14} {G : SimpleGraph V} {x : V}

def tip (A : Arm G x) : PathPiece G where
  start := x
  finish := A.far
  walk := .cons A.adj A.walk
  isPath := A.isPath.cons A.avoids
  positive := by simp

def flip (A : Arm G x) (h : G.Adj x A.far) : Arm G x where
  near := A.far
  far := A.near
  adj := h
  walk := A.walk.reverse
  isPath := A.isPath.reverse
  avoids := by simpa using A.avoids

@[simp] lemma flip_edges (A : Arm G x) (h : G.Adj x A.far) :
    (A.flip h).walk.edgeSet = A.walk.edgeSet := by simp [flip]

@[simp] lemma mem_flip_support (A : Arm G x) (h : G.Adj x A.far) (v : V) :
    v ∈ (A.flip h).walk.support ↔ v ∈ A.walk.support := by simp [flip]

lemma two_arms_isPath (A B : Arm G x)
    (hd : A.walk.support.Disjoint B.walk.support) :
    ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).IsPath := by
  apply Walk.IsPath.mk'
  simp only [Walk.support_append, Walk.support_reverse, Walk.support_cons,
    List.tail_cons, List.reverse_cons, List.append_assoc]
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_reverse.mpr A.isPath.support_nodup, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨B.avoids, B.isPath.support_nodup⟩
  · rw [List.disjoint_left]
    intro v hv hq
    have hav : v ∈ A.walk.support := List.mem_reverse.mp hv
    rcases List.mem_cons.mp hq with rfl | hq
    · exact A.avoids hav
    · exact List.disjoint_left.mp hd hav hq

def join (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) : PathPiece G where
  start := A.far
  finish := B.far
  walk := (Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)
  isPath := two_arms_isPath A B hd
  positive := by simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons]; omega

def orient (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) : Arm G x :=
  if ha : active then A.flip (h ha) else A

@[simp] lemma orient_edges (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).walk.edgeSet = A.walk.edgeSet := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A.flip (h ha) from dite_eq_left ha)).trans (A.flip_edges _)
  · exact congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A from dite_eq_right ha)

@[simp] lemma orient_near (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).near = if active then A.far else A.near := by
  by_cases ha : active <;> simp [orient, flip, ha]

@[simp] lemma mem_orient_support (A : Arm G x) (active : Prop)
    (h : active → G.Adj x A.far) (v : V) :
    v ∈ (A.orient active h).walk.support ↔ v ∈ A.walk.support := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A.flip (h ha) from dite_eq_left ha)).to_iff.trans
        (A.mem_flip_support _ v)
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A from dite_eq_right ha)).to_iff

end Arm

inductive Frame {V : Type cycleUniverse15} (G : SimpleGraph V) (x : V) where
  | away (p : PathPiece G) (avoid : x ∉ p.walk.support)
  | tip (A : Arm G x)
  | through (A B : Arm G x) (disjoint : A.walk.support.Disjoint B.walk.support)

namespace Frame
variable {V : Type cycleUniverse16} {G : SimpleGraph V} {x : V}

def path : Frame G x → PathPiece G
  | .away p _ => p
  | .tip A => A.tip
  | .through A B hd => A.join B hd

def Port : Frame G x → Type
  | .away _ _ => Bool
  | .tip _ => Unit
  | .through _ _ _ => Bool

def endpoint : (F : Frame G x) → F.Port → V
  | .away p _, false => p.start
  | .away p _, true => p.finish
  | .tip A, _ => A.far
  | .through A _ _, false => A.far
  | .through _ B _, true => B.far

def exit : (F : Frame G x) → F.Port → Option V
  | .away _ _, _ => none
  | .tip _, _ => none
  | .through A _ _, false => some A.near
  | .through _ B _, true => some B.near

def inserted (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x, F.endpoint p)}

def removed (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, F.exit p = some v ∧ e = s(x,v)}

@[simp] lemma removed_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).removed active = ∅ := by
  ext e; simp [removed, exit]

@[simp] lemma removed_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).removed active = ∅ := by
  ext e; simp [removed, exit]

end Frame

inductive Centered {V : Type cycleUniverse21} (G : SimpleGraph V) (x : V) where
  | path (F : Frame G x)
  | cycle {v : V} (c : G.Walk v v) (hc : c.IsCycle)

namespace Centered
variable {V : Type cycleUniverse22} {G : SimpleGraph V} {x : V}

def piece : Centered G x → Piece G
  | .path F => .ofPath F.path
  | .cycle c hc => .ofCycle c hc

def Port : Centered G x → Type
  | .path F => F.Port
  | .cycle _ _ => Empty

def endpoint : (K : Centered G x) → K.Port → V
  | .path F, p => F.endpoint p
  | .cycle _ _, p => nomatch p

def exit : (K : Centered G x) → K.Port → Option V
  | .path F, p => F.exit p
  | .cycle _ _, p => nomatch p

def inserted (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x,K.endpoint p)}

def removed (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, K.exit p = some v ∧ e = s(x,v)}

end Centered

namespace Arm
variable {V : Type cycleUniverse27} {G : SimpleGraph V} {x b : V}

def fromWalk (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) : Arm G x :=
  match w with
  | .nil => False.elim (hn .nil)
  | @Walk.cons _ _ _ y _ h q =>
    ⟨y, b, h, q, (Walk.cons_isPath_iff h q).mp hp |>.1,
      (Walk.cons_isPath_iff h q).mp hp |>.2⟩

@[simp] lemma fromWalk_far (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).far = b := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_support (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).walk.support = w.support.tail := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_tip_edges (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).tip.walk.edgeSet = w.edgeSet := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl
end Arm

namespace Piece
variable {V : Type cycleUniverse29} {G H : SimpleGraph V}

def mapLe (h : H ≤ G) (P : Piece H) : Piece G := by
  rcases P with ⟨a,b,w,hs⟩
  refine ⟨a,b,w.mapLe h, ?_⟩
  rcases hs with hp | ⟨hb,hc⟩
  · exact Or.inl ⟨hp.1.mapLe h, by simpa using hp.2⟩
  · subst b
    exact Or.inr ⟨rfl, by simpa using hc.mapLe h⟩

@[simp] lemma mapLe_edges (h : H ≤ G) (P : Piece H) :
    (P.mapLe h).walk.edgeSet = P.walk.edgeSet := by
  cases P
  exact Walk.edgeSet_mapLe_eq_edgeSet _ _

@[simp] lemma mapLe_start (h : H ≤ G) (P : Piece H) : (P.mapLe h).start = P.start := by
  cases P; rfl
@[simp] lemma mapLe_finish (h : H ≤ G) (P : Piece H) : (P.mapLe h).finish = P.finish := by
  cases P; rfl

end Piece

def activeOrder {V : Type cycleUniverse38} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.support.toFinset.card

def HasPartition {V : Type cycleUniverse40} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Piece G),
    (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧ 2 * k ≤ activeOrder G

def evenStarVertices {V : Type cycleUniverse41} [Fintype V] (G : SimpleGraph V) (x : V) : Set V :=
  {y | G.Adj x y ∧ Even (G.degree y)}

def evenStarEdges {V : Type cycleUniverse42} [Fintype V] (G : SimpleGraph V) (x : V) : Set (Sym2 V) :=
  {e | ∃ y ∈ evenStarVertices G x, e = s(x,y)}

def deleteEvenStar {V : Type cycleUniverse43} [Fintype V] (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (evenStarEdges G x)

def subdivision {V : Type cycleUniverse55} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | some a, some b => G.Adj a b ∧ s(a,b) ≠ s(x,y)
    | none, some b => b = x ∨ b = y
    | some a, none => a = x ∨ a = y
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by
    intro a h
    cases a
    · exact h
    · exact G.irrefl h.1⟩

@[simp] lemma subdivision_some {V : Type cycleUniverse56} (G : SimpleGraph V) (x y a b : V) :
    (subdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := Iff.rfl
@[simp] lemma subdivision_none_some {V : Type cycleUniverse57} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj none (some a) ↔ a = x ∨ a = y := Iff.rfl
@[simp] lemma subdivision_some_none {V : Type cycleUniverse58} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj (some a) none ↔ a = x ∨ a = y := Iff.rfl
@[simp] lemma subdivision_none_none {V : Type cycleUniverse59} (G : SimpleGraph V) (x y : V) :
    ¬(subdivision G x y).Adj none none := id

def halfSubdivision {V : Type cycleUniverse60} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) :=
  (subdivision G x y).deleteEdges {s(none,some x)}

@[simp] lemma half_some {V : Type cycleUniverse61} (G : SimpleGraph V) (x y a b : V) :
    (halfSubdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp []

def subdivisionRepresentative {V : Type cycleUniverse77} (x y : V) (e : Sym2 V) : Sym2 (Option V) :=
  if e = s(x,y) then s(none,some x) else e.map Option.some

end
end ErdosGallai.Lovasz

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.PathDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

structure PositiveSimplePath {V : Type cycleUniverse1} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

def EndpointPathPartition {V : Type cycleUniverse5} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → PositiveSimplePath G),
    Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧
    (∀ v : V, (Finset.univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) ∧
    k ≤ Fintype.card V

def PathOrCycleEdgeSet {V : Type cycleUniverse6} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 0 < p.length ∧ s = p.edgeSet) ∨
  (∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ s = p.edgeSet)

def LovaszPathCyclePartition {V : Type cycleUniverse7} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
    (∀ i, PathOrCycleEdgeSet G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet ∧ 2 * k ≤ Fintype.card V

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

def evenAugmentation {V : Type cycleUniverse8} [Fintype V] (G : SimpleGraph V) :
    SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some u, some v => G.Adj u v
    | none, some v => Even (G.degree v)
    | some u, none => Even (G.degree u)
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact G.irrefl h⟩

@[simp] theorem evenAugmentation_some_adj {V : Type cycleUniverse9} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    (evenAugmentation G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem evenAugmentation_none_adj {V : Type cycleUniverse10} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj none (some v) ↔ Even (G.degree v) := Iff.rfl

@[simp] theorem evenAugmentation_some_none {V : Type cycleUniverse11} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj (some v) none ↔ Even (G.degree v) := Iff.rfl

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem path_tail_delete_start {V : Type cycleUniverse21} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.tail.edgeSet = {e | e ∈ p.edgeSet ∧ a ∉ e} := by
  cases p with
  | nil => ext e; simp
  | @cons a c b h q =>
    have ha : a ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have hnot : ∀ e ∈ q.edgeSet, a ∉ e := by
      intro e he hae
      exact ha (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e, he, hae⟩))
    ext e
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.mem_edgeSet,
      SimpleGraph.Walk.edges_tail, SimpleGraph.Walk.edges_cons, List.tail_cons, List.mem_cons]
    constructor
    · intro he
      exact ⟨Or.inr he, hnot e he⟩
    · rintro ⟨he | he, hn⟩
      · subst e; exact (hn (by simp)).elim
      · exact he

theorem path_dropLast_delete_end {V : Type cycleUniverse22} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.dropLast.edgeSet = {e | e ∈ p.edgeSet ∧ b ∉ e} := by
  have he : p.dropLast.edgeSet = p.reverse.tail.edgeSet := by
    calc
      _ = p.dropLast.reverse.edgeSet := (SimpleGraph.Walk.edgeSet_reverse _).symm
      _ = _ := by rw [SimpleGraph.Walk.reverse_dropLast, SimpleGraph.Walk.edgeSet_copy]
  rw [he, path_tail_delete_start p.reverse hp.reverse, SimpleGraph.Walk.edgeSet_reverse]

theorem positive_avoids_of_no_incidence {V : Type cycleUniverse23} {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hpos : 0 < p.length)
    (he : ∀ e ∈ p.edgeSet, v ∉ e) : v ∉ p.support := by
  have hn : ¬p.Nil := by intro hz; have := hz.length_eq_zero; omega
  intro hv
  obtain ⟨e, he', hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  exact he e he' hve

theorem delete_vertex_from_path {V : Type cycleUniverse24} [DecidableEq V] {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support) :
    let q := (p.takeUntil v hv).dropLast
    let r := (p.dropUntil v hv).tail
    q.IsPath ∧ r.IsPath ∧ Disjoint q.edgeSet r.edgeSet ∧
    q.edgeSet ∪ r.edgeSet = {e | e ∈ p.edgeSet ∧ v ∉ e} ∧
    (0 < q.length → v ∉ q.support) ∧
    (0 < r.length → v ∉ r.support) ∧
    (0 < q.length → G.Adj (p.takeUntil v hv).penultimate v) ∧
    (0 < r.length → G.Adj v (p.dropUntil v hv).snd) := by
  dsimp only
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have ht : t.IsPath := hp.takeUntil hv
  have hd : d.IsPath := hp.dropUntil hv
  have heq : t.append d = p := p.take_spec hv
  have hqe : t.dropLast.edgeSet = {e | e ∈ t.edgeSet ∧ v ∉ e} :=
    path_dropLast_delete_end t ht
  have hre : d.tail.edgeSet = {e | e ∈ d.edgeSet ∧ v ∉ e} :=
    path_tail_delete_start d hd
  have hdis : Disjoint t.edgeSet d.edgeSet := by
    have hn := hp.isTrail.edges_nodup
    rw [← heq, SimpleGraph.Walk.edges_append] at hn
    have hn' := (List.nodup_append.mp hn).2.2
    apply Set.disjoint_left.mpr
    intro e het hed
    exact hn' e het e hed rfl
  refine ⟨ht.dropLast, hd.tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqe, hre]
    exact hdis.mono (fun _ h => h.1) (fun _ h => h.1)
  · have he : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    rw [hqe, hre]
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rw [← he]
    simp only [Set.mem_union]
    tauto
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hqe ▸ he).2
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hre ▸ he).2
  · intro hpos
    apply t.adj_penultimate
    intro hn
    have hz := hn.length_eq_zero
    change 0 < t.dropLast.length at hpos
    rw [SimpleGraph.Walk.length_dropLast, hz] at hpos
    omega
  · intro hpos
    apply d.adj_snd
    intro hn
    have hz := hn.length_eq_zero
    change 0 < d.tail.length at hpos
    rw [SimpleGraph.Walk.length_tail, hz] at hpos
    omega

structure SimplePathPiece {V : Type cycleUniverse29} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath

namespace SimplePathPiece
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

def Avoiding (p : I → SimplePathPiece G) (v : V) := {i : I // v ∉ (p i).walk.support}
def Meeting (p : I → SimplePathPiece G) (v : V) := {i : I // v ∈ (p i).walk.support}
def DeleteIndex (p : I → SimplePathPiece G) (v : V) :=
  Avoiding p v ⊕ (Meeting p v × Bool)

instance instFintypeAvoiding (p : I → SimplePathPiece G) (v : V) : Fintype (Avoiding p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∉ (p i).walk.support})
instance instFintypeMeeting (p : I → SimplePathPiece G) (v : V) : Fintype (Meeting p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∈ (p i).walk.support})
instance instFintypeDeleteIndex (p : I → SimplePathPiece G) (v : V) : Fintype (DeleteIndex p v) :=
  inferInstanceAs (Fintype (Avoiding p v ⊕ (Meeting p v × Bool)))

def deleted (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → SimplePathPiece G
  | .inl i => p i.val
  | .inr (i,true) => ⟨_,_,((p i.val).walk.takeUntil v i.property).dropLast,
      ((p i.val).isPath.takeUntil i.property).dropLast⟩
  | .inr (i,false) => ⟨_,_,((p i.val).walk.dropUntil v i.property).tail,
      ((p i.val).isPath.dropUntil i.property).tail⟩

def parent (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → I
  | .inl i => i.val
  | .inr (i,_) => i.val

def oldEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl i => (p i.val).start = x ∨ (p i.val).finish = x
  | .inr (i,true) => (p i.val).start = x
  | .inr (i,false) => (p i.val).finish = x

def newEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl _ => False
  | .inr (i,true) => ((p i.val).walk.takeUntil v i.property).penultimate = x
  | .inr (i,false) => ((p i.val).walk.dropUntil v i.property).snd = x

lemma deleted_positive_avoids {V : Type cycleUniverse36} {I : Type cycleUniverse37} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v)
    (hpos : 0 < (deleted p v j).walk.length) : v ∉ (deleted p v j).walk.support := by
  rcases j with i | ⟨i,b⟩
  · exact i.property
  · have h := delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property
    cases b
    · exact h.2.2.2.2.2.1 hpos
    · exact h.2.2.2.2.1 hpos

def deletedInduced (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    SimplePathPiece (G.induce {x | x ≠ v}) := by
  let q := deleted p v j.val
  have havo : ∀ x ∈ q.walk.support, x ∈ ({x | x ≠ v} : Set V) := by
    intro x hx he
    subst x
    exact deleted_positive_avoids p v j.val j.property hx
  exact ⟨_,_, q.walk.induce _ havo, by
    apply SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    simpa using q.isPath⟩

end SimplePathPiece

end
end ErdosGallai
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.EndpointPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

def PositiveSimplePath.mapIso {V : Type cycleUniverse3} {W : Type cycleUniverse4} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (P : PositiveSimplePath G) : PositiveSimplePath H :=
  ⟨f P.start,f P.finish,P.walk.map f.toHom,P.isPath.map f.injective,by simpa using P.positive⟩

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_map {V : Type cycleUniverse9} {I : Type cycleUniverse10} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] [_contextInstance4 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    (deletedInduced p v j).walk.map (SimpleGraph.Embedding.induce _).toHom =
      (deleted p v j.val).walk := by
  exact SimpleGraph.Walk.map_induce _ _

def deletedPositive (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    PositiveSimplePath (G.induce {x | x ≠ v}) :=
  { deletedInduced p v j with
    positive := by
      have h := congrArg SimpleGraph.Walk.length (deletedInduced_map p v j)
      rw [SimpleGraph.Walk.length_map] at h
      rw [h]
      exact j.property }

end SimplePathPiece

def evenAugmentationOldIso {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V) :
    G ≃g (evenAugmentation G).induce {x | x ≠ none} where
  toEquiv := Equiv.optionSubtype none ⟨Equiv.refl (Option V),rfl⟩
  map_rel_iff' := Iff.rfl

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

noncomputable section
open SimpleGraph

lemma edgeDecomposition_of_indexed {V I : Type} [Fintype I] (G : SimpleGraph V)
    (parts : I → Set (Sym2 V)) (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hu : (⋃ i, parts i) = G.edgeSet) : EdgeDecomposition G (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨fun j => parts (e.symm j), fun j => hp _, ?_, ?_⟩
  · intro i j hij
    exact hd (fun he => hij (e.symm.injective he))
  · ext x
    simp only [Set.mem_iUnion]
    rw [← hu]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i, by simpa using hi⟩

theorem edgeDecomposition_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  apply edgeDecomposition_of_indexed G (fun e : G.edgeSet => {e.1})
  · intro e; exact Or.inr ⟨e.1,e.2,rfl⟩
  · intro e d hed
    exact Set.disjoint_singleton.mpr (fun h => hed (Subtype.ext h))
  · ext e; simp

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def decompositionCost {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, EdgeDecomposition G k from ⟨_,edgeDecomposition_singleEdges G⟩)

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchPathDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

structure PositiveSimplePath {V : Type cycleUniverse1} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

def EndpointPathPartition {V : Type cycleUniverse5} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → PositiveSimplePath G),
    Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧
    (∀ v : V, (Finset.univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) ∧
    k ≤ Fintype.card V

def PathOrCycleEdgeSet {V : Type cycleUniverse6} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 0 < p.length ∧ s = p.edgeSet) ∨
  (∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ s = p.edgeSet)

def LovaszPathCyclePartition {V : Type cycleUniverse7} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
    (∀ i, PathOrCycleEdgeSet G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet ∧ 2 * k ≤ Fintype.card V

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

def evenAugmentation {V : Type cycleUniverse8} [Fintype V] (G : SimpleGraph V) :
    SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some u, some v => G.Adj u v
    | none, some v => Even (G.degree v)
    | some u, none => Even (G.degree u)
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact G.irrefl h⟩

@[simp] theorem evenAugmentation_some_adj {V : Type cycleUniverse9} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    (evenAugmentation G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem evenAugmentation_none_adj {V : Type cycleUniverse10} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj none (some v) ↔ Even (G.degree v) := Iff.rfl

@[simp] theorem evenAugmentation_some_none {V : Type cycleUniverse11} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj (some v) none ↔ Even (G.degree v) := Iff.rfl

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section

theorem path_tail_delete_start {V : Type cycleUniverse21} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.tail.edgeSet = {e | e ∈ p.edgeSet ∧ a ∉ e} := by
  cases p with
  | nil => ext e; simp
  | @cons a c b h q =>
    have ha : a ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have hnot : ∀ e ∈ q.edgeSet, a ∉ e := by
      intro e he hae
      exact ha (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e, he, hae⟩))
    ext e
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.mem_edgeSet,
      SimpleGraph.Walk.edges_tail, SimpleGraph.Walk.edges_cons, List.tail_cons, List.mem_cons]
    constructor
    · intro he
      exact ⟨Or.inr he, hnot e he⟩
    · rintro ⟨he | he, hn⟩
      · subst e; exact (hn (by simp)).elim
      · exact he

theorem path_dropLast_delete_end {V : Type cycleUniverse22} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.dropLast.edgeSet = {e | e ∈ p.edgeSet ∧ b ∉ e} := by
  have he : p.dropLast.edgeSet = p.reverse.tail.edgeSet := by
    calc
      _ = p.dropLast.reverse.edgeSet := (SimpleGraph.Walk.edgeSet_reverse _).symm
      _ = _ := by rw [SimpleGraph.Walk.reverse_dropLast, SimpleGraph.Walk.edgeSet_copy]
  rw [he, path_tail_delete_start p.reverse hp.reverse, SimpleGraph.Walk.edgeSet_reverse]

theorem positive_avoids_of_no_incidence {V : Type cycleUniverse23} {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hpos : 0 < p.length)
    (he : ∀ e ∈ p.edgeSet, v ∉ e) : v ∉ p.support := by
  have hn : ¬p.Nil := by intro hz; have := hz.length_eq_zero; omega
  intro hv
  obtain ⟨e, he', hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  exact he e he' hve

theorem delete_vertex_from_path {V : Type cycleUniverse24} [DecidableEq V] {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support) :
    let q := (p.takeUntil v hv).dropLast
    let r := (p.dropUntil v hv).tail
    q.IsPath ∧ r.IsPath ∧ Disjoint q.edgeSet r.edgeSet ∧
    q.edgeSet ∪ r.edgeSet = {e | e ∈ p.edgeSet ∧ v ∉ e} ∧
    (0 < q.length → v ∉ q.support) ∧
    (0 < r.length → v ∉ r.support) ∧
    (0 < q.length → G.Adj (p.takeUntil v hv).penultimate v) ∧
    (0 < r.length → G.Adj v (p.dropUntil v hv).snd) := by
  dsimp only
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have ht : t.IsPath := hp.takeUntil hv
  have hd : d.IsPath := hp.dropUntil hv
  have heq : t.append d = p := p.take_spec hv
  have hqe : t.dropLast.edgeSet = {e | e ∈ t.edgeSet ∧ v ∉ e} :=
    path_dropLast_delete_end t ht
  have hre : d.tail.edgeSet = {e | e ∈ d.edgeSet ∧ v ∉ e} :=
    path_tail_delete_start d hd
  have hdis : Disjoint t.edgeSet d.edgeSet := by
    have hn := hp.isTrail.edges_nodup
    rw [← heq, SimpleGraph.Walk.edges_append] at hn
    have hn' := (List.nodup_append.mp hn).2.2
    apply Set.disjoint_left.mpr
    intro e het hed
    exact hn' e het e hed rfl
  refine ⟨ht.dropLast, hd.tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqe, hre]
    exact hdis.mono (fun _ h => h.1) (fun _ h => h.1)
  · have he : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    rw [hqe, hre]
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rw [← he]
    simp only [Set.mem_union]
    tauto
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hqe ▸ he).2
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hre ▸ he).2
  · intro hpos
    apply t.adj_penultimate
    intro hn
    have hz := hn.length_eq_zero
    change 0 < t.dropLast.length at hpos
    rw [SimpleGraph.Walk.length_dropLast, hz] at hpos
    omega
  · intro hpos
    apply d.adj_snd
    intro hn
    have hz := hn.length_eq_zero
    change 0 < d.tail.length at hpos
    rw [SimpleGraph.Walk.length_tail, hz] at hpos
    omega

structure SimplePathPiece {V : Type cycleUniverse29} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath

namespace SimplePathPiece
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

def Avoiding (p : I → SimplePathPiece G) (v : V) := {i : I // v ∉ (p i).walk.support}
def Meeting (p : I → SimplePathPiece G) (v : V) := {i : I // v ∈ (p i).walk.support}
def DeleteIndex (p : I → SimplePathPiece G) (v : V) :=
  Avoiding p v ⊕ (Meeting p v × Bool)

instance instFintypeAvoiding (p : I → SimplePathPiece G) (v : V) : Fintype (Avoiding p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∉ (p i).walk.support})
instance instFintypeMeeting (p : I → SimplePathPiece G) (v : V) : Fintype (Meeting p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∈ (p i).walk.support})
instance instFintypeDeleteIndex (p : I → SimplePathPiece G) (v : V) : Fintype (DeleteIndex p v) :=
  inferInstanceAs (Fintype (Avoiding p v ⊕ (Meeting p v × Bool)))

def deleted (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → SimplePathPiece G
  | .inl i => p i.val
  | .inr (i,true) => ⟨_,_,((p i.val).walk.takeUntil v i.property).dropLast,
      ((p i.val).isPath.takeUntil i.property).dropLast⟩
  | .inr (i,false) => ⟨_,_,((p i.val).walk.dropUntil v i.property).tail,
      ((p i.val).isPath.dropUntil i.property).tail⟩

def parent (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → I
  | .inl i => i.val
  | .inr (i,_) => i.val

def oldEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl i => (p i.val).start = x ∨ (p i.val).finish = x
  | .inr (i,true) => (p i.val).start = x
  | .inr (i,false) => (p i.val).finish = x

def newEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl _ => False
  | .inr (i,true) => ((p i.val).walk.takeUntil v i.property).penultimate = x
  | .inr (i,false) => ((p i.val).walk.dropUntil v i.property).snd = x

lemma deleted_positive_avoids {V : Type cycleUniverse36} {I : Type cycleUniverse37} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v)
    (hpos : 0 < (deleted p v j).walk.length) : v ∉ (deleted p v j).walk.support := by
  rcases j with i | ⟨i,b⟩
  · exact i.property
  · have h := delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property
    cases b
    · exact h.2.2.2.2.2.1 hpos
    · exact h.2.2.2.2.1 hpos

def deletedInduced (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    SimplePathPiece (G.induce {x | x ≠ v}) := by
  let q := deleted p v j.val
  have havo : ∀ x ∈ q.walk.support, x ∈ ({x | x ≠ v} : Set V) := by
    intro x hx he
    subst x
    exact deleted_positive_avoids p v j.val j.property hx
  exact ⟨_,_, q.walk.induce _ havo, by
    apply SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    simpa using q.isPath⟩

end SimplePathPiece

end
end ErdosGallai.Batch
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

def PositiveSimplePath.mapIso {V : Type cycleUniverse3} {W : Type cycleUniverse4} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (P : PositiveSimplePath G) : PositiveSimplePath H :=
  ⟨f P.start,f P.finish,P.walk.map f.toHom,P.isPath.map f.injective,by simpa using P.positive⟩

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_map {V : Type cycleUniverse9} {I : Type cycleUniverse10} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] [_contextInstance4 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    (deletedInduced p v j).walk.map (SimpleGraph.Embedding.induce _).toHom =
      (deleted p v j.val).walk := by
  exact SimpleGraph.Walk.map_induce _ _

def deletedPositive (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    PositiveSimplePath (G.induce {x | x ≠ v}) :=
  { deletedInduced p v j with
    positive := by
      have h := congrArg SimpleGraph.Walk.length (deletedInduced_map p v j)
      rw [SimpleGraph.Walk.length_map] at h
      rw [h]
      exact j.property }

end SimplePathPiece

def evenAugmentationOldIso {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V) :
    G ≃g (evenAugmentation G).induce {x | x ≠ none} where
  toEquiv := Equiv.optionSubtype none ⟨Equiv.refl (Option V),rfl⟩
  map_rel_iff' := Iff.rfl

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Pairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56 cycleUniverse57 cycleUniverse58 cycleUniverse59 cycleUniverse60 cycleUniverse61 cycleUniverse62 cycleUniverse63 cycleUniverse64

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
open Finset
noncomputable section

def Pairing (V : Type cycleUniverse1) := {f : V → V // Function.Involutive f ∧ ∀ x, f x ≠ x}

namespace Pairing
variable {V : Type cycleUniverse2} {W : Type cycleUniverse3}
instance instCoeFunForall : CoeFun (Pairing V) (fun _ => V → V) := ⟨Subtype.val⟩
instance instFintype [Fintype V] : Fintype (Pairing V) := by
  classical
  unfold Pairing
  infer_instance
instance instDecidableEqOfFintype [Fintype V] : DecidableEq (Pairing V) := Classical.decEq _

@[simp] theorem apply_apply (p : Pairing V) (v : V) : p (p v) = v := p.property.1 v
@[simp] theorem apply_ne (p : Pairing V) (v : V) : p v ≠ v := p.property.2 v

def transport (e : V ≃ W) : Pairing V ≃ Pairing W where
  toFun p := ⟨fun x => e (p (e.symm x)),
    (by intro x; simp), (by intro x h; have := congrArg e.symm h; simp at this)⟩
  invFun p := ⟨fun x => e.symm (p (e x)),
    (by intro x; simp), (by intro x h; have := congrArg e h; simp at this)⟩
  left_inv p := by apply Subtype.ext; funext x; simp
  right_inv p := by apply Subtype.ext; funext x; simp

@[simp] theorem transport_apply (e : V ≃ W) (p : Pairing V) (x : W) :
    transport e p x = e (p (e.symm x)) := rfl

variable [Fintype V]

def oneCount (a b : V) : ℕ := by
  classical
  exact Fintype.card {p : Pairing V // p a = b}
def twoCount (a b c d : V) : ℕ := by
  classical
  exact Fintype.card {p : Pairing V // p a = b ∧ p c = d}

@[simp] theorem oneCount_self (a : V) : oneCount a a = 0 := by
  classical
  unfold oneCount
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p => p.val.apply_ne a p.property⟩

end Pairing
end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section

def finiteAverage {α : Type cycleUniverse4} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section

abbrev PairingSpace (V : Type cycleUniverse19) [Fintype V] := Pairing (V ⊕ Fin (Fintype.card V % 2))

def paired {V : Type cycleUniverse22} [Fintype V] (p : PairingSpace V) (u v : V) : Prop :=
  p (Sum.inl u) = Sum.inl v

instance paired_decidable {V : Type cycleUniverse23} [Fintype V] (p : PairingSpace V) (u v : V) :
    Decidable (paired p u v) := Classical.propDecidable _

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
namespace Pairing
variable {V : Type cycleUniverse39}

def pairSetoid (p : Pairing V) : Setoid V where
  r u v := u = v ∨ p u = v
  iseqv := ⟨fun _ => Or.inl rfl, (by
    intro u v h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by have hh := congrArg p h; simpa using hh.symm)), (by
    intro u v w h1 h2
    rcases h1 with rfl | h1
    · exact h2
    rcases h2 with rfl | h2
    · exact Or.inr h1
    · left
      have hh := congrArg p h1
      simpa only [apply_apply,h2] using hh)⟩

def PairQuotient (p : Pairing V) := Quotient (pairSetoid p)

instance instFintypePairQuotient [Fintype V] (p : Pairing V) : Fintype (PairQuotient p) := by
  classical
  unfold PairQuotient
  infer_instance

instance instDecidableEqPairQuotient (p : Pairing V) : DecidableEq (PairQuotient p) := Classical.decEq _

def project (p : Pairing V) (v : V) : PairQuotient p := Quotient.mk (pairSetoid p) v

end Pairing

def oldProject {V : Type cycleUniverse40} [Fintype V] (p : PairingSpace V) (v : V) : Pairing.PairQuotient p :=
  p.project (Sum.inl v)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section

variable {V : Type cycleUniverse46} {I : Type cycleUniverse47} [Fintype V] [Fintype I] (X : I → Finset V)

abbrev Outside := {v : V // ∀ i, v ∉ X i}
abbrev FoldDomain := Outside X ⊕ (Σ i, X i)

def unfoldVertex : FoldDomain X → V
  | Sum.inl v => v.val
  | Sum.inr v => v.2.val

lemma unfoldVertex_bijective {V : Type cycleUniverse48} {I : Type cycleUniverse49} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise (fun i j => Disjoint (X i) (X j))) :
    Function.Bijective (unfoldVertex X) := by
  classical
  constructor
  · rintro (u | ⟨i,u⟩) (v | ⟨j,v⟩) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change u.val = v.val at h
      exact False.elim (u.property j (h.symm ▸ v.property))
    · change u.val = v.val at h
      exact False.elim (v.property i (h ▸ u.property))
    · change u.val = v.val at h
      have hij : i = j := by
        by_contra hij
        exact Finset.disjoint_left.mp (hd hij) u.property (h.symm ▸ v.property)
      subst j
      exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext h)))
  · intro v
    by_cases h : ∃ i, v ∈ X i
    · obtain ⟨i,hi⟩ := h
      exact ⟨Sum.inr ⟨i,⟨v,hi⟩⟩,rfl⟩
    · exact ⟨Sum.inl ⟨v,by simpa only [not_exists] using h⟩,rfl⟩

def splitEquiv (hd : Pairwise (fun i j => Disjoint (X i) (X j))) : FoldDomain X ≃ V :=
  Equiv.ofBijective (unfoldVertex X) (unfoldVertex_bijective X hd)

abbrev FamilyQuotient (p : ∀ i, PairingSpace (X i)) :=
  Outside X ⊕ (Σ i, Pairing.PairQuotient (p i))

instance instFintypeFamilyQuotient (p : ∀ i, PairingSpace (X i)) : Fintype (FamilyQuotient X p) := by
  classical
  unfold FamilyQuotient
  infer_instance

instance instDecidableEqFamilyQuotient (p : ∀ i, PairingSpace (X i)) : DecidableEq (FamilyQuotient X p) := Classical.decEq _

def foldOnDomain (p : ∀ i, PairingSpace (X i)) : FoldDomain X → FamilyQuotient X p
  | Sum.inl v => Sum.inl v
  | Sum.inr ⟨i,v⟩ => Sum.inr ⟨i,oldProject (p i) v⟩

def familyProject (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) : V → FamilyQuotient X p :=
  foldOnDomain X p ∘ (splitEquiv X hd).symm

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse50} {I : Type cycleUniverse51} [Fintype V] [Fintype I] (X : I → Finset V)

def familyPaired (p : ∀ i, PairingSpace (X i)) (u v : V) : Prop :=
  ∃ (i : I) (hu : u ∈ X i) (hv : v ∈ X i), paired (p i) ⟨u,hu⟩ ⟨v,hv⟩

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CollisionEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse1} [Fintype V] (G : SimpleGraph V)

def neighborsIn (X : Finset V) (v : V) : ℕ :=
  (X.filter (G.Adj v)).card

def internalGraph (X : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ X ∧ v ∈ X
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

def betweenCount (X Y : Finset V) : ℕ := ∑ x ∈ X, neighborsIn G Y x

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section

def CollisionPairs {α : Type cycleUniverse6} {β : Type cycleUniverse7} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) : Finset (Finset α) := by
  classical
  exact (s.powersetCard 2).filter (fun p => (p.image f).card = 1)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def quotientDefect {V : Type cycleUniverse18} {W : Type cycleUniverse19} [Fintype V] (G : SimpleGraph V) (projMap : V → W) : ℕ := by
  classical
  let s := G.edgeFinset
  exact (s.filter (fun e => (Sym2.map projMap e).IsDiag)).card +
    (CollisionPairs (Sym2.map projMap) (s.filter (fun e => ¬(Sym2.map projMap e).IsDiag))).card

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse22} {I : Type cycleUniverse23} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

def vertexPairEvent (p : ∀ i, PairingSpace (X i)) (s : Finset V) : Prop :=
  ∃ u ∈ s, ∃ v ∈ s, u ≠ v ∧ familyPaired X p u v

def wedgeErrors (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) (i : I) (v : V) :=
  (((X i).filter (G.Adj v)).powersetCard 2).filter (vertexPairEvent X p)

def crossGraph (G : SimpleGraph V) (S T : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S))
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.elim (fun h => Or.inr ⟨h.2,h.1⟩)
    (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

end
end ErdosGallai.Batch
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

def edgePairEvent (p : ∀ i, PairingSpace (X i)) (q : Finset (Sym2 V)) : Prop :=
  (q.image (Sym2.map (familyProject X hd p))).card = 1

def DisjointEdgePair (q : Finset (Sym2 V)) : Prop :=
  ∃ u v x y : V, u ≠ v ∧ x ≠ y ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧
    q = {s(u,v),s(x,y)}

def pairErrors (H : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :=
  ((H.edgeFinset.powersetCard 2).filter DisjointEdgePair).filter (edgePairEvent X hd p)

def loopErrors (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) (i : I) :=
  (internalGraph G (X i)).edgeFinset.filter
    (fun e => (Sym2.map (familyProject X hd p) e).IsDiag)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse5} {I : Type cycleUniverse6} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

def wedgeCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun v =>
    (wedgeErrors X G p i v).image (fun q => q.image (fun u => s(v,u)))

def internalCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => pairErrors X hd (internalGraph G (X i)) p

def crossCover (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun i => (Finset.univ.erase i).biUnion fun j =>
    pairErrors X hd (crossGraph G (X i) (X j)) p

def foldErrorBudget (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) : ℕ :=
  ∑ i, ((loopErrors X hd G p i).card +
    (∑ v, (wedgeErrors X G p i v).card) +
    (pairErrors X hd (internalGraph G (X i)) p).card +
    ∑ j ∈ Finset.univ.erase i, (pairErrors X hd (crossGraph G (X i) (X j)) p).card)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V)

def heavyNeighbors (X : Finset V) (a : ℝ) : Finset V :=
  Finset.univ.filter (fun v => a < (neighborsIn G X v : ℝ))

variable {I : Type cycleUniverse12} [Fintype I] (X : I → Finset V)

def heavyDesignated (a : ℝ) (i : I) : SimpleGraph V :=
  crossGraph G (X i) (heavyNeighbors G (X i) a)

def trimHeavyGraph (a : ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ∀ i, ¬ (heavyDesignated G X a i).Adj u v
  symm := ⟨fun _ _ h => ⟨h.1.symm,fun i hi => h.2 i hi.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

structure TrimmedPath {V : Type cycleUniverse21} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : walk.IsPath

theorem close_trimmed_path {V : Type cycleUniverse29} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (q : G.Walk b a) (hp : p.IsPath) (hq : q.IsPath)
    (hlen : 2 ≤ p.length)
    (havoid : ∀ v ∈ q.support, v ≠ a → v ≠ b → v ∉ p.support) :
    (p.append q).IsCycle ∧ (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  refine ⟨hp.isCycle_append hq ?_ (Or.inl (by omega)), Walk.edgeSet_append p q⟩
  rw [List.disjoint_left]
  intro v hvp hvq
  have hva : v ≠ a := by
    intro h; subst v
    have hn := hp.support_nodup
    rw [← p.cons_tail_support] at hn
    exact hn.notMem hvp
  have hvb : v ≠ b := by
    intro h; subst v
    have hn := hq.support_nodup
    rw [← q.cons_tail_support] at hn
    exact hn.notMem hvq
  exact havoid v (List.mem_of_mem_tail hvq) hva hvb (List.mem_of_mem_tail hvp)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

structure PreparedBatch {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise fun i j => Disjoint (X i) (X j)) where
  pairing : ∀ i, PairingSpace (X i)
  quotient : SimpleGraph (FamilyQuotient X pairing)
  retained : Finset (Sym2 V)
  bad : Finset (Sym2 V)
  count : I → ℕ
  path : ∀ i, Fin (count i) → TrimmedPath G
  count_le : ∀ i, count i ≤ 2 * (X i).card
  bad_le : bad.card ≤ 6 * ∑ i, (X i).card
  ends : ∀ i j, 0 < (path i j).walk.length →
    (path i j).start ∈ X i ∧ (path i j).finish ∈ X i ∧ 2 ≤ (path i j).walk.length
  paths_disjoint : Pairwise fun z w : Σ i, Fin (count i) =>
    Disjoint (path z.1 z.2).walk.edgeSet (path w.1 w.2).walk.edgeSet
  bad_paths : ∀ i j, Disjoint (bad : Set (Sym2 V)) (path i j).walk.edgeSet
  retained_paths : ∀ i j, Disjoint (retained : Set (Sym2 V)) (path i j).walk.edgeSet
  bad_retained : Disjoint (bad : Set (Sym2 V)) (retained : Set (Sym2 V))
  cover : (bad : Set (Sym2 V)) ∪ (retained : Set (Sym2 V)) ∪
    (⋃ (i) (j), (path i j).walk.edgeSet) = G.edgeSet
  quotient_edges : quotient.edgeSet =
    (Sym2.map (familyProject X hd pairing)) '' (retained : Set (Sym2 V))
  representatives : ∀ e ∈ quotient.edgeSet, ∃! f,
    f ∈ retained ∧ Sym2.map (familyProject X hd pairing) f = e
  order : Fintype.card (FamilyQuotient X pairing) =
    Fintype.card V - ∑ i, (X i).card / 2

end
end ErdosGallai.Batch
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Batch

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

def avoidGraph (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    SimpleGraph V where
  Adj v w := P.Adj v w ∧ s(v, w) ∉ F ∧ v ∉ W ∧ w ∉ W
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2.1, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨by intro v h; exact P.irrefl h.1⟩

noncomputable def walkBall (G : SimpleGraph V) (s : V) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ p : G.Walk s v, p.length ≤ t)

@[simp] lemma mem_walkBall {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (s v : V) (t : ℕ) :
    v ∈ walkBall G s t ↔ ∃ p : G.Walk s v, p.length ≤ t := by
  classical
  simp [walkBall]

noncomputable def routingG (r h : ℝ) : ℕ := ⌈8 * (r / h) * Real.logb 2 (2 * r)⌉₊

noncomputable def routingDepth (r : ℝ) : ℕ := ⌈Real.logb 2 r⌉₊

noncomputable def routingLength (r h : ℝ) : ℕ := 2 * routingG r h * (1 + routingDepth r)

def incidentEdges (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  F.filter (fun e => v ∈ e)

noncomputable def saturated (F : Finset (Sym2 V)) (h : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => h / 8 ≤ ((incidentEdges F v).card : ℝ))

def pathInterior {P : SimpleGraph V} {s t : V} (q : P.Walk s t) : Finset V :=
  q.support.toFinset \ {s, t}

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

def endpointLoad (A : Finset I) (x y : I → V) (v : V) : ℕ :=
  (A.filter (fun i => x i = v ∨ y i = v)).card

noncomputable def usedEdges (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) : Finset (Sym2 V) :=
  A.biUnion (fun i => (q i).edges.toFinset)

noncomputable def teamInterior (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) : Finset V :=
  (A.filter (fun j => team j = team i)).biUnion (fun j => pathInterior (q j))

structure PartialRoutes (P : SimpleGraph V) (x y : I → V) (team : I → T)
    (Z : I → Finset V) (L : ℕ) (h : ℝ) (A : Finset I)
    (q : ∀ i, P.Walk (x i) (y i)) : Prop where
  simple : ∀ i ∈ A, (q i).IsPath
  short : ∀ i ∈ A, (q i).length ≤ L
  avoids : ∀ i ∈ A, Disjoint (pathInterior (q i)) (Z i)
  edge_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset
  team_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))
  degree : ∀ v, ((incidentEdges (usedEdges A q) v).card : ℝ) ≤ h / 8 + 2 + endpointLoad A x y v

end Families
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CycleLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Batch
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open SimpleGraph

variable {V : Type cycleUniverse1} {G : SimpleGraph V}

structure CycleVisit (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish

inductive VisitChain (G : SimpleGraph V) : V → V → Type _
  | single {u v : V} (p : G.Walk u v) : VisitChain G u v
  | cons {u v w z : V} (p : G.Walk u v) (h : G.Adj v w)
      (q : VisitChain G w z) : VisitChain G u z

namespace VisitChain

variable {u v : V}

def walk : {u v : V} → VisitChain G u v → G.Walk u v
  | _, _, .single p => p
  | _, _, .cons p h q => p.append (.cons h q.walk)

def visits : {u v : V} → VisitChain G u v → List (CycleVisit G)
  | u, v, .single p => [⟨u,v,p⟩]
  | u, _, .cons (v := v) p _ q => ⟨u,v,p⟩ :: q.visits

def links : {u v : V} → VisitChain G u v → Set (Sym2 V)
  | _, _, .single _ => ∅
  | _, _, .cons (v := v) (w := w) _ _ q => {s(v,w)} ∪ q.links

def switchEdges (q : VisitChain G u v) : Set (Sym2 V) :=
  ⋃ p ∈ q.visits, p.walk.edgeSet

lemma mem_support_iff (q : VisitChain G u v) (x : V) :
    x ∈ q.walk.support ↔ ∃ p ∈ q.visits, x ∈ p.walk.support := by
  induction q with
  | single p => simp [walk, visits]
  | cons p h q ih =>
    simp only [walk, Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
      ih, visits, List.mem_cons]
    constructor
    · rintro (hp | rfl | ⟨r,hr,hx⟩)
      · exact ⟨_, Or.inl rfl, hp⟩
      · exact ⟨_, Or.inl rfl, p.end_mem_support⟩
      · exact ⟨r, Or.inr hr, hx⟩
    · rintro ⟨r, rfl | hr, hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inr ⟨r,hr,hx⟩)

lemma isPath_of_separated (q : VisitChain G u v)
    (hp : ∀ p ∈ q.visits, p.walk.IsPath)
    (hd : q.visits.Pairwise (fun p r => p.walk.support.Disjoint r.walk.support)) :
    q.walk.IsPath := by
  induction q with
  | single p => exact hp ⟨_,_,p⟩ (by simp [visits])
  | cons p h q ih =>
    have hpd := (List.pairwise_cons.mp hd).1
    have hqt := ih (fun r hr => hp r (by simp [visits, hr]))
      (List.pairwise_cons.mp hd).2
    have hpt := hp ⟨_,_,p⟩ (by simp [visits])
    have hdisj : p.support.Disjoint q.walk.support := by
      rw [List.disjoint_left]
      intro x hx hqx
      obtain ⟨r,hr,hxr⟩ := q.mem_support_iff x |>.mp hqx
      exact hpd r hr hx hxr
    apply Walk.IsPath.mk'
    simpa only [walk, Walk.support_append, Walk.support_cons, List.tail_cons]
      using (List.nodup_append').mpr ⟨hpt.support_nodup, hqt.support_nodup, hdisj⟩

lemma length_visits_le (q : VisitChain G u v) : q.visits.length ≤ q.walk.length + 1 := by
  induction q with
  | single p => simp [visits, walk]
  | cons p h q ih => simp only [visits, List.length_cons, walk, Walk.length_append,
      Walk.length_cons]; omega

lemma edgeSet_eq (q : VisitChain G u v) :
    q.walk.edgeSet = q.links ∪ q.switchEdges := by
  induction q with
  | single p => simp [walk, links, switchEdges, visits]
  | cons p h q ih =>
    simp only [walk, Walk.edgeSet_append, Walk.edgeSet_cons, ih, links,
      switchEdges, visits]
    ext e
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_iUnion, List.mem_cons, exists_prop, or_and_right, exists_or, exists_eq_left]
    tauto

theorem close_cycle (q : VisitChain G u v) (hc : G.Adj v u)
    (hp : ∀ p ∈ q.visits, p.walk.IsPath)
    (hd : q.visits.Pairwise (fun p r => p.walk.support.Disjoint r.walk.support))
    (hn : 3 ≤ q.visits.length) :
    (Walk.cons hc q.walk).IsCycle ∧
    (Walk.cons hc q.walk).edgeSet = {s(v,u)} ∪ q.links ∪ q.switchEdges ∧
    3 ≤ (Walk.cons hc q.walk).length := by
  have hpath := q.isPath_of_separated hp hd
  have hlength := q.length_visits_le
  have he : s(v,u) ∉ q.walk.edges := by
    intro he
    have hh := hpath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    omega
  refine ⟨Path.cons_isCycle ⟨q.walk,hpath⟩ hc he, ?_, ?_⟩
  · rw [Walk.edgeSet_cons, q.edgeSet_eq]
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · simp only [Walk.length_cons]
    omega

end VisitChain

namespace VisitChain
variable {W : Type cycleUniverse2} {Q : SimpleGraph W}

def of_walk (s t : W → V) (q : ∀ z, G.Walk (s z) (t z)) :
    {a b : W} → (p : Q.Walk a b) →
    (∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) → VisitChain G (s a) (t b)
  | _, _, .nil, _ => .single (q _)
  | a, b, .cons (v := c) h p, hr => .cons (q a)
      (hr ⟨(a,c),h⟩ (by simp))
      (of_walk s t q p (by intro d hd; exact hr d (by simp [hd])))

lemma of_walk_visits (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).visits = p.support.map (fun z => (⟨s z,t z,q z⟩ : CycleVisit G)) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [of_walk, visits, ih]

lemma of_walk_links (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).links = {e | ∃ d ∈ p.darts, e = s(t d.fst,s d.snd)} := by
  induction p with
  | nil => ext e; simp [of_walk, links]
  | cons h p ih =>
    ext e
    simp [of_walk, links, ih,  ]

lemma of_walk_switchEdges (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).switchEdges = ⋃ z ∈ p.support, (q z).edgeSet := by
  rw [switchEdges, of_walk_visits]
  ext e
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨r,⟨z,hz,rfl⟩,he⟩
    exact ⟨z,hz,he⟩
  · rintro ⟨z,hz,he⟩
    exact ⟨⟨s z,t z,q z⟩,⟨z,hz,rfl⟩,he⟩

end VisitChain

theorem lift_quotient_cycle {W : Type cycleUniverse3} {Q : SimpleGraph W}
    (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hr : ∀ d ∈ p.dropLast.darts, G.Adj (t d.fst) (s d.snd))
    (hc : G.Adj (t p.penultimate) (s a))
    (hq : ∀ z ∈ p.dropLast.support, (q z).IsPath)
    (hsep : ∀ z ∈ p.dropLast.support, ∀ w ∈ p.dropLast.support,
      z ≠ w → (q z).support.Disjoint (q w).support) :
    ∃ c : G.Walk (t p.penultimate) (t p.penultimate), c.IsCycle ∧
      c.edgeSet = {s(t p.penultimate,s a)} ∪
        {e | ∃ d ∈ p.dropLast.darts, e = s(t d.fst,s d.snd)} ∪
        (⋃ z ∈ p.dropLast.support, (q z).edgeSet) := by
  let chain := VisitChain.of_walk s t q p.dropLast hr
  have hv : chain.visits = p.dropLast.support.map (fun z => (⟨s z,t z,q z⟩ : CycleVisit G)) :=
    VisitChain.of_walk_visits s t q p.dropLast hr
  have hpaths : ∀ v ∈ chain.visits, v.walk.IsPath := by
    intro v hvv
    rw [hv] at hvv
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hvv
    exact hq z hz
  have hpair : chain.visits.Pairwise (fun v w => v.walk.support.Disjoint w.walk.support) := by
    rw [hv, List.pairwise_map]
    apply (List.pairwise_iff_getElem).mpr
    intro i j hi hj hij
    have hne : p.dropLast.support[i] ≠ p.dropLast.support[j] := by
      intro he
      have hij' := hp.isPath_dropLast.support_nodup.getElem_inj_iff.mp he
      omega
    exact hsep _ (List.getElem_mem _) _ (List.getElem_mem _) hne
  have hn : 3 ≤ chain.visits.length := by
    rw [hv, List.length_map, Walk.length_support, Walk.length_dropLast]
    have := hp.three_le_length
    omega
  obtain ⟨hcycle,hedges,_⟩ := chain.close_cycle hc hpaths hpair hn
  refine ⟨Walk.cons hc chain.walk,hcycle,?_⟩
  rw [hedges, VisitChain.of_walk_links, VisitChain.of_walk_switchEdges]

noncomputable section
attribute [local instance] Classical.propDecidable

def portFrom {A : Type cycleUniverse5} {W : Type cycleUniverse6} (L : List A) (f : A → W) (g : A → V)
    (v₀ : V) (z : W) : V :=
  if h : ∃ d ∈ L, f d = z then g h.choose else v₀

lemma last_dart_mem {W : Type cycleUniverse10} {Q : SimpleGraph W} {a b : W}
    (p : Q.Walk a b) (hp : ¬p.Nil) :
    (⟨(p.penultimate,b),p.adj_penultimate hp⟩ : Q.Dart) ∈ p.darts := by
  have he := congrArg Walk.darts (p.concat_dropLast (p.adj_penultimate hp))
  rw [Walk.darts_concat] at he
  rw [← he]
  simp

lemma cycle_darts_split {W : Type cycleUniverse11} {Q : SimpleGraph W} {a b : W}
    (p : Q.Walk a b) (hp : ¬p.Nil) :
    p.darts = p.dropLast.darts ++ [⟨(p.penultimate,b),p.adj_penultimate hp⟩] := by
  have he := congrArg Walk.darts (p.concat_dropLast (p.adj_penultimate hp))
  simpa only [Walk.darts_concat, List.concat_eq_append] using he.symm

theorem inflate_represented_cycle {W : Type cycleUniverse12} {Q : SimpleGraph W}
    (R : Q.Dart → G.Dart) (s t : W → V)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hports : ∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd)
    (q : ∀ z, G.Walk (s z) (t z))
    (hq : ∀ z ∈ p.dropLast.support, (q z).IsPath)
    (hsep : ∀ z ∈ p.dropLast.support, ∀ w ∈ p.dropLast.support,
      z ≠ w → (q z).support.Disjoint (q w).support) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.edgeSet = {e | ∃ d ∈ p.darts, e = (R d).edge} ∪
        (⋃ z ∈ p.dropLast.support, (q z).edgeSet) := by
  let last : Q.Dart := ⟨(p.penultimate,a),p.adj_penultimate hp.not_nil⟩
  have hlast : last ∈ p.darts := last_dart_mem p hp.not_nil
  have hsub : p.dropLast.darts ⊆ p.darts := by
    rw [Walk.darts_dropLast]; exact List.dropLast_subset _
  have hed : ∀ d ∈ p.darts, s(t d.fst,s d.snd) = (R d).edge := by
    intro d hd
    rw [(hports d hd).1,(hports d hd).2]
    rfl
  have hadj : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd) := by
    intro d hd
    rw [(hports d hd).1,(hports d hd).2]
    exact (R d).adj
  obtain ⟨c,hc,he⟩ := lift_quotient_cycle s t q p hp
    (fun d hd => hadj d (hsub hd)) (hadj last hlast) hq hsep
  refine ⟨_,c,hc,?_⟩
  rw [he]
  have hlinks : {s(t p.penultimate,s a)} ∪
      {e | ∃ d ∈ p.dropLast.darts, e = s(t d.fst,s d.snd)} =
      {e | ∃ d ∈ p.darts, e = (R d).edge} := by
    ext e
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨d,hd,rfl⟩)
      · exact ⟨last,hlast,hed last hlast⟩
      · exact ⟨d,hsub hd,hed d (hsub hd)⟩
    · rintro ⟨d,hd,rfl⟩
      rw [cycle_darts_split p hp.not_nil] at hd
      simp only [List.mem_append,List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact Or.inr ⟨d,hd,(hed d (hsub hd)).symm⟩
      · exact Or.inl (hed last hlast).symm
  rw [hlinks]

def cyclePortSet {W : Type cycleUniverse15} (S : Set W) (s t : W → V) : Set V :=
  {v | ∃ z ∈ S, v = s z ∨ v = t z}

def visitInterior {W : Type cycleUniverse16} (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    (z : W) : Set V := {x | x ∈ (q z).support ∧ x ≠ s z ∧ x ≠ t z}

theorem switch_supports_separated {W : Type cycleUniverse17}
    (S : Set W) (projMap : V → W) (s t : W → V)
    (q : ∀ z, G.Walk (s z) (t z))
    (hproj : ∀ z ∈ S, projMap (s z) = z ∧ projMap (t z) = z)
    (havoid : ∀ z ∈ S, Disjoint (visitInterior s t q z) (cyclePortSet S s t))
    (hinter : ∀ z ∈ S, ∀ w ∈ S, z ≠ w →
      Disjoint (visitInterior s t q z) (visitInterior s t q w)) :
    ∀ z ∈ S, ∀ w ∈ S, z ≠ w → (q z).support.Disjoint (q w).support := by
  intro z hz w hw hzw
  rw [List.disjoint_left]
  intro x hx hy
  by_cases hxend : x = s z ∨ x = t z
  · have hxZ : x ∈ cyclePortSet S s t := ⟨z,hz,hxend⟩
    by_cases hyend : x = s w ∨ x = t w
    · have hxprojMap : projMap x = z := by rcases hxend with rfl | rfl <;> simp_all
      have hyprojMap : projMap x = w := by rcases hyend with rfl | rfl <;> simp_all
      exact hzw (hxprojMap.symm.trans hyprojMap)
    · exact Set.disjoint_left.mp (havoid w hw)
        ⟨hy,fun he => hyend (Or.inl he),fun he => hyend (Or.inr he)⟩ hxZ
  · have hxI : x ∈ visitInterior s t q z :=
      ⟨hx,fun he => hxend (Or.inl he),fun he => hxend (Or.inr he)⟩
    by_cases hyend : x = s w ∨ x = t w
    · exact Set.disjoint_left.mp (havoid z hz) hxI ⟨w,hw,hyend⟩
    · exact Set.disjoint_left.mp (hinter z hz w hw hzw) hxI
        ⟨hy,fun he => hyend (Or.inl he),fun he => hyend (Or.inr he)⟩

theorem cyclePortSet_eq_representative_vertices {W : Type cycleUniverse18} {Q : SimpleGraph W}
    (R : Q.Dart → G.Dart) (s t : W → V)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hports : ∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd) :
    cyclePortSet {z | z ∈ p.dropLast.support} s t =
      {v | ∃ d ∈ p.darts, v = (R d).fst ∨ v = (R d).snd} := by
  have hmF : p.darts.map (fun d => d.fst) = p.dropLast.support := by
    rw [Walk.map_fst_darts, p.support_dropLast hp.not_nil]
  have hmS : ∀ z, z ∈ p.darts.map (fun d => d.snd) ↔ z ∈ p.dropLast.support := by
    intro z
    rw [Walk.map_snd_darts, p.support_dropLast hp.not_nil]
    exact p.tail_support_perm_dropLast_support.mem_iff
  ext v
  constructor
  · rintro ⟨z,hz,hv | hv⟩
    · obtain ⟨d,hd,hds⟩ := List.mem_map.mp ((hmS z).mpr hz)
      exact ⟨d,hd,Or.inr (hv.trans (by rw [← hds]; exact (hports d hd).2))⟩
    · have hz' : z ∈ p.darts.map (fun d => d.fst) := by rwa [hmF]
      obtain ⟨d,hd,hdf⟩ := List.mem_map.mp hz'
      exact ⟨d,hd,Or.inl (hv.trans (by rw [← hdf]; exact (hports d hd).1))⟩
  · rintro ⟨d,hd,hv | hv⟩
    · refine ⟨d.fst,?_,Or.inr (hv.trans (hports d hd).1.symm)⟩
      rw [← hmF]
      exact List.mem_map.mpr ⟨d,hd,rfl⟩
    · exact ⟨d.snd,(hmS _).mp (List.mem_map.mpr ⟨d,hd,rfl⟩),
        Or.inl (hv.trans (hports d hd).2.symm)⟩

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Templates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def demandLoad {I : Type cycleUniverse1} {V : Type cycleUniverse2} [Fintype I] (x y : I → V) (v : V) : ℕ :=
  (univ.filter fun i => x i = v ∨ y i = v).card

lemma start_has_incident_edge {V : Type cycleUniverse6} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ¬p.Nil) :
    ∃ w, G.Adj a w ∧ s(a,w) ∈ p.edgeSet := by
  exact ⟨p.snd,p.adj_snd hp,p.mk_start_snd_mem_edges hp⟩

lemma finish_has_incident_edge {V : Type cycleUniverse7} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ¬p.Nil) :
    ∃ w, G.Adj b w ∧ s(b,w) ∈ p.edgeSet := by
  refine ⟨p.penultimate,(p.adj_penultimate hp).symm,?_⟩
  change s(b,p.penultimate) ∈ p.edges
  simpa only [Sym2.eq_swap] using p.mk_penultimate_end_mem_edges hp

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet

noncomputable section
open SimpleGraph

lemma edgeDecomposition_of_indexed {V I : Type} [Fintype I] (G : SimpleGraph V)
    (parts : I → Set (Sym2 V)) (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hu : (⋃ i, parts i) = G.edgeSet) : EdgeDecomposition G (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨fun j => parts (e.symm j), fun j => hp _, ?_, ?_⟩
  · intro i j hij
    exact hd (fun he => hij (e.symm.injective he))
  · ext x
    simp only [Set.mem_iUnion]
    rw [← hu]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i, by simpa using hi⟩

theorem edgeDecomposition_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  apply edgeDecomposition_of_indexed G (fun e : G.edgeSet => {e.1})
  · intro e; exact Or.inr ⟨e.1,e.2,rfl⟩
  · intro e d hed
    exact Set.disjoint_singleton.mpr (fun h => hed (Subtype.ext h))
  · ext e; simp

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def decompositionCost {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, EdgeDecomposition G k from ⟨_,edgeDecomposition_singleEdges G⟩)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

structure CycleOutline {V : Type} (G : SimpleGraph V) where
  W : Type
  finiteW : Fintype W
  Q : SimpleGraph W
  base : W
  cycle : Q.Walk base base
  isCycle : cycle.IsCycle
  rep : Q.Dart → G.Dart
  start : W → V
  finish : W → V
  project : V → W
  ports : ∀ d ∈ cycle.darts, finish d.fst = (rep d).fst ∧ start d.snd = (rep d).snd
  projects : ∀ z ∈ cycle.dropLast.support, project (start z) = z ∧ project (finish z) = z
  outside : ∀ z, z ∉ cycle.dropLast.support → start z = finish z
attribute [instance] CycleOutline.finiteW

namespace CycleOutline
variable {V : Type} {G : SimpleGraph V} (c : CycleOutline G)

def edges : Set (Sym2 V) := {e | ∃ d ∈ c.cycle.darts, e = (c.rep d).edge}
def vertices : Finset V := c.cycle.darts.toFinset.biUnion fun d => {(c.rep d).fst,(c.rep d).snd}
abbrev Switch := {z : c.W // z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z}
instance instFintypeSwitch : Fintype c.Switch := inferInstanceAs (Fintype {_z : c.W // _})

lemma edges_subset : c.edges ⊆ G.edgeSet := by
  rintro e ⟨d,hd,rfl⟩; exact (c.rep d).edge_mem

lemma outgoing (z : c.W) (hz : z ∈ c.cycle.dropLast.support) :
    ∃ d ∈ c.cycle.darts, d.fst = z := by
  have h : z ∈ c.cycle.darts.map (fun d => d.fst) := by
    rw [Walk.map_fst_darts,← c.cycle.support_dropLast c.isCycle.not_nil]; exact hz
  exact List.mem_map.mp h

lemma incoming (z : c.W) (hz : z ∈ c.cycle.dropLast.support) :
    ∃ d ∈ c.cycle.darts, d.snd = z := by
  have h : z ∈ c.cycle.darts.map (fun d => d.snd) := by
    rw [Walk.map_snd_darts]
    apply c.cycle.tail_support_perm_dropLast_support.mem_iff.mpr
    rw [← c.cycle.support_dropLast c.isCycle.not_nil]; exact hz
  exact List.mem_map.mp h

lemma endpoint_incident (z : c.Switch) (v : V) (hv : c.start z = v ∨ c.finish z = v) :
    ∃ w, G.Adj v w ∧ s(v,w) ∈ c.edges := by
  rcases hv with rfl | rfl
  · obtain ⟨d,hd,he⟩ := c.incoming z z.property.1
    have hh := (c.ports d hd).2
    rw [he] at hh
    refine ⟨(c.rep d).fst,?_,?_⟩
    · rw [hh]; exact (c.rep d).adj.symm
    · refine ⟨d,hd,?_⟩
      rw [hh]; exact Sym2.eq_swap
  · obtain ⟨d,hd,he⟩ := c.outgoing z z.property.1
    have hh := (c.ports d hd).1
    rw [he] at hh
    refine ⟨(c.rep d).snd,?_,?_⟩
    · rw [hh]; exact (c.rep d).adj
    · refine ⟨d,hd,?_⟩; rw [hh]; rfl

lemma endpoint_unique (z w : c.Switch) (v : V)
    (hz : c.start z = v ∨ c.finish z = v) (hw : c.start w = v ∨ c.finish w = v) : z = w := by
  apply Subtype.ext
  have hf : ∀ (z : c.Switch), c.start z = v ∨ c.finish z = v → c.project v = z := by
    intro z hz
    rcases hz with h | h
    · rw [← h]; exact (c.projects z z.property.1).1
    · rw [← h]; exact (c.projects z z.property.1).2
  exact (hf z hz).symm.trans (hf w hw)

lemma mem_vertices (v : V) : v ∈ c.vertices ↔ ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd := by
  simp [vertices]

theorem complete [DecidableEq V]
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z))
    (hs : ∀ z, (route z).IsPath)
    (ha : ∀ z, Disjoint (pathInterior (route z)) c.vertices)
    (hd : Pairwise fun z w => Disjoint (pathInterior (route z)) (pathInterior (route w))) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧
      p.edgeSet = c.edges ∪ ⋃ z, (route z).edgeSet := by
  classical
  let visits : ∀ z, G.Walk (c.start z) (c.finish z) := fun z =>
    if h : z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z then route ⟨z,h⟩
    else (Walk.nil : G.Walk (c.start z) (c.start z)).copy rfl (by
      by_cases hz : z ∈ c.cycle.dropLast.support
      · exact not_not.mp (fun hn => h ⟨hz,hn⟩)
      · exact c.outside z hz)
  have hv (z : c.Switch) : visits z = route z := by simp only [visits,dite_eq_left z.property]
  have hnil (z : c.W) (hz : ¬(z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z)) :
      (visits z).Nil := by simp only [visits,dite_eq_right hz,Walk.nil_copy,Walk.nil_nil]
  have hpath : ∀ z, (visits z).IsPath := by
    intro z
    by_cases hz : z ∈ c.cycle.dropLast.support ∧ c.start z ≠ c.finish z
    · simpa only [visits,dite_eq_left hz] using hs ⟨z,hz⟩
    · simp [visits,dite_eq_right hz]
  have hinter (z : c.W) : visitInterior c.start c.finish visits z = (pathInterior (visits z):Set V) := by
    ext v; simp [visitInterior,pathInterior]
  have h_avoid : ∀ z ∈ c.cycle.dropLast.support, Disjoint
      (visitInterior c.start c.finish visits z) {v | ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd} := by
    intro z hz
    rw [hinter]
    have he : {v | ∃ d ∈ c.cycle.darts, v = (c.rep d).fst ∨ v = (c.rep d).snd} = (c.vertices:Set V) := by
      ext v; exact (c.mem_vertices v).symm
    rw [he,Finset.disjoint_coe]
    by_cases hne : c.start z ≠ c.finish z
    · rw [hv ⟨z,hz,hne⟩]; exact ha _
    · have hn := hnil z (by tauto)
      simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn]
  have h_dis : Pairwise fun z w : {z // z ∈ c.cycle.dropLast.support} =>
      Disjoint (visitInterior c.start c.finish visits z) (visitInterior c.start c.finish visits w) := by
    intro z w hzw
    rw [hinter,hinter,Finset.disjoint_coe]
    by_cases hz : c.start z ≠ c.finish z
    · by_cases hw : c.start w ≠ c.finish w
      · rw [hv ⟨z,z.property,hz⟩,hv ⟨w,w.property,hw⟩]
        exact hd (fun h => hzw (Subtype.ext (congrArg (fun t : c.Switch => (t:c.W)) h)))
      · have hn := hnil w (by tauto); simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn] ; tauto
    · have hn := hnil z (by tauto); simp [Finset.disjoint_left,pathInterior,Walk.nil_iff_support_eq.mp hn]
  obtain ⟨v,p,hp,hedge⟩ := inflate_represented_cycle c.rep c.start c.finish c.cycle c.isCycle c.ports visits
    (fun z _ => hpath z) (switch_supports_separated {z | z ∈ c.cycle.dropLast.support}
      c.project c.start c.finish visits c.projects
      (by
        intro z hz
        rw [cyclePortSet_eq_representative_vertices c.rep c.start c.finish c.cycle c.isCycle c.ports]
        exact h_avoid z hz)
      (fun z hz w hw hzw => h_dis (show (⟨z,hz⟩:{z // z ∈ c.cycle.dropLast.support}) ≠ ⟨w,hw⟩ from
        fun h => hzw (congrArg Subtype.val h))))
  refine ⟨v,p,hp,hedge.trans ?_⟩
  congr 1
  ext e
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨z,hz,he⟩
    by_cases hne : c.start z ≠ c.finish z
    · exact ⟨⟨z,hz,hne⟩,by rwa [hv ⟨z,hz,hne⟩] at he⟩
    · have hn := hnil z (by tauto)
      have hh := he
      simp [Walk.edgeSet,Walk.edges_eq_nil.mpr hn] at hh
  · rintro ⟨z,he⟩; exact ⟨z,z.property.1,by rwa [hv]⟩

end CycleOutline
end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

structure RoutingTemplate {V : Type} (G : SimpleGraph V) where
  Arity : Type
  finiteArity : Fintype Arity
  x : Arity → V
  y : Arity → V
  ne : ∀ i, x i ≠ y i
  edges : Set (Sym2 V)
  subset : edges ⊆ G.edgeSet
  vertices : Finset V
  incident : ∀ i v, x i = v ∨ y i = v → ∃ w, s(v,w) ∈ edges
  unique : ∀ i j v, (x i = v ∨ y i = v) → (x j = v ∨ y j = v) → i = j
  complete : ∀ q : ∀ i, G.Walk (x i) (y i),
    (∀ i, (q i).IsPath) →
    (∀ i, Disjoint (pathInterior (q i)) vertices) →
    Pairwise (fun i j => Disjoint (pathInterior (q i)) (pathInterior (q j))) →
    CycleOrSingleEdge G (edges ∪ ⋃ i, (q i).edgeSet)
attribute [instance] RoutingTemplate.finiteArity

namespace RoutingTemplate
variable {V : Type} {G : SimpleGraph V}

def ofCycle (c : CycleOutline G) : RoutingTemplate G where
  Arity := c.Switch
  finiteArity := inferInstance
  x := fun i => c.start i
  y := fun i => c.finish i
  ne := fun i => i.property.2
  edges := c.edges
  subset := c.edges_subset
  vertices := c.vertices
  incident := fun i v h => by obtain ⟨w,_,he⟩ := c.endpoint_incident i v h; exact ⟨w,he⟩
  unique := c.endpoint_unique
  complete := by
    intro q hs ha hd
    obtain ⟨v,p,hp,he⟩ := c.complete q hs ha hd
    exact Or.inl ⟨v,p,hp,he.symm⟩

def ofSingle (e : Sym2 V) (he : e ∈ G.edgeSet) : RoutingTemplate G where
  Arity := Empty
  finiteArity := inferInstance
  x := Empty.elim
  y := Empty.elim
  ne := fun i => i.elim
  edges := {e}
  subset := Set.singleton_subset_iff.mpr he
  vertices := ∅
  incident := fun i => i.elim
  unique := fun i => i.elim
  complete := by intro q _ _ _; exact Or.inr ⟨e,he,by simp⟩

def ofPath {x y : V} (p : G.Walk x y) (hp : p.IsPath) (hl : 2 ≤ p.length) : RoutingTemplate G where
  Arity := Unit
  finiteArity := inferInstance
  x := fun _ => y
  y := fun _ => x
  ne := fun _ he => by
    have hn : p.Nil := hp.nil_iff_eq.mpr he.symm
    have := Walk.length_eq_zero_iff.mpr hn
    omega
  edges := p.edgeSet
  subset := p.edges_subset_edgeSet
  vertices := p.support.toFinset
  incident := by
    intro i v hv
    have hn : ¬p.Nil := fun h => by have := Walk.length_eq_zero_iff.mpr h; omega
    rcases hv with rfl | rfl
    · obtain ⟨w,_,he⟩ := finish_has_incident_edge p hn; exact ⟨w,he⟩
    · obtain ⟨w,_,he⟩ := start_has_incident_edge p hn; exact ⟨w,he⟩
  unique := fun _ _ _ _ _ => Subsingleton.elim _ _
  complete := by
    intro q hs ha hd
    obtain ⟨hc,he⟩ := close_trimmed_path p (q ()) hp (hs ()) hl (by
      intro v hv hxa hxb hpv
      exact Finset.disjoint_left.mp (ha ())
        (by simp [pathInterior,hv,hxa,hxb]) (List.mem_toFinset.mpr hpv))
    refine Or.inl ⟨x,p.append (q ()),hc,?_⟩
    have hh : ∀ i : Unit, q i = q () := fun i => by cases i; rfl
    simp_rw [hh,Set.iUnion_const]
    exact he.symm

end RoutingTemplate

end
end ErdosGallai.Batch
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

structure BatchTemplateFamily {V I : Type} [Fintype I]
    (G J : SimpleGraph V) (X : I → Finset V) (W : Finset V) (bad : Finset (Sym2 V)) (k : ℕ) where
  Index : Type
  finiteIndex : Fintype Index
  block : Index → RoutingTemplate G
  count : Fintype.card Index ≤ k + 2 * ∑ i, (X i).card
  disjoint : Pairwise fun i j => Disjoint (block i).edges (block j).edges
  bad_disjoint : ∀ i, Disjoint (bad : Set (Sym2 V)) (block i).edges
  cover : (bad : Set (Sym2 V)) ∪ (⋃ i, (block i).edges) = J.edgeSet
  arity : ∀ i, Fintype.card (block i).Arity ≤ W.card
  vertices : ∀ i, (block i).vertices.card ≤ 2*W.card
  owner : (i : Index) → (block i).Arity → I
  ends : ∀ i j, (block i).x j ∈ X (owner i j) ∧ (block i).y j ∈ X (owner i j)
attribute [instance] BatchTemplateFamily.finiteIndex

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CoupledResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch.Splitting
open MeasureTheory ProbabilityTheory Finset Real

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

def edgeColorMeasure (V : Type cycleUniverse5) [Fintype V] (l : ℕ) [NeZero l] :
    Measure (Sym2 V → Fin l) :=
  Measure.pi (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure)

instance edgeColorMeasure_probability (l : ℕ) [NeZero l] :
    IsProbabilityMeasure (edgeColorMeasure V l) := by
  unfold edgeColorMeasure
  infer_instance

def colorIndicator {l : ℕ} (i : Fin l) (e : Sym2 V) (ω : Sym2 V → Fin l) : ℝ :=
  if ω e = i then 1 else 0

def colorGraph (P : SimpleGraph V) {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    SimpleGraph V where
  Adj x y := P.Adj x y ∧ ω s(x,y) = i
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact P.irrefl h.1⟩

instance colorGraph_decidable (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    DecidableRel (colorGraph P ω i).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

end

open Filter Asymptotics
open scoped Topology

noncomputable def edgeSplittingScaleError (c : ℝ) (l : ℕ) (D : ℝ) : ℝ :=
  (l : ℝ) * (Real.exp (D^(51/50 : ℝ) * Real.exp ((-(c / (8*l))) * D^(9/10 : ℝ))) - 1)

universe u

end ErdosGallai.Batch.Splitting

namespace ErdosGallai.Batch
noncomputable section
open Real

def inductionPhi (x : ℝ) : ℝ :=
  if x = 1 then 1/2 else max (1/2) (1 - 1 / sqrt (logb 2 x))

def inductionDelta : ℝ := 1 / sqrt (3/10) - 1

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

def routerRemainder {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) : SimpleGraph V :=
  R \ SimpleGraph.fromEdgeSet used

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.DepthFirstSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
universe u
open Finset SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

structure DFSState (G : SimpleGraph V) where
  stack : List V
  finished : Finset V
  unexplored : Finset V
  nodup : stack.Nodup
  chain : stack.IsChain G.Adj
  f_s : Disjoint finished stack.toFinset
  f_u : Disjoint finished unexplored
  s_u : Disjoint stack.toFinset unexplored
  cover : finished ∪ stack.toFinset ∪ unexplored = univ
  separation : ∀ x ∈ finished, ∀ y ∈ unexplored, ¬ G.Adj x y

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse2} [Fintype V] [DecidableEq V]

def externalNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)

def VertexExpansion (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) : Prop :=
  ∀ U : Finset V, U.Nonempty → 2 * U.card ≤ Fintype.card V →
    α * U.card ≤ ((externalNeighbors G U).card : ℝ)

end ErdosGallai.Scale
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ExpansionBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]
def avoidGraph (G : SimpleGraph V) (J : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ J ∧ y ∉ J
  symm := ⟨fun _x _y h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _x h => G.irrefl h.1⟩

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open Finset SimpleGraph Classical
variable {V : Type cycleUniverse5} [Fintype V] [DecidableEq V]

def SupportedOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A

structure AssignedPiece (V : Type cycleUniverse6) [DecidableEq V] where
  vertices : Finset V
  graph : SimpleGraph V
  supported : SupportedOn graph vertices

noncomputable def restrictGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

noncomputable def crossingGraph (G : SimpleGraph V) (A B : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inr ⟨h.2,h.1⟩)
    (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

noncomputable def edgeOccurrences (L : List (SimpleGraph V)) (x y : V) : ℕ := by
  classical
  exact L.countP (fun H => H.Adj x y)

def GraphPartition (G : SimpleGraph V) (L : List (SimpleGraph V)) : Prop :=
  ∀ x y, edgeOccurrences L x y = if G.Adj x y then 1 else 0

noncomputable def edgeCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

noncomputable def cutCount (G : SimpleGraph V) (A B : Finset V) : ℕ := by
  classical
  exact (G.interedges A B).card

def CutExpansionOn (G : SimpleGraph V) (A : Finset V) (h : ℝ) : Prop :=
  ∀ U ⊆ A, h * min (U.card : ℝ) ((A \ U).card : ℝ) ≤ cutCount G U (A \ U)

@[simp] lemma edgeOccurrences_nil {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (x y : V) : edgeOccurrences [] x y = 0 := by
  classical
  simp [edgeOccurrences]
@[simp] lemma edgeOccurrences_cons {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (H : SimpleGraph V) (L) (x y : V) :
    edgeOccurrences (H::L) x y = (if H.Adj x y then 1 else 0) + edgeOccurrences L x y := by
  classical
  simp [edgeOccurrences, List.countP_cons, Nat.add_comm]
@[simp] lemma edgeOccurrences_append {V : Type cycleUniverse9} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L M : List (SimpleGraph V)) (x y : V) :
    edgeOccurrences (L++M) x y = edgeOccurrences L x y + edgeOccurrences M x y := by
  classical
  simp [edgeOccurrences]

@[simp] lemma edgeCount_bot {V : Type cycleUniverse13} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : edgeCount (⊥ : SimpleGraph V) = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] at he

open Real

noncomputable def splitPotential (T x : ℝ) : ℝ :=
  1 + 1 / logb 2 (T/2) - 1 / logb 2 (max x (T/2))

noncomputable def externalOn (G : SimpleGraph V) (U : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)

end ErdosGallai.Scale
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ScaleExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph Classical
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

def IsCycleGraph (K : SimpleGraph V) : Prop :=
  ∃ a : V, ∃ p : K.Walk a a, p.IsCycle ∧ K.edgeSet = p.edgeSet

def NoLongCycle (G : SimpleGraph V) (ℓ : ℝ) : Prop :=
  ∀ a : V, ∀ p : G.Walk a a, p.IsCycle → (p.length : ℝ) < ℓ

open Real Filter Asymptotics

end ErdosGallai.Scale

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ScaleHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Real Filter Finset
open scoped Topology

def scaleTheta : ℝ := 19/20
def inductionScale (n : ℝ) (j : ℕ) : ℝ := n ^ (scaleTheta ^ j)

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

structure StageSplit (P : AssignedPiece V) where
  cycles : List (SimpleGraph V)
  boxes : List (AssignedPiece V)
  pieces : AssignedPiece V → List (AssignedPiece V)
  remainder : AssignedPiece V → SimpleGraph V
  cycles_good : ∀ K ∈ cycles, IsCycleGraph K
  box_subset : ∀ B ∈ boxes, B.vertices ⊆ P.vertices
  box_nonempty : P.vertices.Nonempty → ∀ B ∈ boxes, B.vertices.Nonempty
  box_cover : ∀ v ∈ P.vertices, ∃ B ∈ boxes, v ∈ B.vertices
  piece_subset : ∀ B ∈ boxes, ∀ R ∈ pieces B, R.vertices ⊆ B.vertices
  piece_disjoint : ∀ B ∈ boxes, (pieces B).Pairwise fun R S => Disjoint R.vertices S.vertices
  remainder_supported : ∀ B ∈ boxes, SupportedOn (remainder B) B.vertices
  box_partition : ∀ B ∈ boxes, GraphPartition B.graph (remainder B :: (pieces B).map AssignedPiece.graph)
  partition : GraphPartition P.graph (cycles ++ boxes.map AssignedPiece.graph)

def StageSplit.Bounded {P : AssignedPiece V} (s : StageSplit P) (D : ℝ) : Prop :=
  (s.cycles.length:ℝ) ≤ P.vertices.card / (2*D^(1/100:ℝ)) ∧
  (s.boxes.map (fun B => (B.vertices.card:ℝ))).sum ≤ (1+2/logb 2 D)*P.vertices.card ∧
  (∀ B ∈ s.boxes, (B.vertices.card:ℝ) ≤ D^(51/50:ℝ)) ∧
  (∀ B ∈ s.boxes, ∀ R ∈ s.pieces B,
    D^(9/10:ℝ) ≤ (R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
    CutExpansionOn R.graph R.vertices (D^(9/10:ℝ))) ∧
  (∀ B ∈ s.boxes, 2*(edgeCount (s.remainder B):ℝ)/B.vertices.card ≤ D^(19/20:ℝ))

def StageSplit.trivial (P : AssignedPiece V) : StageSplit P where
  cycles := []
  boxes := [P]
  pieces := fun _ => []
  remainder := AssignedPiece.graph
  cycles_good := by simp
  box_subset := by simp
  box_nonempty := by simp
  box_cover := by intro v hv; exact ⟨P,by simp,hv⟩
  piece_subset := by simp
  piece_disjoint := by simp
  remainder_supported := fun B _ => B.supported
  box_partition := by intro B _ x y; simp
  partition := by intro x y; simp

def StageSplit.children {P : AssignedPiece V} (s : StageSplit P) : List (AssignedPiece V) :=
  s.boxes.pmap (fun B hB => ⟨B.vertices,s.remainder B,s.remainder_supported B hB⟩) (fun _ h => h)

def vertexMass (L : List (AssignedPiece V)) : ℝ :=
  (L.map (fun P => (P.vertices.card:ℝ))).sum

@[simp] lemma vertexMass_nil {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : vertexMass ([] : List (AssignedPiece V)) = 0 := rfl
@[simp] lemma vertexMass_cons {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : AssignedPiece V) (L) :
    vertexMass (P::L) = P.vertices.card + vertexMass L := rfl
@[simp] lemma vertexMass_append {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L M : List (AssignedPiece V)) :
    vertexMass (L++M) = vertexMass L + vertexMass M := by simp [vertexMass]

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev SplitSystem (V : Type) [Fintype V] [DecidableEq V] :=
  ℕ → (P : AssignedPiece V) → StageSplit P

def nextLayer (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (AssignedPiece V) :=
  L.flatMap fun P => (s j P).children

def advance (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (AssignedPiece V)
  | 0,L => L
  | k+1,L => nextLayer s (j+k) (advance s j k L)

@[simp] lemma advance_zero (s : SplitSystem V) (j) (L) : advance s j 0 L = L := rfl
@[simp] lemma advance_succ (s : SplitSystem V) (j k) (L) :
    advance s j (k+1) L = nextLayer s (j+k) (advance s j k L) := rfl

end
end ErdosGallai.Scale
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ScaleDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def graphUnion (L : List (SimpleGraph V)) : SimpleGraph V := L.foldr (· ⊔ ·) ⊥

@[simp] lemma graphUnion_nil {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : graphUnion ([] : List (SimpleGraph V)) = ⊥ := rfl
@[simp] lemma graphUnion_cons {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (L) : graphUnion (G::L) = G ⊔ graphUnion L := rfl

def levelCycles (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (SimpleGraph V) :=
  L.flatMap fun P => (s j P).cycles

def levelPieces (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (AssignedPiece V) :=
  L.flatMap fun P => (s j P).boxes.flatMap (s j P).pieces

def pastCycles (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (SimpleGraph V)
  | 0,_ => []
  | k+1,L => pastCycles s j k L ++ levelCycles s (j+k) (advance s j k L)

def pastPieces (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (AssignedPiece V)
  | 0,_ => []
  | k+1,L => pastPieces s j k L ++ levelPieces s (j+k) (advance s j k L)

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet

noncomputable section
open SimpleGraph

lemma edgeDecomposition_of_indexed {V I : Type} [Fintype I] (G : SimpleGraph V)
    (parts : I → Set (Sym2 V)) (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hu : (⋃ i, parts i) = G.edgeSet) : EdgeDecomposition G (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨fun j => parts (e.symm j), fun j => hp _, ?_, ?_⟩
  · intro i j hij
    exact hd (fun he => hij (e.symm.injective he))
  · ext x
    simp only [Set.mem_iUnion]
    rw [← hu]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i, by simpa using hi⟩

theorem edgeDecomposition_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  apply edgeDecomposition_of_indexed G (fun e : G.edgeSet => {e.1})
  · intro e; exact Or.inr ⟨e.1,e.2,rfl⟩
  · intro e d hed
    exact Set.disjoint_singleton.mpr (fun h => hed (Subtype.ext h))
  · ext e; simp

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def decompositionCost {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, EdgeDecomposition G k from ⟨_,edgeDecomposition_singleEdges G⟩)

end
end ErdosGallai.Scale

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchIndexing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Indexing
noncomputable section
open Finset

variable {I : Type cycleUniverse1} [DecidableEq I]

def batchWeight (w : I → ℕ) (b : Finset I) : ℝ := ∑ i ∈ b, (w i : ℝ)

end
end ErdosGallai.Indexing

namespace ErdosGallai.Indexing
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

structure GraphBatches {V : Type} (F : SimpleGraph V) (Y : Finset V) (B T : ℝ) where
  Index : Type
  finite : Fintype Index
  graph : Index → SimpleGraph V
  vertices : Index → Finset V
  graph_le : ∀ i, graph i ≤ F
  disjoint : Pairwise fun i j => Disjoint (graph i).edgeSet (graph j).edgeSet
  edge_cover : (⋃ i, (graph i).edgeSet) = F.edgeSet
  supported : ∀ i, ∀ ⦃x y⦄, (graph i).Adj x y → x ∈ vertices i ∧ y ∈ vertices i
  subset : ∀ i, vertices i ⊆ Y
  vertex_cover : Y ⊆ univ.biUnion vertices
  order_le : ∀ i, ((vertices i).card:ℝ) ≤ B
  mass_le : (∑ i, ((vertices i).card:ℝ)) ≤ T
  count_le : (Fintype.card Index:ℝ) ≤ 1+2*T/B
attribute [instance] GraphBatches.finite

end
end ErdosGallai.Indexing

namespace ErdosGallai.Indexing
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def goodVertices {V : Type} [Fintype V] (F : SimpleGraph V) (Y : Finset V) (a : ℝ) : Finset V :=
  Y.filter fun v => (F.degree v:ℝ) ≤ a

structure ActiveFamily {V R B : Type} [Fintype V] [Fintype R] [Fintype B]
    (F : SimpleGraph V) (Y : Finset V) (W : B → Finset V) (U : R → Finset V) (a L : ℝ) where
  Index : B → Type
  finite : ∀ b, Fintype (Index b)
  vertices : ∀ b, Index b → Finset V
  router : ∀ b, Index b → R
  subset_batch : ∀ b i, vertices b i ⊆ W b
  subset_router : ∀ b i, vertices b i ⊆ U (router b i)
  disjoint : ∀ b, Pairwise fun i j => Disjoint (vertices b i) (vertices b j)
  degree_le : ∀ b i v, v ∈ vertices b i → (F.degree v:ℝ) ≤ a
  large : ∀ b i, L ≤ ((vertices b i).card:ℝ)
  lower : (∑ r, ((U r).card:ℝ)) - ((Y \ goodVertices F Y a).card:ℝ) -
    L * Fintype.card B * Fintype.card R ≤ ∑ b, ∑ i, ((vertices b i).card:ℝ)
  upper : (∑ b, ∑ i, ((vertices b i).card:ℝ)) + Y.card ≤
    (∑ r, ((U r).card:ℝ)) + ∑ b, ((W b).card:ℝ)
attribute [instance] ActiveFamily.finite

end
end ErdosGallai.Indexing

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CostRegrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def StageSplit.rest {P : AssignedPiece V} (s : StageSplit P) (B : AssignedPiece V) : AssignedPiece V :=
  if h : B ∈ s.boxes then ⟨B.vertices,s.remainder B,s.remainder_supported B h⟩ else B

@[simp] lemma StageSplit.rest_vertices {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) (B) :
    (s.rest B).vertices = B.vertices := by unfold StageSplit.rest; split_ifs <;> rfl

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Real Filter

def mainP : ℝ := 804
def mainEta : ℝ := 1/(100*mainP)
def mainH : ℝ := 80/(Scale.scaleTheta^200)
def mainA₁ : ℝ := mainH + 4/3
def mainA₂ : ℝ := max (9*mainP+8) (9*mainH)

structure MainScaleReady (wmin D : ℝ) : Prop where
  gt_one : 1 < D
  log_large : wmin ≤ logb 2 D
  cycle_power : 1/(D^(1/100:ℝ)) ≤ 1/logb 2 D
  batch_power : D^(1/1000:ℝ) ≤ D^(3/10:ℝ)/2
  bad_power : 2*D^(-9/1000:ℝ) ≤ 1/logb 2 D
  skip_power : D^(-87/100:ℝ)+4*D^(-3/20:ℝ) ≤ 1/logb 2 D
  active_eight : 8 ≤ D^(3/100:ℝ)

end
end ErdosGallai

end

section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def costMass (L : List (AssignedPiece V)) : ℝ := (L.map (fun Q => (decompositionCost Q.graph:ℝ))).sum

end
end ErdosGallai.Scale

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.UniformLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure Layers (P : AssignedPiece V) (Dstar : ℝ) where
  system : SplitSystem V
  count : ℕ
  positive : 0 < count
  cutoff : ∀ j < count, Dstar ≤ inductionScale P.vertices.card j
  last_lt : inductionScale P.vertices.card count < Dstar
  bounded : ∀ j < count, ∀ Q ∈ advance system 0 j [P],
    (system j Q).Bounded (inductionScale P.vertices.card j)
  degree : ∀ j ≤ count, ∀ Q ∈ advance system 0 j [P],
    2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card j

variable {P : AssignedPiece V} {Dstar : ℝ}

abbrev Layers.frontier (H : Layers P Dstar) (j : ℕ) := advance H.system 0 j [P]
abbrev Layers.scale (_H : Layers P Dstar) (j : ℕ) := inductionScale (P.vertices.card:ℝ) j
abbrev Layers.mass (H : Layers P Dstar) (j : ℕ) := vertexMass (H.frontier j)
abbrev Layers.pieceMass (H : Layers P Dstar) (j : ℕ) := vertexMass (levelPieces H.system j (H.frontier j))

end
end ErdosGallai.Scale

end

end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

def Layers.pieceSequence (H : Layers P Dstar) (j : ℕ) : ℝ :=
  if j < H.count then H.pieceMass j else 0

end
end ErdosGallai.Scale

end

end
end

end OAI
end


