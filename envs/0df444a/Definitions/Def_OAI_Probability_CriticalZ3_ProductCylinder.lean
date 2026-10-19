-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
-- name    : OAI_Probability_CriticalZ3_ProductCylinder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:50:17.522985+00:00
-- url     : https://prove2.me/theorems/5902ac8b-baf1-4722-97d5-16ca90f5c525
-- title:
--   Product Bernoulli laws on bit configurations
-- statement:
--   Product measures of independent bits with site-dependent parameters $p:E\to[0,1]$.
--
--   1. **Infinite product law.** For a countable index set $E$, the law of $\omega:E\to\{0,1\}$ makes the bits independent with
--   $$
--   \mathbb P(\omega_e=1)=p_e .
--   $$
--   For a finite set $J\subseteq E$, the finite law is the product law on $J\to\{0,1\}$, and a finite configuration extends by $0$ outside $J$.
--   2. **Cylinder functions.** A function $f$ of configurations is determined by $J$ if it depends only on the bits in $J$; such observables reduce exactly to the finite law.
--   3. **Finite index sets.** For finite $E$ the same product law, its means $\mathbb E[f]$ and probabilities of events are also defined directly, and a configuration extends to $\mathrm{Option}\,E$ by a fixed extra bit; these are used for Harris association.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ProductCylinder.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ProductCylinder.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

noncomputable def law (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.infinitePi (fun e => bernoulliMeasure true false (p e))

instance law_probability (p : E → Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (law p) := by
  unfold law; infer_instance

noncomputable def finiteLaw (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) : Measure (J → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance finiteLaw_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (finiteLaw J p) := by unfold finiteLaw; infer_instance

noncomputable def extend (J : Finset E) (ξ : J → Bool) : E → Bool :=
  fun e => if h : e ∈ J then ξ ⟨e,h⟩ else false

def DeterminedBy (J : Finset E) (f : (E → Bool) → F) : Prop :=
  ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

noncomputable def law [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance law_probability [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (law p) := by unfold law; infer_instance

noncomputable def mean [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) (f : (E → Bool) → ℝ) : ℝ :=
  ∫ ω, f ω ∂law p

def extend (ω : E → Bool) (b : Bool) : Option E → Bool
  | none => b
  | some e => ω e

noncomputable def prob [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : ℝ := mean p (fun ω => if P ω then 1 else 0)

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

end ProductCylinder

end OAI


