-- Prove2me | Definitions.Def_LowRandomnessDP_KNorm_Privacy
-- name    : LowRandomnessDP_KNorm_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:19.324205+00:00
-- url     : https://prove2.me/theorems/36596a70-3e61-4ebf-bc9e-8ed324cc165d
-- title:
--   General-adjacency privacy and the full exponential partition law
-- statement:
--   Let $D$ be an arbitrary dataset type, $x\sim y$ its symmetric adjacency relation, and $f:D\to\mathbb R^d$ a query. Sensitivity at most one means $\|f(x)-f(y)\|_K\le1$ for every adjacent pair. Pure privacy compares the probabilities of every measurable output event by the factor $e^\varepsilon$.
--
--   For real scores $s_i$, define all exponential weights and their extended sum by
--
--   $$w_i=e^{-\varepsilon s_i/2},\qquad Z=\sum_iw_i,\qquad p_i=w_i/Z.$$
--
--   The raw atomic formula is used as a probability law only once $0<Z<\infty$ and normalization have been established. Algorithm 2 takes $s_P=\Delta_P(f(x))$ and emits the representative of the sampled cell. It includes all cells without truncation. Nonnegative cell expectations and event probabilities are extended sums.
--
--   This interface separates the output formula from its later guarantees. Theorems establish normalization for MSSPs; the main goal assumes no partition, sampler, entropy bound, or normalizer.
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, §2.2, Definitions 2.4–2.5, Theorem 2.7 (PDF 7–8 / printed 5–6), Algorithm 2 (PDF 16 / printed 14)

import Definitions.Def_LowRandomnessDP_KNorm_Geometry

open MeasureTheory

open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace LowRandomnessDP.KNorm

def SensitivityOne {D : Type} {d : ℕ} (adj : D → D → Prop)
    (K : Set (Vec d)) (f : D → Vec d) : Prop :=
  ∀ x y, adj x y → kNorm K (f x - f y) ≤ 1

/-- Pure privacy on every measurable event. Probability normalization is supplied by
PMF/trees or proved separately for the raw exponential formula. -/
def PureDP {D O : Type} [MeasurableSpace O] (adj : D → D → Prop)
    (ε : ℝ) (M : D → Measure O) : Prop :=
  ∀ x y, adj x y → ∀ E : Set O, MeasurableSet E →
    M x E ≤ ENNReal.ofReal (Real.exp ε) * M y E

/-- All outputs, with no truncation. -/
def gibbsWeight {ι : Type} (ε : ℝ) (s : ι → ℝ) (i : ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(ε / 2) * s i))

def normalizer {ι : Type} (ε : ℝ) (s : ι → ℝ) : ℝ≥0∞ :=
  ∑' i, gibbsWeight ε s i

/-- Only well-definedness, no privacy, error, entropy, or sampler assumptions. -/
def Normalizable {ι : Type} (ε : ℝ) (s : ι → ℝ) : Prop :=
  0 < normalizer ε s ∧ normalizer ε s < ⊤

/-- Raw formula: used as a law only with a proof of Normalizable / mass one. -/
def gibbsMass {ι : Type} (ε : ℝ) (s : ι → ℝ) (i : ι) : ℝ≥0∞ :=
  gibbsWeight ε s i / normalizer ε s

/-- Countable atomic output formula; includes every index, even distant cells. -/
def gibbsMeasure {ι O : Type} [MeasurableSpace O] (ε : ℝ)
    (s : ι → ℝ) (out : ι → O) : Measure O :=
  Measure.sum (fun i => gibbsMass ε s i • Measure.dirac (out i))

def eventMass {ι : Type} (p : PMF ι) (S : Set ι) : ℝ≥0∞ :=
  ∑' i : S, p i.val

/-- Algorithm 2 independently of its guarantees. -/
def expPart {d : ℕ} (K : Set (Vec d)) (P : CellPartition d)
    (ε : ℝ) (v : Vec d) : Measure (Vec d) :=
  gibbsMeasure ε (fun c => cellDistance K P c v) P.representative

/-- Nonnegative expectation, retaining infinity if the expectation diverges. -/
def cellExpectation {d : ℕ} (P : CellPartition d) (p : PMF P.Cell)
    (g : P.Cell → ℝ) : ℝ≥0∞ :=
  ∑' c, p c * ENNReal.ofReal (g c)

end LowRandomnessDP.KNorm


