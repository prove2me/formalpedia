-- Prove2me | Definitions.Def_RandomIsetThreshold_Degree_ResamplingPath
-- name    : RandomIsetThreshold_Degree_ResamplingPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:13:59.3873+00:00
-- url     : https://prove2.me/theorems/94583c7b-770a-44eb-9bba-213dec962462
-- title:
--   Stationary resampling paths and the five Section 4 events
-- statement:
--   Draw independent fresh Bernoulli-$p$ hypergraphs and Bernoulli-$\tau$ masks at every time. Starting with $G_0\sim H_{n,p}$, set $G_{i+1}=G_i^\tau$. A single independent seed $R$ is shared across all times. For $0<\varepsilon\le1$ and $0<\kappa<1/e$, the Section 4 parameters are
--
--   $$\gamma=\varepsilon/49,\quad\tau=\frac{\log(1/\kappa)}{pL^r},\quad a=\frac12-\sqrt{12\gamma/\varepsilon},\quad m=\lceil\log(e/(1-p))/\tau\rceil,\quad K=\lceil192/\varepsilon^2\rceil,\quad T=mK.$$
--
--   Let $I_i$ be the lexicographically first independent set of size at least $(1+\varepsilon)L$ that is $\gamma$-close to $f(G_i,R)$, or empty on failure. The success event $E$ requires this success for every $0\le i\le T$. The maximum event $M$ requires every independent set in every $G_i$ to have size strictly below $3L$. Stability $S$ requires $\|f(G_i,R)-f(G_{i+1},R)\|_2\le a\sqrt{\varepsilon L}$ for $i<T$; $S_{0,1}$ denotes the first such condition.
--
--   Chaos $C$ requires $|I_{t_i+m}\setminus\bigcup_{j\le i}I_{t_j}|>\varepsilon L/2$ for each $i<K$ and strictly increasing $t_0,\dots,t_i\le T-m$. The event $O$ excludes every sequence $S_0,\dots,S_K$ with $|S_i|\ge(1+\varepsilon)L$, each independent at strictly increasing times at most $T$, and $|S_i\setminus\bigcup_{j<i}S_j|\in[\varepsilon L/4,\varepsilon L/2]$ for $1\le i\le K$.
--
--   The event probabilities are taken under the actual resampling-path law times $\mu$, without assuming any event estimate. **Formalization Note** A clipped rate makes the law total off its domain; every Section 4 theorem uses the source regime, which ensures $0<\tau\le1/2$ and makes clipping the identity. Infinite sequences only supply the finite prefixes used in each result.
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 13–14, §4, equations (32)–(33), §4.1

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_SelectorFourier

namespace RandomIsetThreshold.Degree

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

variable {n r : ℕ}
abbrev PathSample (n r : ℕ) := (ℕ → Cube n r) × (ℕ → Cube n r)

/-- Independent fresh graphs and masks at every time. The zeroth mask is unused. -/
def pathLaw (n r : ℕ) (p τ : unitInterval) : Measure (PathSample n r) :=
  (Measure.infinitePi (fun _ : ℕ => graphLaw n r p)).prod
    (Measure.infinitePi (fun _ : ℕ => graphLaw n r τ))

instance pathLaw_probability (n r : ℕ) (p τ : unitInterval) :
    IsProbabilityMeasure (pathLaw n r p τ) := by
  unfold pathLaw
  infer_instance

def pathGraph (z : PathSample n r) : ℕ → Cube n r
  | 0 => z.1 0
  | i + 1 => resample (pathGraph z i) (z.1 (i + 1)) (z.2 (i + 1))

/-- Section 4 parameters are computed from the input, never from event probabilities. -/
def tolerance (ε : ℝ) : ℝ := ε / 49
def noiseRate (n r : ℕ) (p : unitInterval) (κ : ℝ) : ℝ :=
  Real.log (1 / κ) / ((p : ℝ) * scale n r p ^ r)
def stabilityCoefficient (ε : ℝ) : ℝ := 1 / 2 - Real.sqrt (12 * tolerance ε / ε)
def blockLength (n r : ℕ) (p : unitInterval) (κ : ℝ) : ℕ :=
  ⌈Real.log (Real.exp 1 / (1 - (p : ℝ))) / noiseRate n r p κ⌉₊
def blockCount (ε : ℝ) : ℕ := ⌈192 / ε ^ 2⌉₊
def horizon (n r : ℕ) (p : unitInterval) (ε κ : ℝ) : ℕ :=
  blockLength n r p κ * blockCount ε

/-- Clipping is irrelevant under 0 < rate ≤ 1/2; it gives a total definition elsewhere. -/
def rateParameter (n r : ℕ) (p : unitInterval) (κ : ℝ) : unitInterval :=
  ⟨max 0 (min 1 (noiseRate n r p κ)), by constructor <;> simp⟩

def ensembleLaw (n r : ℕ) (p : unitInterval) (κ : ℝ) : Measure (PathSample n r) :=
  pathLaw n r p (rateParameter n r p κ)

variable {Ω : Type*} [MeasurableSpace Ω]

def foundSet (p : unitInterval) (ε : ℝ) (f : Cube n r → Ω → Vector n)
    (G : Cube n r) (s : Ω) : Finset (Fin n) :=
  lexFirst (fun I => Independent G I ∧ (1 + ε) * scale n r p ≤ (I.card : ℝ) ∧
    Close (tolerance ε) (f G s) I)

def eventE (p : unitInterval) (ε κ : ℝ) (f : Cube n r → Ω → Vector n) :
    Set (PathSample n r × Ω) :=
  {z | ∀ i ≤ horizon n r p ε κ,
    Success ε (tolerance ε) p (pathGraph z.1 i) (f (pathGraph z.1 i) z.2)}

def eventM (p : unitInterval) (ε κ : ℝ) : Set (PathSample n r × Ω) :=
  {z | ∀ i ≤ horizon n r p ε κ, ∀ I : Finset (Fin n),
    Independent (pathGraph z.1 i) I → (I.card : ℝ) < 3 * scale n r p}

def eventS01 (p : unitInterval) (ε : ℝ) (f : Cube n r → Ω → Vector n) :
    Set (PathSample n r × Ω) :=
  {z | Real.sqrt (sqDist (f (pathGraph z.1 0) z.2) (f (pathGraph z.1 1) z.2)) ≤
    stabilityCoefficient ε * Real.sqrt (ε * scale n r p)}

def eventS (p : unitInterval) (ε κ : ℝ) (f : Cube n r → Ω → Vector n) :
    Set (PathSample n r × Ω) :=
  {z | ∀ i < horizon n r p ε κ,
    Real.sqrt (sqDist (f (pathGraph z.1 i) z.2) (f (pathGraph z.1 (i + 1)) z.2)) ≤
      stabilityCoefficient ε * Real.sqrt (ε * scale n r p)}

def eventC (p : unitInterval) (ε κ : ℝ) (f : Cube n r → Ω → Vector n) :
    Set (PathSample n r × Ω) := by
  classical
  exact {z | ∀ i < blockCount ε, ∀ t : Fin (i + 1) → ℕ, StrictMono t →
    (∀ j, t j ≤ horizon n r p ε κ - blockLength n r p κ) →
    (ε * scale n r p / 2 <
      ((foundSet p ε f (pathGraph z.1 (t (Fin.last i) + blockLength n r p κ)) z.2 \
        (Finset.univ.biUnion (fun j => foundSet p ε f (pathGraph z.1 (t j)) z.2))).card : ℝ))}

def eventO (p : unitInterval) (ε κ : ℝ) : Set (PathSample n r × Ω) := by
  classical
  exact {z | ¬ ∃ (S : Fin (blockCount ε + 1) → Finset (Fin n))
    (t : Fin (blockCount ε + 1) → ℕ), StrictMono t ∧
    (∀ i, t i ≤ horizon n r p ε κ) ∧
    (∀ i, Independent (pathGraph z.1 (t i)) (S i) ∧
      (1 + ε) * scale n r p ≤ ((S i).card : ℝ)) ∧
    (∀ i : Fin (blockCount ε + 1), 0 < i.val →
      let fresh := ((S i \ ((Finset.univ.filter (fun j => j < i)).biUnion S)).card : ℝ)
      ε * scale n r p / 4 ≤ fresh ∧ fresh ≤ ε * scale n r p / 2)}

def sectionProbability (p : unitInterval) (κ : ℝ) (μ : Measure Ω)
    (A : Set (PathSample n r × Ω)) : ℝ := ((ensembleLaw n r p κ).prod μ).real A

end
end RandomIsetThreshold.Degree


