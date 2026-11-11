-- Prove2me | Definitions.Def_GaussLocalMaxColoring_Main_Iterative
-- name    : GaussLocalMaxColoring_Main_Iterative
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:21:05.596233+00:00
-- url     : https://prove2.me/theorems/7fd206ea-77bb-4e9a-bf88-919d97d59bae
-- title:
--   Algorithm 1 (GaussianLocalMaxima) and one trial of Algorithm 2 (IterativeGaussianLocalMaxima)
-- statement:
--   **Algorithm 1** on a vertex set $F$ draws $g\sim N(0,I_d)$ and returns $I_F(g)$. **Algorithm 2** (one trial) takes $G$, unit vectors $\{v_x\}$, $\delta\in(0,1)$, $T,R\in\mathbb N$, sets $F_0=V$ and, for levels $j=1,\dots,\ell$: runs Algorithm 1 $R$ times on $F_{j-1}$, returning SUCCESS$(I^{(i)})$ as soon as $|I^{(i)}|\ge T$; otherwise sets $\hat p_j(x)=R^{-1}\sum_{i}\mathbf 1[x\in I^{(i)}]$ and $F_j=\{x\in F_{j-1}:\hat p_j(x)<\delta/2\}$. After level $\ell$ it returns FAIL.
--
--   The trial is a function of its $\ell R$ i.i.d. standard Gaussian samples ($\omega(j,i)$ is the $i$-th sample at level $j+1$). `cores` computes $F_0\supseteq F_1\supseteq\cdots$ for every level as if no level had succeeded; $F_j$ is **constructed** when no set sampled at levels $1,\dots,j$ has size $\ge T$, and then it is the trial's core. `alg2` returns SUCCESS of the first sampled set (levels in order, samples in order) of size $\ge T$, or FAIL (`none`). `largest` picks a set of maximum size from a list; `trialLaw` is the product Gaussian law of the samples.
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Algorithms 1 and 2, §4.1, printed pp. 15–16 (PDF 17–18)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Basic

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical
noncomputable section

namespace GaussLocalMaxColoring.Main

/-! # Algorithm 1 (GaussianLocalMaxima) and Algorithm 2 (IterativeGaussianLocalMaxima)

Deguchi–Kawarabayashi–Yoneda–Yoneda, arXiv:2610.35859, §4.1, pp. 15–16 (PDF 17–18).

Algorithm 1 on a vertex set `F` with a Gaussian sample `g` returns `I_F(g)` (`localMax`).
One trial of Algorithm 2 is modelled as a function of its `ℓ·R` Gaussian samples
`ω : Fin ℓ × Fin R → Space d`, `ℓ = ⌈log n⌉`: the sample `ω (j, i)` (0-based level `j`) is the
`i`-th call of Algorithm 1 at level `j + 1`. Level `j + 1` runs Algorithm 1 `R` times on the core
`F_j`, computes `p̂_{j+1}(x) = R⁻¹ Σ_i 1[x ∈ I^{(i)}]`, and sets
`F_{j+1} = {x ∈ F_j : p̂_{j+1}(x) < δ/2}`; `F_0 = V`.

**Formalization Note.** `cores` computes the core sequence for every level as if no level had
returned `SUCCESS`; the trial itself (`alg2`) stops at the first sampled set of size `≥ T`
(levels in order, samples in order within a level). The core `F_j` is *constructed* by the trial
exactly when no sample at levels `1, …, j` reached size `T` (`Constructed`), and then it equals
`cores … j`. Beyond level `ℓ` the sequence is constant. -/

variable {n d : ℕ}

/-- The `i`-th independent set `I^{(i)}` sampled at (0-based) level `j` on the core `F`: Algorithm 1
run on `F` with the sample `ω (j, i)`; `∅` for `j ≥ ℓ` (no such level). -/
def sampledAt (G : SimpleGraph (Fin n)) (v : Fin n → Space d) {R : ℕ}
    (ω : Fin (numLevels n) × Fin R → Space d) (F : Finset (Fin n)) (j : ℕ) (i : Fin R) :
    Finset (Fin n) :=
  if h : j < numLevels n then localMax G v F (ω (⟨j, h⟩, i)) else ∅

/-- Empirical frequency `R⁻¹ Σ_{i} 1[x ∈ I^{(i)}]` of `x` among `R` sampled sets. -/
def freq {R : ℕ} (I : Fin R → Finset (Fin n)) (x : Fin n) : ℝ :=
  ((Finset.univ.filter fun i => x ∈ I i).card : ℝ) / R

/-- The cores `F_0 = V ⊇ F_1 ⊇ ⋯` of one trial of Algorithm 2 (line 9). -/
def cores (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ) {R : ℕ}
    (ω : Fin (numLevels n) × Fin R → Space d) : ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | j + 1 => (cores G v δ ω j).filter fun x =>
      freq (sampledAt G v ω (cores G v δ ω j) j) x < δ / 2

/-- `I^{(i)}` at level `j` (1-based, `1 ≤ j ≤ ℓ`): Algorithm 1 on `F_{j−1}`. -/
def sampleSet (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ) {R : ℕ}
    (ω : Fin (numLevels n) × Fin R → Space d) (j : ℕ) (i : Fin R) : Finset (Fin n) :=
  sampledAt G v ω (cores G v δ ω (j - 1)) (j - 1) i

/-- `p̂_j(x)` at level `j` (1-based), line 8. -/
def phat (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ) {R : ℕ}
    (ω : Fin (numLevels n) × Fin R → Space d) (j : ℕ) (x : Fin n) : ℝ :=
  freq (sampleSet G v δ ω j) x

/-- The core `F_j` is constructed by the trial: no set sampled at levels `1, …, j` has size `≥ T`. -/
def Constructed (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ) (T : ℕ) {R : ℕ}
    (ω : Fin (numLevels n) × Fin R → Space d) (j : ℕ) : Prop :=
  ∀ j', 1 ≤ j' → j' ≤ j → ∀ i, (sampleSet G v δ ω j' i).card < T

/-- One trial of Algorithm 2: `some I` = `SUCCESS(I)` for the first sampled set (levels in order,
samples in order) with `|I| ≥ T`; `none` = `FAIL`. -/
def alg2 (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ) (T : ℕ) {R : ℕ}
    (ω : Fin (numLevels n) × Fin R → Space d) : Option (Finset (Fin n)) :=
  ((List.range (numLevels n)).flatMap fun j =>
      (List.finRange R).map fun i => sampleSet G v δ ω (j + 1) i).find? fun I => T ≤ I.card

/-- Every set sampled by one trial (all levels), the sets "obtained" by the trial. -/
def alg2Sampled (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ) {R : ℕ}
    (ω : Fin (numLevels n) × Fin R → Space d) : List (Finset (Fin n)) :=
  (List.range (numLevels n)).flatMap fun j =>
    (List.finRange R).map fun i => sampleSet G v δ ω (j + 1) i

/-- A largest set of a list (the first one of maximum cardinality; `∅` for the empty list). -/
def largest (l : List (Finset (Fin n))) : Finset (Fin n) :=
  l.foldl (fun acc I => if acc.card < I.card then I else acc) ∅

/-- The sample space of one trial and its law: `ℓ·R` i.i.d. standard Gaussian vectors. -/
def trialLaw (n d R : ℕ) : Measure (Fin (numLevels n) × Fin R → Space d) :=
  Measure.pi fun _ => stdGaussian (Space d)

end GaussLocalMaxColoring.Main


