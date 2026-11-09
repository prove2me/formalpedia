-- Prove2me | Definitions.Def_RandomIsetThreshold_Degree_Hypergraph
-- name    : RandomIsetThreshold_Degree_Hypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:00:23.160823+00:00
-- url     : https://prove2.me/theorems/ccd74809-87da-4f22-91d8-a598c24524b9
-- title:
--   Binomial uniform hypergraphs, independent sets, and scale
-- statement:
--   Let $V=[n]$ and $\mathcal E=\binom{V}{r}$. A configuration $G\in\{0,1\}^{\mathcal E}$ is an $r$-uniform hypergraph. The law $H_{n,p}$ independently includes every potential edge with probability $p$. A set $I\subseteq V$ is independent when it contains no present edge, and $\alpha(G)$ is the maximum cardinality of any independent set. Write $1_I$ for its indicator vector. For $x,y\in\mathbb R^n$, squared norm and squared distance are the coordinate sums of squares. Define
--
--   $$L=\left((r-2)!\frac{\log(n^{r-1}p)}{-\log(1-p)}\right)^{1/(r-1)},\qquad x\text{ is }\gamma\text{-close to }I\iff\sum_v(x_v-1_I(v))^2\le\gamma|I|.$$
--
--   The regime predicate is $d/n^{r-1}\le p\le1-n^{-\xi}$. Success means that an independent $I$ exists with $|I|\ge(1+\varepsilon)L$ and the displayed closeness property; the exact-size version instead requires $|I|=k$.
--
--   These definitions fix the objects shared by both threshold branches. **Formalization Note** The law uses Mathlib's genuine Bernoulli product measure. Vertices are `Fin n`; the actual maximum is a finite maximum, with $\alpha=0$ when $n=0$. Real powers are total outside the stated theorem regimes, where their arguments need not have the intended interpretation.
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 2–4, §1.1, equations (1)–(3)

import Mathlib

namespace RandomIsetThreshold.Degree

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

/-- All unordered potential r-edges, with no repetitions or loops. -/
abbrev Edge (n r : ℕ) := {e : Finset (Fin n) // e.card = r}
abbrev Cube (n r : ℕ) := Edge n r → Bool
abbrev Vector (n : ℕ) := Fin n → ℝ

/-- Mathlib's Bernoulli product law, with true having probability p. -/
def graphLaw (n r : ℕ) (p : unitInterval) : Measure (Cube n r) :=
  Measure.pi (fun _ => ProbabilityTheory.bernoulliMeasure true false p)

instance graphLaw_probability (n r : ℕ) (p : unitInterval) :
    IsProbabilityMeasure (graphLaw n r p) := by
  unfold graphLaw
  infer_instance

def Independent {n r : ℕ} (G : Cube n r) (I : Finset (Fin n)) : Prop :=
  ∀ e : Edge n r, G e = true → ¬ e.val ⊆ I

def independenceNumber {n r : ℕ} (G : Cube n r) : ℕ := by
  classical
  exact ((Finset.univ.filter (Independent G)).image Finset.card).max.getD 0

def indicator {n : ℕ} (I : Finset (Fin n)) : Vector n :=
  fun v => if v ∈ I then 1 else 0

def sqNorm {n : ℕ} (x : Vector n) : ℝ := ∑ v, (x v) ^ 2

def sqDist {n : ℕ} (x y : Vector n) : ℝ := ∑ v, (x v - y v) ^ 2

def Close {n : ℕ} (γ : ℝ) (x : Vector n) (I : Finset (Fin n)) : Prop :=
  sqDist x (indicator I) ≤ γ * I.card

/-- Equation (1), with real division in the root exponent. -/
def scale (n r : ℕ) (p : unitInterval) : ℝ :=
  Real.rpow ((Nat.factorial (r - 2) : ℝ) *
    Real.log ((n : ℝ) ^ (r - 1) * (p : ℝ)) / (-Real.log (1 - (p : ℝ))))
    (1 / ((r : ℝ) - 1))

def rootFactor (r : ℕ) : ℝ := Real.rpow (r : ℝ) (1 / ((r : ℝ) - 1))

def Regime (n r : ℕ) (p : unitInterval) (d ξ : ℝ) : Prop :=
  d / (n : ℝ) ^ (r - 1) ≤ (p : ℝ) ∧
    (p : ℝ) ≤ 1 - Real.rpow (n : ℝ) (-ξ)

def Success {n r : ℕ} (ε γ : ℝ) (p : unitInterval)
    (G : Cube n r) (x : Vector n) : Prop :=
  ∃ I : Finset (Fin n), Independent G I ∧
    (1 + ε) * scale n r p ≤ (I.card : ℝ) ∧ Close γ x I

def ExactSize {n r : ℕ} (k : ℕ) (γ : ℝ) (G : Cube n r) (x : Vector n) : Prop :=
  ∃ I : Finset (Fin n), Independent G I ∧ I.card = k ∧ Close γ x I

end
end RandomIsetThreshold.Degree


