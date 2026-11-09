-- Prove2me | Definitions.Def_PrattColoring_Barrier_Setting
-- name    : PrattColoring_Barrier_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:18.5172+00:00
-- url     : https://prove2.me/theorems/42361d70-6c4c-4554-bc54-89e252e727ef
-- title:
--   Graphs, exact profiles, palettes, and neighborhood promises
-- statement:
--   Let $G$ be a finite simple graph with vertices $\mathrm{Fin}(n)$ and let the colors be $\mathrm{Fin}(k)$. A **count profile** is a vector of natural numbers $(n_i)$ with $\sum_i n_i=n$. A proper coloring has this profile exactly when its color classes have those cardinalities. Colors may be unused. List colorability also requires each vertex's color to belong to its given list. A constrained profile coloring requires all vertices of $A$ to receive colors in $R$.
--
--   For $n>0$ put $p_i=n_i/n$ and $p(R)=\sum_{i\in R}p_i$. A palette is $\eta$-good when
--   $$p(R)\le\frac12-\eta.$$
--   At $n=0$ weights are defined as zero and the exact profile is still the unique zero count vector. Realizability concerns a partition of the specified vertex set itself. An $(\alpha,\Delta)$-bounded graph has at least $\alpha n$ vertices of degree at most $\Delta$. A mostly-light witness has at least $15n/16$ vertices of degree at least $d$, each with at most $c$ neighbors outside some good palette; the palette may depend on the vertex. Binary entropy is Mathlib's natural-log entropy divided by $\log 2$, used on $(0,1)$.
--
--   These are the shared mathematical objects for the six supporting results and the headline.
-- source:
--   Kevin Pratt, STOC 2027 submission #690 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/690.pdf, Problem 1.1; §2; §4, Definition 4.3; Lemma 5.2, pp. 1, 3, 5–6 (PDF pp. 1, 3, 5–6); SHA256 ad5f710e4e7049a1d0cc1cd1397305575274d94aac977c67c5de74f037a0309d.

import Mathlib

namespace PrattColoring.Barrier

open Finset

/-- Exact color-class sizes (§2, p.3), including the unique zero vector at n=0. -/
structure CountProfile (n k : ℕ) where
  count : Fin k → ℕ
  total : ∑ i, count i = n

/-- The normalized profile is used only for palette tests, not as a real input oracle.
At n=0 every mass is defined as zero; exact coloring still uses counts. -/
noncomputable def CountProfile.weight {n k : ℕ} (p : CountProfile n k) (i : Fin k) : ℝ :=
  (p.count i : ℝ) / n

def paletteMass {k : ℕ} (p : Fin k → ℝ) (R : Finset (Fin k)) : ℝ := ∑ i ∈ R, p i

def GoodPalette {n k : ℕ} (p : CountProfile n k) (η : ℝ) (R : Finset (Fin k)) : Prop :=
  paletteMass p.weight R ≤ 1 / 2 - η

noncomputable def HasProfile {n k : ℕ} {G : SimpleGraph (Fin n)}
    (f : G.Coloring (Fin k)) (p : CountProfile n k) : Prop :=
  ∀ i, (univ.filter fun v => f v = i).card = p.count i

def ProfileColorable {n k : ℕ} (G : SimpleGraph (Fin n)) (p : CountProfile n k) : Prop :=
  ∃ f : G.Coloring (Fin k), HasProfile f p

def ListColorable {n k : ℕ} (G : SimpleGraph (Fin n)) (L : Fin n → Finset (Fin k)) : Prop :=
  ∃ f : G.Coloring (Fin k), ∀ v, f v ∈ L v

def ConstrainedColorable {n k : ℕ} (G : SimpleGraph (Fin n)) (p : CountProfile n k)
    (A : Finset (Fin n)) (R : Finset (Fin k)) : Prop :=
  ∃ f : G.Coloring (Fin k), HasProfile f p ∧ ∀ v ∈ A, f v ∈ R

/-- Realizability is a partition on A itself, not a coloring of the entire graph. -/
def Realizable {n k : ℕ} (G : SimpleGraph (Fin n)) (p : CountProfile n k)
    (A : Finset (Fin n)) (R : Finset (Fin k)) : Prop :=
  ∃ f : A → Fin k,
    (∀ v, f v ∈ R) ∧
    (∀ v w, G.Adj v.val w.val → f v ≠ f w) ∧
    ∀ i ∈ R, Fintype.card {v : A // f v = i} = p.count i

noncomputable def neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  by classical exact univ.filter (G.Adj v)

noncomputable def degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (neighbors G v).card

/-- The source's fraction convention includes α=0; the theorem binds 0≤α≤1. -/
noncomputable def BoundedGraph {n : ℕ} (G : SimpleGraph (Fin n)) (α : ℝ) (Δ : ℕ) : Prop :=
  by classical exact α * n ≤ ((univ.filter fun v => degree G v ≤ Δ).card : ℝ)

/-- The palette may depend on v; c exceptional neighbors are counted exactly. -/
noncomputable def LightVertex {n k : ℕ} {G : SimpleGraph (Fin n)}
    (p : CountProfile n k) (f : G.Coloring (Fin k)) (c d : ℕ) (η : ℝ) (v : Fin n) : Prop :=
  ∃ R : Finset (Fin k), GoodPalette p η R ∧ d ≤ degree G v ∧
    ((neighbors G v).filter fun u => f u ∉ R).card ≤ c

noncomputable def MostlyLightWitness {n k : ℕ} (G : SimpleGraph (Fin n))
    (p : CountProfile n k) (c d : ℕ) (η : ℝ) : Prop := by
  classical
  exact ∃ f : G.Coloring (Fin k), HasProfile f p ∧
    15 * n ≤ 16 * (univ.filter (LightVertex p f c d η)).card

/-- Only the implication is promised; no-instance soundness is unconditional. -/
def LightPromise {n k : ℕ} (G : SimpleGraph (Fin n)) (p : CountProfile n k)
    (c d : ℕ) (η : ℝ) : Prop :=
  ProfileColorable G p → MostlyLightWitness G p c d η

/-- Natural-log Mathlib entropy converted to base two. Uses are restricted to (0,1). -/
noncomputable def entropy2 (x : ℝ) : ℝ := Real.binEntropy x / Real.log 2

end PrattColoring.Barrier


