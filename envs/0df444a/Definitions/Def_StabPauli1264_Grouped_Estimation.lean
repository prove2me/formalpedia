-- Prove2me | Definitions.Def_StabPauli1264_Grouped_Estimation
-- name    : StabPauli1264_Grouped_Estimation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:26:35.889355+00:00
-- url     : https://prove2.me/theorems/eba0f47f-5809-404a-be02-0e661d62966d
-- title:
--   Fresh-copy block data and the capped-weight dyadic functional
-- statement:
--   Let $C_j$ be finitely many measured contexts, with $N_j$ fresh copies allocated to context $j$. The block data consist of all their joint outcome vectors. Their probability is the product of the joint Born probabilities, preserving dependence inside each vector. For a class $J$, write $I=\bigcup_{j\in J}C_j$, $q=p(I)$ and
--
--   $$\sigma=\sqrt{\max_{j\in J}N_j^{-1}},\quad \nu_i=\widehat b_i-b_i,\quad \Phi(x)=\max\left\{\sum_{i\in I}y_i|\nu_i|:0\le y_i\le p_i,\ \sum_{i\in I}y_i=x\right\}.$$
--
--   The empirical mean uses the actual signs on copies measuring coordinate $i$. The class expectation is the finite sum of $\Phi$ weighted by the actual block-data probability. This defines the optimization in Lemma 8.2 for every feasible mass $x$, independently of the later dyadic substitution.
--
--   **Formalization Note** Optimization is represented by a real supremum; Lemma 8.2 explicitly asserts attainment on its source domain. A class is reindexed by `Fin l`. Empty classes have $q=0$, and the totalized empty inverse-maximum and supremum values are zero; the theorem assumes $q>0$ and positive copy allocations. Outside-$I$ weights do not occur in the objective or constraint.
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Lemma 8.2 Eq. (50), p. 20, and proof pp. 20–21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Peeling
set_option autoImplicit false

namespace StabPauli1264.Grouped

open scoped BigOperators Classical

/-- Nonadaptive fresh-copy block experiment; physical validity is stated by the theorem. -/
structure BlockExperiment (m l : ℕ) where
  context : Fin l → Finset (Fin m)
  copies : Fin l → ℕ

abbrev BlockData {m l : ℕ} (E : BlockExperiment m l) :=
  (j : Fin l) → Fin (E.copies j) → Outcome m

noncomputable def blockWeight {n m l : ℕ} (M : Window n m) (E : BlockExperiment m l)
    (ρ : Mat n) (h : BlockData E) : ℝ :=
  ∏ j, ∏ t, jointWeight M ρ (E.context j) (h j t)

noncomputable def classIndices {m l : ℕ} (E : BlockExperiment m l)
    (J : Finset (Fin l)) : Finset (Fin m) := J.biUnion E.context

noncomputable def blockMean {m l : ℕ} (E : BlockExperiment m l) (h : BlockData E)
    (i : Fin m) : ℝ :=
  (∑ j, if i ∈ E.context j then ∑ t, sign (h j t i) else 0) /
    (∑ j, if i ∈ E.context j then (E.copies j : ℝ) else 0)

noncomputable def classSigma {m l : ℕ} (E : BlockExperiment m l)
    (J : Finset (Fin l)) : ℝ :=
  Real.sqrt (sSup {r : ℝ | ∃ j ∈ J, r = (E.copies j : ℝ)⁻¹})

def ClassFeasible {m : ℕ} (p : EvalLaw m) (I : Finset (Fin m))
    (x : ℝ) (y : Fin m → ℝ) : Prop :=
  (∀ i ∈ I, 0 ≤ y i ∧ y i ≤ p.mass i) ∧ (∑ i ∈ I, y i = x)

noncomputable def classObjective {n m l : ℕ} (M : Window n m) (E : BlockExperiment m l)
    (ρ : Mat n) (J : Finset (Fin l)) (h : BlockData E) (y : Fin m → ℝ) : ℝ :=
  ∑ i ∈ classIndices E J, y i * |blockMean E h i - bias M ρ i|

/-- The genuine finite-dimensional capped-weight optimization, not a concentration certificate. -/
noncomputable def classPhi {n m l : ℕ} (M : Window n m) (p : EvalLaw m)
    (E : BlockExperiment m l) (ρ : Mat n) (J : Finset (Fin l)) (x : ℝ)
    (h : BlockData E) : ℝ :=
  sSup {r | ∃ y, ClassFeasible p (classIndices E J) x y ∧ r = classObjective M E ρ J h y}

noncomputable def classExpectation {n m l : ℕ} (M : Window n m) (p : EvalLaw m)
    (E : BlockExperiment m l) (ρ : Mat n) (J : Finset (Fin l)) (x : ℝ) : ℝ :=
  ∑ h : BlockData E, blockWeight M E ρ h * classPhi M p E ρ J x h

end StabPauli1264.Grouped


