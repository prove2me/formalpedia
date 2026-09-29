-- Prove2me | Definitions.Def_VapnikChervonenkis_Shared_deviation
-- name    : VapnikChervonenkis_Shared_deviation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:15:53.30526+00:00
-- url     : https://prove2.me/theorems/de08c1b5-0e60-46b3-b112-a02c69876490
-- title:
--   Relative frequency $\nu_A^{(l)}$, the uniform deviation $\pi^{(l)}$ and the semi-sample deviation $\rho^{(l)}$
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of events $A \subseteq X$ with probabilities $P_A = P(A)$.
--
--   1. For a sample $x_1, \dots, x_l$ of size $l$ and an event $A$, the **relative frequency** of $A$ is the fraction of sample terms lying in $A$:
--   $$
--   \nu_A^{(l)}(x_1, \dots, x_l) = \frac{n_A}{l}, \qquad n_A = \#\{\, i : x_i \in A \,\}.
--   $$
--   2. The **uniform deviation** of relative frequencies from probabilities over the class $S$ is
--   $$
--   \pi^{(l)}(x_1, \dots, x_l) = \sup_{A \in S} \bigl|\nu_A^{(l)} - P_A\bigr|.
--   $$
--   3. For a double sample $x_1, \dots, x_l, x_{l+1}, \dots, x_{2l}$, let $\nu'_A$ and $\nu''_A$ be the relative frequencies of $A$ in the first semi-sample $x_1, \dots, x_l$ and in the second semi-sample $x_{l+1}, \dots, x_{2l}$. The **semi-sample deviation** is
--   $$
--   \rho^{(l)}(x_1, \dots, x_{2l}) = \sup_{A \in S} \bigl|\nu'_A - \nu''_A\bigr|.
--   $$
--
--   The event $\{\pi^{(l)} > \varepsilon\}$ is the failure of uniform convergence that the paper estimates; $\rho^{(l)}$ depends on the sample only, not on $P$, and is the quantity through which that estimate is obtained.
--
--   **Shared definition.** This one definition serves two missions of the paper: *02-vc-inequality* (Lemma 2, p. 268; equation (11), p. 270; the permutation and semi-sample bounds, p. 271; Theorem 2 and its corollary, p. 269; Theorem 3, p. 271) and *03-entropy-criterion* (Lemma 2, p. 268; the permutation bound, p. 271; the sufficiency estimate, p. 276; the necessity steps, pp. 276–277 and p. 280; Theorem 4, p. 275).
--
--   **Formalization Note** Samples are functions `Fin l → X` and double samples functions `Fin (l + l) → X`; the first semi-sample is read through `Fin.castAdd l` and the second through `Fin.natAdd l`. $P_A$ is `P.real A`. Both suprema are real suprema over the subtype of events in $S$; the values lie in $[0, 1]$, and for $S = \emptyset$ the supremum is $0$. For $l = 0$ the relative frequency is $0/0 = 0$ in Lean; every theorem of the mission uses $l \ge 1$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 264 (relative frequency), p. 265 (π^(l)), p. 268 Subsection 3 (ρ^(l))

import Mathlib

namespace VapnikChervonenkis.Shared

open MeasureTheory

open Classical in
/-- The relative frequency `ν_A^(l)(x_1, …, x_l) = n_A / l` of the event `A` in the sample
`x : Fin l → X` (Introduction, p. 264): the number of sample terms lying in `A`, divided by
the sample size. -/
noncomputable def relFreq {X : Type*} (A : Set X) {l : ℕ} (x : Fin l → X) : ℝ :=
  ((Finset.univ.filter (fun i => x i ∈ A)).card : ℝ) / l

/-- The maximal deviation `π^(l) = sup_{A ∈ S} |ν_A^(l) − P_A|` between relative frequency and
probability over the class `S` (p. 265), as a function of the sample `x : Fin l → X`. The
supremum runs over the events of `S`; for `S = ∅` it is `0`. -/
noncomputable def maxDeviation {X : Type*} [MeasurableSpace X] (S : Set (Set X))
    (P : Measure X) (l : ℕ) (x : Fin l → X) : ℝ :=
  ⨆ A : S, |relFreq (A : Set X) x - P.real (A : Set X)|

/-- The maximal difference of relative frequencies between the two semi-samples,
`ρ^(l) = sup_{A ∈ S} |ν′_A − ν″_A|` (§1.3, p. 268), as a function of the double sample
`x : Fin (l + l) → X`: the first semi-sample is `x_1, …, x_l` (indices `Fin.castAdd`), the
second `x_{l+1}, …, x_{2l}` (indices `Fin.natAdd`). For `S = ∅` it is `0`. -/
noncomputable def semiSampleDeviation {X : Type*} (S : Set (Set X)) (l : ℕ)
    (x : Fin (l + l) → X) : ℝ :=
  ⨆ A : S, |relFreq (A : Set X) (fun i : Fin l => x (Fin.castAdd l i))
    - relFreq (A : Set X) (fun i : Fin l => x (Fin.natAdd l i))|

end VapnikChervonenkis.Shared


