-- Prove2me | Definitions.Def_RiddledBasins_Churn
-- name    : RiddledBasins_Churn
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T20:33:21.380011+00:00
-- url     : https://prove2.me/theorems/58923476-379d-449a-a0e7-78a3f3541f15
-- title:
--   Churn $m_\varepsilon(O,O')$ and predicted class
-- statement:
--   This file defines the functional-side diagnostic of the paper: **churn**, the fraction of inputs on which two trained networks disagree.
--
--   Let $O,O'\in\mathbb R^{N\times C}$ be the output (logit) matrices of two networks on the same $N$ inputs, with $C$ classes. Writing $\hat y_i=\arg\max_j O_{i,j}$ and $\hat y'_i=\arg\max_j O'_{i,j}$ for the predicted classes, the churn is
--   $$m(O,O')=\frac{1}{N}\,\#\{i:\hat y_i\neq\hat y'_i\}.$$
--   Averaged over pairs of networks trained from $\varepsilon$-close initializations, this is the similarity measure $m_\varepsilon$ whose power-law exponent is the paper's functional uncertainty exponent $\phi_f$.
--
--   Churn measures disagreement of the learned input–output map rather than of the weights, which is what matters in deployment: two parameter vectors related by a network symmetry give the same function and hence zero churn, even though they are different points of parameter space.
--
--   **Formalization Note.** The arg-max is chosen classically by `Exists.choose` from `Finset.exists_max_image`, so ties are resolved by an unspecified but fixed choice; the accompanying lemma `predictedLabel_spec` records that the chosen index attains the maximum. Inputs and classes are arbitrary nonempty finite types, which avoids a degenerate division by zero in the average.
-- source:
--   A. Ly & P. Gong, Fractal basin geometry and the limits to predictability and reproducibility in deep learning, Nature Machine Intelligence (2026), https://doi.org/10.1038/s42256-026-01336-3, PDF p. 5, 'Function-space irreproducibility', eq. (6)

import Mathlib

namespace RiddledBasins

/-- The predicted class of a logit vector: an index attaining the maximum logit. -/
noncomputable def predictedLabel {κ : Type*} [Fintype κ] [Nonempty κ] (o : κ → ℝ) : κ :=
  (Finset.exists_max_image Finset.univ o Finset.univ_nonempty).choose

lemma predictedLabel_spec {κ : Type*} [Fintype κ] [Nonempty κ] (o : κ → ℝ) (k : κ) :
    o k ≤ o (predictedLabel o) := by
  have h := (Finset.exists_max_image Finset.univ o Finset.univ_nonempty).choose_spec
  exact h.2 k (Finset.mem_univ k)

/-- Churn: the fraction of inputs on which two networks' predicted classes differ. -/
noncomputable def churn {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    [DecidableEq κ] (O O' : ι → κ → ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => predictedLabel (O i) ≠ predictedLabel (O' i))).card : ℝ)
    / (Fintype.card ι : ℝ)

end RiddledBasins


