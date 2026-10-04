-- Prove2me | Definitions.Def_StabGen_Hypothesis_Setting
-- name    : StabGen_Hypothesis_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:29:15.591988+00:00
-- url     : https://prove2.me/theorems/ab0449c1-d6c3-4809-a158-96402d2934d6
-- title:
--   The learning setting: symmetric algorithms, $S^{\setminus i}$, $S^i$ and the leave-one-out error
-- statement:
--   This file fixes the standing setting of Bousquet and Elisseeff (§2.1, pp. 501–502).
--
--   Let $Z = X \times Y$ be the space of labelled examples. A **training set** of size $m$ is $S = \{z_1, \dots, z_m\}$, with $z_i = (x_i, y_i) \in Z$. A **learning algorithm** $A$ maps a training set $S$ to a hypothesis $A_S : X \to Y'$. The paper considers only deterministic algorithms that are **symmetric** in $S$, that is, they do not depend on the order of the examples. Accordingly $A$ is modelled as a function on finite multisets of examples, which makes symmetry automatic and lets the same $A$ act on training sets of every size.
--
--   From a sample $S = (z_1, \dots, z_m)$ two modified training sets are built for each index $i$:
--
--   1. the set with the $i$-th example removed, $S^{\setminus i} = \{z_1, \dots, z_{i-1}, z_{i+1}, \dots, z_m\}$ (size $m - 1$);
--   2. the set with the $i$-th example replaced, $S^{i} = \{z_1, \dots, z_{i-1}, z'_i, z_{i+1}, \dots, z_m\}$.
--
--   With the loss $\ell(f, z) = c(f(x), y)$ of a hypothesis $f$ at $z = (x, y)$, the **leave-one-out error** is
--
--   $$R_{\mathrm{loo}}(A, S) = \frac{1}{m} \sum_{i=1}^{m} \ell\bigl(A_{S^{\setminus i}}, z_i\bigr).$$
--
--   The generalization error $R(A,S) = \mathbb E_z[\ell(A_S, z)]$ and the empirical error $R_{\mathrm{emp}}(A,S) = \frac1m\sum_i \ell(A_S, z_i)$ are the published definitions `FoundationsML.Stability.GeneralizationError` and `FoundationsML.Stability.EmpiricalError`, applied to the hypothesis $A_S$.
--
--   **Formalization Note** A sample is a function $S : \mathrm{Fin}\ m \to X \times Y$; `trainingSet S` is the multiset of its values, `removeAt S i` the multiset with index $i$ dropped, and `replaceAt S i z'` the sample with the $i$-th entry replaced by $z'$. The algorithm type `LearningAlgorithm X Y Y'` is `Multiset (X × Y) → (X → Y')`.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 501–502, §2.1 (Notations)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss

namespace StabGen.Hypothesis

open FoundationsML.Stability

/-- A deterministic learning algorithm that is symmetric in its training set (p. 501): it sees the
training set only as a multiset, so it cannot depend on the order of the examples, and it is
defined for training sets of every size (S and S^{\i} have sizes m and m − 1). -/
abbrev LearningAlgorithm (X Y Y' : Type*) := Multiset (X × Y) → (X → Y')

/-- The training set S = {z_1, …, z_m} of a sample `S : Fin m → Z`. -/
def trainingSet {Z : Type*} {m : ℕ} (S : Fin m → Z) : Multiset Z := Finset.univ.val.map S

/-- S^{\i} = {z_1, …, z_{i−1}, z_{i+1}, …, z_m} (p. 502). -/
def removeAt {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) : Multiset Z :=
  (Finset.univ.erase i).val.map S

/-- S^i = {z_1, …, z_{i−1}, z'_i, z_{i+1}, …, z_m} (p. 502). -/
def replaceAt {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z) : Fin m → Z :=
  Function.update S i z'

/-- Leave-one-out error R_loo(A, S) = (1/m) ∑_i ℓ(A_{S^{\i}}, z_i) (p. 502). -/
noncomputable def looError {X Y Y' : Type*} {m : ℕ} (L : Y' → Y → ℝ)
    (A : LearningAlgorithm X Y Y') (S : Fin m → X × Y) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, Loss L (A (removeAt S i)) (S i)

end StabGen.Hypothesis


