-- Prove2me | Definitions.Def_StabGen_Uniform_Stability
-- name    : StabGen_Uniform_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:47:13.688001+00:00
-- url     : https://prove2.me/theorems/cea95c2f-5be3-4f61-a4d5-1c9e3ea0632a
-- title:
--   Uniform stability $\beta$ (Definition 6)
-- statement:
--   Let $A$ be a symmetric learning algorithm and $\ell(f, (x,y)) = c(f(x), y)$ a loss. The algorithm $A$ has **uniform stability** $\beta$ at sample size $m$ with respect to $\ell$ if
--
--   $$\forall S \in Z^m,\ \forall i \in \{1, \dots, m\}, \qquad \|\ell(A_S, \cdot) - \ell(A_{S^{\setminus i}}, \cdot)\|_\infty \le \beta,$$
--
--   that is, $|\ell(A_S, z) - \ell(A_{S^{\setminus i}}, z)| \le \beta$ for every sample $S$, every index $i$ and every point $z \in Z$. Here $S^{\setminus i}$ is $S$ with its $i$-th example removed.
--
--   Uniform stability is the strongest of the paper's stability notions: removing any one training example changes the loss of the learned hypothesis by at most $\beta$, everywhere. Considered as a function of $m$, the constant is written $\beta_m$; it is the hypothesis of the paper's exponential generalization bounds (Theorem 12).
--
--   **Formalization Note** The sup norm is written as "for every $z$", and $S$ ranges over every point of $Z^m$, not almost every one. The definition is the *remove-one* notion of the paper, which differs from the replace-one notion of uniform stability in Mohri, Rostamizadeh and Talwalkar (published as `FoundationsML_Stability_UniformlyStable`); the two give different constants.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 504, Definition 6, Eq. (7)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_StabGen_Hypothesis_Setting

namespace StabGen.Uniform

open FoundationsML.Stability

/-- **Uniform stability** (Bousquet & Elisseeff 2002, Definition 6, p. 504, eq. (7)).
An algorithm `A` has uniform stability `β` with respect to the loss `ℓ(f, (x, y)) = L (f x) y`
at sample size `m` if for every training set `S ∈ Z^m`, every `i ∈ {1, …, m}` and every point
`z ∈ Z`, `|ℓ(A_S, z) − ℓ(A_{S^{\i}}, z)| ≤ β`, i.e. `‖ℓ(A_S, ·) − ℓ(A_{S^{\i}}, ·)‖_∞ ≤ β`.
Here `S^{\i}` is `S` with its `i`-th example removed (remove-one, not replace-one). The
condition quantifies over every sample, not almost every one. -/
def HasUniformStability {X Y Y' : Type*} (L : Y' → Y → ℝ) (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (m : ℕ) (β : ℝ) : Prop :=
  ∀ S : Fin m → X × Y, ∀ i : Fin m, ∀ z : X × Y,
    |Loss L (A (StabGen.Hypothesis.trainingSet S)) z - Loss L (A (StabGen.Hypothesis.removeAt S i)) z| ≤ β

end StabGen.Uniform


