-- Prove2me | Definitions.Def_GoodQLTC_IsExpanding
-- name    : GoodQLTC_IsExpanding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:01.289256+00:00
-- url     : https://prove2.me/theorems/82e65b4c-88b9-46db-bdf8-ec1666f3eeef
-- title:
--   $\lambda$-expanding cubical complex (Definition 4.5)
-- statement:
--   For $I\subsetneq[t]$, $j\notin I$, the parallel face graph $G_{I,j}$ has vertex set $X(I)$ and an edge $q\in X(I\cup\{j\})$ between its two facets $f^0_j(q),f^1_j(q)$ of type $I$. Its normalized adjacency operator is $(M_{I,j}z)(f)=\frac1{n_j}\sum_{q\in X(I\cup\{j\}),\,f\le q}z(f^{1-\phi_j(f)}_j(q))$. For $c\in\{0,1\}^{[t]\setminus(I\cup\{j\})}$ put $C_{I,j,c}=\{f\in X(I):\phi(f)|_{[t]\setminus(I\cup\{j\})}=c\}$ and $\sigma_C(f)=(-1)^{\phi_j(f)}$.
--
--   For $0\le\lambda<1$, $X$ is **$\lambda$-expanding** if for all $I,j,c$ the graph induced on $C=C_{I,j,c}$ is connected and
--   $$
--   \|M_Cz\|_2\le\lambda\|z\|_2\qquad\text{for every }z\in\mathrm{span}\{1_C,\sigma_C\}^{\perp}\subseteq\mathbb R^C .
--   $$
--
--   **Formalization Note** $0\le\lambda<1$ is part of the predicate; vectors on $C$ are functions on $X$ vanishing off $C$, and the norm bound is stated for squares.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.1 and Definition 4.5, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_GoodQLTC_dir

namespace GoodQLTC

open Classical in
/-- The set `C_{I,j,c} := {f ∈ X(I) : ϕ(f)|_{[t]∖(I∪{j})} = c}`, Gay–Jeronimo, arXiv:2609.20780
(held version), §4.1, p.16. **Formalization Note.** `c : Fin t → Bool`; its values on `I ∪ {j}`
are ignored. -/
noncomputable def transverseClass {X : Type} [Fintype X] {t : ℕ} (φ : X → Fin t → Option Bool)
    (I : Finset (Fin t)) (j : Fin t) (c : Fin t → Bool) : Finset X :=
  Finset.univ.filter fun f => dir φ f = I ∧ ∀ i, i ∉ I → i ≠ j → φ f i = some (c i)

open Classical in
/-- The normalized adjacency operator of the parallel face graph `G_{I,j}` (arXiv:2609.20780,
§4.1, p.16): `(M_{I,j} z)(f) := (1/n_j) ∑_{q ∈ X(I∪{j}), f ≤ q} z(f_j^{1−ϕ_j(f)}(q))`.
**Formalization Note.** `f_j^{1−ϕ_j(f)}(q)` is written as the sum over the faces `g ∈ X(I)` with
`g ≤ q` and `ϕ_j(g) ≠ ϕ_j(f)`; in a cubical complex there is exactly one such `g` for each
`q ≥ f` (Definition 4.1 (1)). -/
noncomputable def parallelWalk {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) (n : Fin t → ℕ) (I : Finset (Fin t)) (j : Fin t)
    (z : X → ℝ) (f : X) : ℝ :=
  (1 / (n j : ℝ)) * ∑ q ∈ Finset.univ.filter (fun q => dir φ q = insert j I ∧ f ≤ q),
    ∑ g ∈ Finset.univ.filter (fun g => dir φ g = I ∧ g ≤ q ∧ φ g j ≠ φ f j), z g

/-- The sign `σ_C(f) := (−1)^{ϕ_j(f)}` (arXiv:2609.20780, §4.1, p.16). -/
def paritySign {X : Type} {t : ℕ} (φ : X → Fin t → Option Bool) (j : Fin t) (f : X) : ℝ :=
  if φ f j = some true then -1 else 1

/-- A **`λ`-expanding** cubical complex, Gay–Jeronimo, arXiv:2609.20780 (held version),
Definition 4.5, p.16: for `0 ≤ λ < 1`, for every `I ⊊ [t]`, `j ∈ [t] ∖ I` and
`c ∈ {0,1}^{[t]∖(I∪{j})}`, the graph induced on `C = C_{I,j,c}` is connected and
`‖M_C z‖₂ ≤ λ ‖z‖₂` for every `z ∈ span{1_C, σ_C}^⊥` (usual scalar product on `ℝ^C`).

**Formalization Note.** `0 ≤ λ < 1` is part of the predicate. A vector `z ∈ ℝ^C` is a function
`X → ℝ` vanishing off `C`; `z ⊥ 1_C` and `z ⊥ σ_C` are the two sums; the norm inequality is stated
for squares. The induced graph joins distinct `f, g ∈ C` lying below a common `q ∈ X(I ∪ {j})`.
`n` is the degree vector of the regular complex (it normalizes `M_{I,j}`). -/
def IsExpanding {X : Type} [PartialOrder X] [Fintype X] {t : ℕ} (φ : X → Fin t → Option Bool)
    (n : Fin t → ℕ) (lam : ℝ) : Prop :=
  0 ≤ lam ∧ lam < 1 ∧
  ∀ (I : Finset (Fin t)) (j : Fin t) (c : Fin t → Bool), j ∉ I →
    (SimpleGraph.fromRel fun a b : transverseClass φ I j c =>
        ∃ q : X, dir φ q = insert j I ∧ a.1 ≤ q ∧ b.1 ≤ q).Connected ∧
    ∀ z : X → ℝ, (∀ f, f ∉ transverseClass φ I j c → z f = 0) →
      ∑ f ∈ transverseClass φ I j c, z f = 0 →
      ∑ f ∈ transverseClass φ I j c, paritySign φ j f * z f = 0 →
      ∑ f ∈ transverseClass φ I j c, (parallelWalk φ n I j z f) ^ 2 ≤
        lam ^ 2 * ∑ f ∈ transverseClass φ I j c, (z f) ^ 2

end GoodQLTC


