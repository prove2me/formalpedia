-- Prove2me | Definitions.Def_GoodQLTC_IsRegular
-- name    : GoodQLTC_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:43:53.618123+00:00
-- url     : https://prove2.me/theorems/a6f11ec2-f3dc-4d41-a211-e1105e1a8b01
-- title:
--   Regular cubical complex with degrees $\{n_i\}$ (Definition 4.2)
-- statement:
--   For a vertex $x$ and $i\in[t]$ let $E_i(x)=\{e\in X(\{i\}):x\le e\}$. The complex is **regular with degrees $\{n_i\}_{i\in[t]}$** if for every vertex $x$: $|E_i(x)|=n_i$ for every $i$, and for every $I\subseteq[t]$ and every family $\{e_i\}_{i\in I}$ with $e_i\in E_i(x)$ there is a unique $f\in X(I)$ with $x\le f$ and $e_i\le f$ for all $i\in I$.
--
--   **Formalization Note** $E_i(x)$ is the type `EdgeType`. The standing assumption $2\le n_1\le\dots\le n_t$ of §4.1 is stated in the theorems, not in the definition.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Definition 4.2, p.15 (PDF p.18)

import Mathlib
import Definitions.Def_GoodQLTC_dir

namespace GoodQLTC

/-- The edges `E_i(x) := {e ∈ X({i}) : x ≤ e}` in direction `i` through a vertex `x`, Gay–Jeronimo,
arXiv:2609.20780 (held version), §4.1, p.15, as a type.

**Formalization Note.** A subtype of `X`; `Fintype` and `DecidableEq` instances are classical. -/
def EdgeType {X : Type} [PartialOrder X] {t : ℕ} (φ : X → Fin t → Option Bool) (x : X)
    (i : Fin t) : Type :=
  {e : X // dir φ e = {i} ∧ x ≤ e}

noncomputable instance {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) (x : X) (i : Fin t) : Fintype (EdgeType φ x i) := by
  classical
  unfold EdgeType
  infer_instance

noncomputable instance {X : Type} [PartialOrder X] {t : ℕ} (φ : X → Fin t → Option Bool) (x : X)
    (i : Fin t) : DecidableEq (EdgeType φ x i) :=
  Classical.decEq _

/-- A **regular** cubical complex with degrees `{n_i}_{i∈[t]}`, Gay–Jeronimo, arXiv:2609.20780
(held version), Definition 4.2, p.15: for every vertex `x`, `|E_i(x)| = n_i` for every `i ∈ [t]`,
and for every `I ⊆ [t]` and every family `{e_i}_{i∈I}` with `e_i ∈ E_i(x)` there is a unique
`f ∈ X(I)` with `x ≤ f` and `e_i ≤ f` for all `i ∈ I`.

**Formalization Note.** Vertices are the faces of dimension `0`. A family `{e_i}_{i∈I}` is a
function `e : Fin t → X` whose values outside `I` are ignored. The standing assumption
`2 ≤ n_1 ≤ ⋯ ≤ n_t` (p.15) is not part of the definition; theorems state it. -/
def IsRegular {X : Type} [PartialOrder X] [Fintype X] {t : ℕ} (φ : X → Fin t → Option Bool)
    (n : Fin t → ℕ) : Prop :=
  ∀ x : X, fdim φ x = 0 →
    (∀ i, Fintype.card (EdgeType φ x i) = n i) ∧
    ∀ (I : Finset (Fin t)) (e : Fin t → X), (∀ i ∈ I, dir φ (e i) = {i} ∧ x ≤ e i) →
      ∃! f : X, dir φ f = I ∧ x ≤ f ∧ ∀ i ∈ I, e i ≤ f

end GoodQLTC


