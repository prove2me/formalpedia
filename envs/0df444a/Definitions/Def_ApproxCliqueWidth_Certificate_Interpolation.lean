-- Prove2me | Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation
-- name    : ApproxCliqueWidth_Certificate_Interpolation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:29:44.028451+00:00
-- url     : https://prove2.me/theorems/85e90a62-33b1-4a33-9031-558631e95231
-- title:
--   Interpolation $f^*$ of a submodular function and the interpolation $f_{\min}$
-- statement:
--   Let $V$ be a finite set and write $3^V = \{(X, Y) : X, Y \subseteq V,\ X \cap Y = \emptyset\}$ for the set of disjoint pairs of subsets. Let $f : 2^V \to \mathbb{Z}$. A function $f^* : 3^V \to \mathbb{Z}$ is an **interpolation** of $f$ if
--
--   1. $f^*(X, V \setminus X) = f(X)$ for all $X \subseteq V$;
--   2. (uniform) if $C \cap D = \emptyset$, $A \subseteq C$ and $B \subseteq D$, then $f^*(A, B) \le f^*(C, D)$;
--   3. (submodular) for all $(A, B), (C, D) \in 3^V$,
--   $$f^*(A, B) + f^*(C, D) \ge f^*(A \cap C, B \cup D) + f^*(A \cup C, B \cap D);$$
--   4. $f^*(\emptyset, \emptyset) = f(\emptyset)$.
--
--   The function $f_{\min}$ on $3^V$ is
--   $$f_{\min}(X, Y) = \min_{X \subseteq Z \subseteq V \setminus Y} f(Z),$$
--   a minimum over a nonempty finite family because $X \cap Y = \emptyset$.
--
--   An interpolation extends $f$ from bipartitions $(X, V\setminus X)$ to partial bipartitions, monotonically and submodularly; it is the device through which the branch-width algorithm finds matroid bases and certifies that a set is not well-linked.
--
--   **Formalization Note** $f^*$ is a function on all pairs of `Finset V`; every axiom quantifies only over disjoint pairs, and values on non-disjoint pairs are never constrained. The paper's standing assumptions on $f$ in Definition 4.1 (submodular, with $f(\emptyset) \le f(X)$ for all $X$) are hypotheses of the theorems that use the notion. $f_{\min}(X, Y)$ is `Finset.inf'` over the nonempty family $\{Z : X \subseteq Z,\ Z \cap Y = \emptyset\}$; on non-disjoint pairs, outside $3^V$, it returns the placeholder $0$, which no statement uses.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 518, Definition 4.1 and the definition of 3^V; p. 519, definition of f_min

import Mathlib

namespace ApproxCliqueWidth.Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Oum–Seymour Definition 4.1 (p. 518). A function `fstar` on pairs of subsets is an
interpolation of `f : 2^V → ℤ` if, on the domain `3^V` of **disjoint** pairs,
(i) `f*(X, V \ X) = f(X)`; (ii) (uniform) `f*(A, B) ≤ f*(C, D)` whenever `C ∩ D = ∅`,
`A ⊆ C`, `B ⊆ D`; (iii) (submodular) `f*(A, B) + f*(C, D) ≥ f*(A ∩ C, B ∪ D) + f*(A ∪ C, B ∩ D)`
for disjoint `(A, B)`, `(C, D)`; (iv) `f*(∅, ∅) = f(∅)`. Values of `fstar` on non-disjoint pairs
are never constrained. (The paper's standing assumptions on `f` — submodular with `f(∅) ≤ f(X)` —
are hypotheses of the theorems that use this notion.) -/
def IsInterpolation (f : Finset V → ℤ) (fstar : Finset V → Finset V → ℤ) : Prop :=
  (∀ X : Finset V, fstar X Xᶜ = f X) ∧
  (∀ A B C D : Finset V, Disjoint C D → A ⊆ C → B ⊆ D → fstar A B ≤ fstar C D) ∧
  (∀ A B C D : Finset V, Disjoint A B → Disjoint C D →
      fstar (A ∩ C) (B ∪ D) + fstar (A ∪ C) (B ∩ D) ≤ fstar A B + fstar C D) ∧
  fstar ∅ ∅ = f ∅

/-- Oum–Seymour p. 519: `f_min(X, Y) = min_{X ⊆ Z ⊆ V \ Y} f(Z)`. The family
`{Z | X ⊆ Z, Z ∩ Y = ∅}` is nonempty exactly when `X ∩ Y = ∅` (i.e. on `3^V`); on the
non-disjoint pairs, outside the paper's domain, the value `0` is a placeholder never used. -/
noncomputable def fmin (f : Finset V → ℤ) (X Y : Finset V) : ℤ :=
  if h : (Finset.univ.filter (fun Z : Finset V => X ⊆ Z ∧ Disjoint Z Y)).Nonempty then
    (Finset.univ.filter (fun Z : Finset V => X ⊆ Z ∧ Disjoint Z Y)).inf' h f
  else 0

end ApproxCliqueWidth.Certificate


