-- Prove2me | Definitions.Def_UltrametricFit_avgDist
-- name    : UltrametricFit_avgDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:56.084602+00:00
-- url     : https://prove2.me/theorems/8f34755f-99bd-4513-ad35-222fb66f091a
-- title:
--   Pseudometrics, the average distance between two sets, and $\phi$
-- statement:
--   A **pseudometric** on the species is a symmetric $d$ with $d(i,i)=0$ and the triangle inequality; distinct species may be at distance $0$. The **distance between two non-empty sets** is the average
--   $$d(A,B)=\frac{1}{|A||B|}\sum_{i\in A,\,j\in B}d(i,j),$$
--   $\mathbb E_{i\in A}[f(i)]$ is the uniform average of $f$ over $A$, and $\phi(x)=\min\{x,1-x\}$.
--
--   **Formalization Note** On an empty set the average evaluates to the junk value $0$; each statement that needs non-emptiness has it, directly or because nodes of a merge forest are non-empty. For $A=B$ the sum runs over all ordered pairs, including $i=j$.
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §2, p.7; §1, p.2 (pseudometric); §4.2, p.9 (φ)

import Mathlib

namespace UltrametricFit

/-- **Pseudometric on the species**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…): the paper's "metric" `([n], d)` of §2, p.7 and §4.1, p.8. The LP solution is
"technically a pseudometric, since 0 distances are allowed" (§1, p.2), so `d i j = 0` is permitted
for `i ≠ j`. Nonnegativity follows from these three clauses. -/
structure IsPseudometric {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop where
  self : ∀ i, d i i = 0
  symm : ∀ i j, d i j = d j i
  triangle : ∀ i j k, d i j ≤ d i k + d k j

/-- **Distance between two sets**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §2, p.7: `d(A, B) = (1/(|A||B|)) · Σ_{i∈A, j∈B} d(i, j)`.

**Formalization Note.** The page defines this for non-empty sets. In Lean the empty case evaluates
to the junk `0` (division by zero), so each statement that needs it carries non-emptiness, and the
nodes of a merge forest are non-empty automatically. With `A = B`, the sum runs over all ordered
pairs, including `i = j`, as the proof of Claim 8 (p.9) needs. -/
noncomputable def avgDist {n : ℕ} (d : Fin n → Fin n → ℝ) (A B : Finset (Fin n)) : ℝ :=
  (∑ i ∈ A, ∑ j ∈ B, d i j) / ((A.card : ℝ) * (B.card : ℝ))

/-- The uniform average `E_{i∈A}[f(i)]`, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §2, p.6 ("i ∼ A"), Lemma 12, p.10. -/
noncomputable def avgOver {n : ℕ} (f : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  (∑ i ∈ A, f i) / (A.card : ℝ)

/-- `φ(x) = min{x, 1 − x}`, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…),
§4.2, p.9. -/
noncomputable def phi (x : ℝ) : ℝ := min x (1 - x)

end UltrametricFit


