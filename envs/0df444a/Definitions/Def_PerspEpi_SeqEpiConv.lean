-- Prove2me | Definitions.Def_PerspEpi_SeqEpiConv
-- name    : PerspEpi_SeqEpiConv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:34.29398+00:00
-- url     : https://prove2.me/theorems/1d844d73-b6c7-431d-ade9-eccd1f111796
-- title:
--   Epi-convergence of a sequence of functions
-- statement:
--   A sequence $f_k : X \to \overline{\mathbb R}$ **epi-converges** to $f$, written $f_k \xrightarrow{e} f$, if for every $x \in X$
--
--   $$
--   \forall\, x_k \to x:\ \liminf_{k\to\infty} f_k(x_k) \ge f(x), \qquad \exists\, x_k \to x:\ \limsup_{k\to\infty} f_k(x_k) \le f(x).
--   $$
--
--   **Formalization Note** $\liminf$ and $\limsup$ are taken in the complete lattice `EReal`.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §1.2 Notation, p.4

import Mathlib

namespace PerspEpi

/-- **Epi-convergence of a sequence.** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §1.2 Notation, p.4: "{f_k} epi-converges
to f if ∀x ∈ E: ∀{x_k} → x : liminf_{k→∞} f_k(x_k) ≥ f(x), ∃{x_k} → x : limsup_{k→∞} f_k(x_k) ≤ f(x)".

**Formalization Note.** `liminf`/`limsup` are taken in the complete lattice `EReal`. -/
def SeqEpiConv {X : Type*} [TopologicalSpace X] (F : ℕ → X → EReal) (g : X → EReal) : Prop :=
  ∀ x : X,
    (∀ xs : ℕ → X, Filter.Tendsto xs Filter.atTop (nhds x) →
      g x ≤ Filter.liminf (fun k => F k (xs k)) Filter.atTop) ∧
    (∃ xs : ℕ → X, Filter.Tendsto xs Filter.atTop (nhds x) ∧
      Filter.limsup (fun k => F k (xs k)) Filter.atTop ≤ g x)

end PerspEpi


