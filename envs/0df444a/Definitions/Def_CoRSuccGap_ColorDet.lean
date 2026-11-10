-- Prove2me | Definitions.Def_CoRSuccGap_ColorDet
-- name    : CoRSuccGap_ColorDet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:47:38.509508+00:00
-- url     : https://prove2.me/theorems/71aeedea-488d-4e66-bc90-eadc9f3f5d77
-- title:
--   Colour labels, colour-determined relations, colour tables $X[\mu]$ and off-diagonal supports $S_X$
-- statement:
--   Let $\chi$ be a colouring of the pairs of distinct vertices of $V$ with palette $\Lambda$. Extend it to loops by giving every loop $(u,u)$ the extra **label** $\mathbf{id}$, which is not a colour; a pair $(u,v)$ with $u\neq v$ has label $\chi(u,v)$. A relation $X\subseteq V^2$ is **colour-determined** if $X(u,v)$ depends only on the label of $(u,v)$. For such $X$ and a label $\ell\in\Lambda\cup\{\mathbf{id}\}$, the **table entry** $X[\ell]\in\{0,1\}$ is the common value of $X$ at the pairs with label $\ell$, and
--
--   $$
--   S_X:=\{\mu\in\Lambda : X[\mu]=1\}
--   $$
--
--   is the **off-diagonal support** of $X$. Thus $X$ is the union of the colour classes $e_\mu$, $\mu\in S_X$, together with the diagonal if $X[\mathbf{id}]=1$.
--
--   Colour-determined relations are the values every circuit takes on a reference structure (Lemma 3.2); their tables are what the fold argument compares.
--
--   **Formalization Note** `lab χ u v : Option Λ` is the label (`none` stands for $\mathbf{id}$). `tab χ X ℓ` reads $X[\ell]$ as "$X$ holds at some pair with label $\ell$": for a colour-determined $X$ and a label that occurs this is the common value, and for a label that does not occur it is false. `supp χ X` is $S_X$.
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), §3.2, pp.18–19 (PDF 20–21)

import Mathlib

set_option autoImplicit false

namespace CoRSuccGap

/-!
# Colour-determined relations, colour tables and off-diagonal supports

Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), §3.2, pp.18–19 (PDF 20–21): "We extend χ to loops by giving every loop the extra label id,
which is not a color. A relation X ⊆ V² is color-determined if X(u, v) depends only on χ(u, v).
For such a relation, write X[μ] ∈ B for its common value at pairs (u, v) with χ(u, v) = μ, where
μ ∈ Λ ∪ {id}. These N + 1 values form a table, and S_X := {μ ∈ Λ : X[μ] = 1} is the off-diagonal
support of X."

**Formalization Note.**
* `lab χ u v : Option Λ` is the label of the pair `(u, v)`: `none` (the label id) on loops,
  `some (χ s(u, v))` otherwise. χ is never read on the diagonal.
* `ColorDet χ X`: `X u v` depends only on `lab χ u v`.
* `tab χ X ℓ` is the table entry X[ℓ], read as "X holds at some pair with label ℓ". For a
  colour-determined `X` and a label that occurs, this is the common value; for a label that does
  not occur it is false.
* `supp χ X` is S_X = {μ | X[μ] = 1}.
-/

variable {V : Type*} {Λ : Type*} [DecidableEq V]

/-- The label of a pair: the extra label id (`none`) on loops, the colour `χ s(u, v)` otherwise
(p.18). -/
def lab (χ : Sym2 V → Λ) (u v : V) : Option Λ :=
  if u = v then none else some (χ s(u, v))

/-- `X` is colour-determined: `X(u, v)` depends only on the label of `(u, v)` (p.18). -/
def ColorDet (χ : Sym2 V → Λ) (X : V → V → Prop) : Prop :=
  ∀ u v u' v' : V, lab χ u v = lab χ u' v' → (X u v ↔ X u' v')

/-- The table entry X[ℓ] (p.19): `X` holds at some pair with label `ℓ`. -/
def tab (χ : Sym2 V → Λ) (X : V → V → Prop) (ℓ : Option Λ) : Prop :=
  ∃ u v : V, lab χ u v = ℓ ∧ X u v

/-- The off-diagonal support S_X = {μ ∈ Λ : X[μ] = 1} (p.19). -/
def supp (χ : Sym2 V → Λ) (X : V → V → Prop) : Set Λ :=
  {μ | tab χ X (some μ)}

end CoRSuccGap


