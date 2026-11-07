-- Prove2me | Definitions.Def_PredAdvice_IsSeparated
-- name    : PredAdvice_IsSeparated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:44.420045+00:00
-- url     : https://prove2.me/theorems/55ffb7a9-a9bc-436a-b966-e1d4fd857b59
-- title:
--   Colourings, shifted colours, isolation and separated small pairs
-- statement:
--   Fix integers $D,L$ and colourings $\chi_1,\dots,\chi_L : V\to[2D]$. The **$u$-shifted colour** of $h$ under $\chi_j$ is $c_{j,u}(h)=\chi_j(h)+\mathrm{dist}(u,h)$. The colouring $\chi_j$ **isolates** $h$ for $(u,v)$ if $h\in H^\circ_{u,v}$ and
--   $$
--   c_{j,u}(h)\neq c_{j,u}(h') \quad\text{for every } h'\in H^\circ_{u,v}\setminus\{h\}.
--   $$
--   A small pair $(u,v)$ is **unseparated** if some $h\in H^\circ_{u,v}$ is isolated by none of the colourings, and **separated** (a separated small pair) otherwise. Finally $j(u,v,h)=\min\{j : \chi_j \text{ isolates } h \text{ for } (u,v)\}$, stated as the predicate "$\chi_j$ isolates $h$ and no earlier colouring does".
--
--   **Formalization Note** The index $j\in[L]$ is an element of $\{0,\dots,L-1\}$ and the colour $\chi_j(h)\in[2D]$ is stored as an element of $\{0,\dots,2D-1\}$ plus one. Trivial pairs $(u,u)$ are separated, since $H^\circ_{u,u}=\emptyset$; the statements exclude them where the paper does.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3.2, p.12; §3.3, p.12

import Mathlib
import Definitions.Def_PredAdvice_H

set_option autoImplicit false

namespace PredAdvice

/-- `L` colourings `χ_1, …, χ_L : V → [2D]` (Kopelowitz, Korin, Roditty, *Using Small Advice to
Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3.2, p.12).

**Formalization Note** The index `j ∈ [L]` is `Fin L` (`0, …, L−1` for `1, …, L`) and the colour
`χ_j(h) ∈ [2D]` is `(χ j h).val + 1` with `χ j h : Fin (2D)`. -/
abbrev Colorings (V : Type*) (D L : ℕ) := Fin L → V → Fin (2 * D)

/-- The `u`-shifted colouring `c_{j,u}(h) := χ_j(h) + dist(u, h)` (§3.2, p.12).

**Formalization Note** `χ_j(h) = (χ j h).val + 1 ∈ [2D]`. The distance is read through
`ENat.toNat`; it is used only for `h ∈ H°_{u,v}`, where `dist(u, h)` is finite. -/
noncomputable def shiftedColor {V : Type*} {D L : ℕ} (G : Digraph V) (χ : Colorings V D L)
    (j : Fin L) (u h : V) : ℕ :=
  ((χ j h).val + 1) + (dist G u h).toNat

/-- `χ_j` **isolates** `h` for `(u, v)` (§3.2, p.12): `h ∈ H°_{u,v}` and
`c_{j,u}(h) ≠ c_{j,u}(h′)` for every `h′ ∈ H°_{u,v} \ {h}`. -/
def Isolates {V : Type*} [Fintype V] [DecidableEq V] {D L : ℕ} (G : Digraph V)
    (χ : Colorings V D L) (j : Fin L) (u v h : V) : Prop :=
  h ∈ Hcirc G u v ∧ ∀ h' ∈ Hcirc G u v, h' ≠ h → shiftedColor G χ j u h ≠ shiftedColor G χ j u h'

/-- A small pair `(u, v)` is **unseparated** (proof of Lemma 3.3, p.12) if some `h ∈ H°_{u,v}` is
isolated for `(u, v)` by none of the `L` colourings. -/
def IsUnseparated {V : Type*} [Fintype V] [DecidableEq V] {D L : ℕ} (G : Digraph V)
    (χ : Colorings V D L) (u v : V) : Prop :=
  IsSmall G D u v ∧ ∃ h ∈ Hcirc G u v, ∀ j : Fin L, ¬ Isolates G χ j u v h

/-- A **separated small pair** (§3.3, p.12: "small pairs that are not unseparated"): `(u, v)` is
small and every `h ∈ H°_{u,v}` is isolated for `(u, v)` by at least one colouring `χ_j`.

**Formalization Note** "Separated" includes "small", as in the paper's use. Trivial pairs `(u, u)`
are separated (their `H°` is empty); the paper excludes them separately ("nontrivial"), and so do
the statements of the mission. -/
def IsSeparated {V : Type*} [Fintype V] [DecidableEq V] {D L : ℕ} (G : Digraph V)
    (χ : Colorings V D L) (u v : V) : Prop :=
  IsSmall G D u v ∧ ∀ h ∈ Hcirc G u v, ∃ j : Fin L, Isolates G χ j u v h

/-- `j = j(u, v, h) := min{j ∈ [L] | χ_j isolates h for (u, v)}` (§3.3, p.12), as a predicate:
`χ_j` isolates `h` for `(u, v)` and no earlier colouring does. -/
def IsFirstIsolating {V : Type*} [Fintype V] [DecidableEq V] {D L : ℕ} (G : Digraph V)
    (χ : Colorings V D L) (j : Fin L) (u v h : V) : Prop :=
  Isolates G χ j u v h ∧ ∀ j' : Fin L, j' < j → ¬ Isolates G χ j' u v h

end PredAdvice


