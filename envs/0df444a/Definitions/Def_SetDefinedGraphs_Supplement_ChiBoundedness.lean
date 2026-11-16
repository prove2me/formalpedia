-- Prove2me | Definitions.Def_SetDefinedGraphs_Supplement_ChiBoundedness
-- name    : SetDefinedGraphs_Supplement_ChiBoundedness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:41:37.537171+00:00
-- url     : https://prove2.me/theorems/319e6ea6-79ac-42b4-bad6-34a46a246ecb
-- title:
--   Chromatic number of a digraph; $\chi$-bounded, polynomially $\chi$-bounded and bounded-$\chi$ classes; symmetrization; classes containing $\vec{\mathcal S}_D$
-- statement:
--   The chromatic number $\chi(G)$ of a digraph $G$ is the chromatic number of its underlying graph (orientations and loops ignored), exactly as the clique number $\omega(G)$ is. A **class of digraphs** is a property of digraphs; the classes used here are closed under isomorphism and contain only finite digraphs.
--
--   1. A class $\vec{\mathcal X}$ is **$\chi$-bounded** if there is $h:\mathbb N\to\mathbb N$ with $\chi(G)\le h(\omega(G))$ for all $G\in\vec{\mathcal X}$, and **polynomially $\chi$-bounded** if $h$ can be chosen to be a polynomial.
--   2. A class **has bounded chromatic number** if there is a constant $M$ with $\chi(G)\le M$ for all $G$ in it.
--   3. The **symmetrization** of a digraph adds, for every arc $(u,w)$, the arc $(w,u)$.
--   4. A class **contains $\vec{\mathcal S}_D$** if every $D$-dimensional shift digraph (induced subdigraph of a canonical shift digraph $\vec S(n,D)$) belongs to it, and it **contains the symmetrized $D$-dimensional shift digraphs** if the symmetrization of every such digraph belongs to it.
--
--   These notions express the dichotomy, decidability and reduction theorems of the paper.
--
--   **Formalization Note** $\chi$ is Mathlib's `chromaticNumber` (valued in $\mathbb N\cup\{\infty\}$) of `SimpleGraph.fromRel G.Adj`; a polynomial $h$ has natural-number coefficients (every real polynomial is bounded on $\mathbb N$ by one). The paper's $\chi$-boundedness quantifies over induced subgraphs of members; the classes it is applied to are hereditary.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.3 (PDF p.5): χ, χ-bounded, polynomially χ-bounded; §3 p.14 (PDF p.16): χ of a digraph; §3.5 p.18 (PDF p.20); p.4 (PDF p.6): symmetrization; §3.2 p.15 (PDF p.17): S⃗_D

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- The **chromatic number** `χ(G)` of a digraph `G`: the chromatic number of its underlying graph, the simple graph
obtained by ignoring orientations and loops (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes:
χ-boundedness meets tropical algebra*, arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.3 (PDF p.5) and §3
p.14 (PDF p.16)).

**Formalization Note** The underlying graph is `SimpleGraph.fromRel G.Adj`, exactly as for `ω` (`SetDefinedGraphs.omega`),
and `χ` is Mathlib's `chromaticNumber`, valued in `ℕ∞`. Every digraph in the classes of the mission is finite, so the
value is a natural number. -/
noncomputable def chi {W : Type} (G : Digraph W) : ℕ∞ :=
  (SimpleGraph.fromRel G.Adj).chromaticNumber

/-- A **class of digraphs**: a predicate on digraphs over arbitrary vertex types (`C W G` reads `G ∈ C`). The classes
of the mission (`InX f`, `InY f`, `InYPZ P Z`) are closed under isomorphism and contain only finite digraphs. -/
abbrev DigraphClass : Type 1 := ∀ (W : Type), Digraph W → Prop

/-- A class `X` of digraphs is **χ-bounded** (arXiv:2607.23754, p.3 and §3.5 p.18) if there is a function
`h : ℕ → ℕ` with `χ(G) ≤ h(ω(G))` for every `G ∈ X`.

**Formalization Note** The paper's definition quantifies over the induced subdigraphs of members of `X`; the classes to
which the mission applies it are hereditary, so the two agree. -/
def IsChiBounded (C : DigraphClass) : Prop :=
  ∃ h : ℕ → ℕ, ∀ (W : Type) (G : Digraph W), C W G → chi G ≤ (h (omega G) : ℕ∞)

/-- A class `X` of digraphs is **polynomially χ-bounded** (arXiv:2607.23754, p.3 and p.18) if the function `h` can be
chosen to be a polynomial: `χ(G) ≤ h(ω(G))` for every `G ∈ X`.

**Formalization Note** `h` is a polynomial with natural-number coefficients evaluated at `ω(G)`. A real polynomial is
bounded on `ℕ` by the natural-coefficient polynomial of the absolute values of its coefficients (rounded up), and the
bound is monotone in `h`, so the two notions agree. -/
def IsPolyChiBounded (C : DigraphClass) : Prop :=
  ∃ h : Polynomial ℕ, ∀ (W : Type) (G : Digraph W), C W G → chi G ≤ ((h.eval (omega G) : ℕ) : ℕ∞)

/-- A class of digraphs **has bounded chromatic number** (arXiv:2607.23754, §4.5 p.31, §5 p.35) if some constant
`M ∈ ℕ` bounds `χ(G)` for every `G` in it; "the chromatic number of the class is unbounded" is the negation. -/
def HasBoundedChromaticNumber (C : DigraphClass) : Prop :=
  ∃ M : ℕ, ∀ (W : Type) (G : Digraph W), C W G → chi G ≤ (M : ℕ∞)

/-- The **symmetrization** of a digraph (arXiv:2607.23754, §1.1 p.4, PDF p.6): it is obtained by adding, for every
arc `(u, w)`, the arc `(w, u)`. -/
def symmetrization {W : Type} (G : Digraph W) : Digraph W where
  Adj u w := G.Adj u w ∨ G.Adj w u

/-- A class `X` **contains the class `S⃗_D` of `D`-dimensional shift digraphs** (arXiv:2607.23754, p.4 and p.15):
every `D`-dimensional shift digraph (`SetDefinedGraphs.IsShiftDigraphDim D`) is in `X`. -/
def ContainsShiftDigraphs (D : ℕ) (C : DigraphClass) : Prop :=
  ∀ (W : Type) (G : Digraph W), IsShiftDigraphDim D G → C W G

/-- A class `X` **contains the class of symmetrized `D`-dimensional shift digraphs** (arXiv:2607.23754, p.4): the
symmetrization of every `D`-dimensional shift digraph is in `X`.

**Formalization Note** The class of symmetrized shift digraphs is the isomorphism closure of these symmetrizations; the
classes to which the mission applies this notion are closed under isomorphism, so membership of every symmetrization
is the same as containing that class. -/
def ContainsSymmShiftDigraphs (D : ℕ) (C : DigraphClass) : Prop :=
  ∀ (W : Type) (G : Digraph W), IsShiftDigraphDim D G → C W (symmetrization G)

end SetDefinedGraphs.Supplement


