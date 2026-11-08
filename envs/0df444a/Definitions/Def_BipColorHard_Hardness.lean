-- Prove2me | Definitions.Def_BipColorHard_Hardness
-- name    : BipColorHard_Hardness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:59.267515+00:00
-- url     : https://prove2.me/theorems/d2f7eaf3-0cd1-48a5-ab14-25265fa9b894
-- title:
--   Coloring count, maximum degree, the factor $\exp(\pm x)$, and NP-hardness of approximating within $\exp(c\cdot\mathrm{size})$
-- statement:
--   For a graph $G$ and a positive integer $q$, $Z_q(G)$ is the number of **proper $q$-colorings** of $G$: maps $\sigma:V(G)\to[q]$ with $\sigma(u)\ne\sigma(v)$ on every edge. A graph has **maximum degree at most $\Delta$** when every vertex has at most $\Delta$ neighbours.
--
--   A rational $r$ is **within the factor $e^{\pm x}$** of a real $Z$ when
--   $$e^{-x}Z\le r\le e^{x}Z.$$
--
--   **Approximating $F$ within $\exp(c\cdot\mathrm{size})$ on a class of instances is NP-hard** when, for every language $L$ in NP over any finite nonempty alphabet, there are a polynomial-time map $x\mapsto I_x$ into the class and a polynomial-time answer map $g$ such that for every string $x$ and every rational $r$ within the factor $e^{\pm c\,\mathrm{size}(I_x)}$ of $F(I_x)$, the map $g$, reading $x$ and $r$, outputs "yes" exactly when $x\in L$.
--
--   The statement *approximating $Z_q$ within $\exp(cn)$ on bipartite graphs of maximum degree at most $\Delta$ is NP-hard* is this notion with $\mathrm{size}$ the number of vertices of the queried graph. The degree $D$ of the coloring graphs built by the reduction is $D=q+1$ for $q\ge5$ and $D=5$ for $q=3$. An instance of gap MAX-CUT is a graph and an integer threshold $\tau$, encoded in that order.
--
--   These are the objects of the goal theorem.
--
--   **Formalization Note** Graphs are `SimpleGraph (Fin N)` with the published binary encoding `encGraph`. The reduction queries an approximation once and post-processes the answer, which is the shape the proof of Theorem 1 builds, and it implies hardness under polynomial-time oracle reductions. Machines, NP and polynomial time are from the published `CookPvsNP` definitions.
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Theorem 1, p.2 (PDF p.4); §3, p.6 (PDF p.8); proof of Proposition 8, §4.4, p.19 (PDF p.21)

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_NSWApxHard_Reduction_CubicVC
import Definitions.Def_ImpatientMatching_Input
import Definitions.Def_IIDMatchHard_ApproxNPHard

set_option autoImplicit false

namespace BipColorHard

open NSWApxHard.Reduction (GraphInput encGraph)

/-- Maximum degree at most `Δ`: every vertex has at most `Δ` neighbours. Galanis, Guo, He,
Štefankovič, Vigoda, *NP-hardness for Bipartite Colorings up to the Maximum Degree* (manuscript of
Nov. 3, 2026, sha256 78a66d1f…), Theorem 1, p.2 (PDF p.4). -/
def MaxDegLe (Δ : ℕ) (I : GraphInput) : Prop := ∀ v, (I.G.neighborSet v).ncard ≤ Δ

/-- `Z_q(G)`, the number of proper `q`-colorings of the graph `I` (manuscript sha256 78a66d1f…, §1,
p.1 (PDF p.3)).

**Formalization Note.** The vertex set `Fin N` and the colour set `Fin q` are finite, so `Nat.card`
is the true count. -/
noncomputable def coloringCount (q : ℕ) (I : GraphInput) : ℕ := Nat.card (I.G.Coloring (Fin q))

/-- `r` is within the factor `exp(±x)` of `Z`: `e^{-x} Z ≤ r ≤ e^{x} Z`. This is how the manuscript
(sha256 78a66d1f…) uses "within a factor", e.g. in the proof of Proposition 8, §4.4, p.19 (PDF p.21). -/
def WithinExp (x Z : ℝ) (r : ℚ) : Prop := Real.exp (-x) * Z ≤ r ∧ (r : ℝ) ≤ Real.exp x * Z

/-- **Approximating `F` within the factor `exp(c · size)` on the inputs satisfying `Dom` is NP-hard**:
for every language `L` in NP over any finite nonempty alphabet there are a polynomial-time instance
map `f` (with values in `Dom`, measured on the encoding `enc`) and a polynomial-time answer map `g`
such that for every string `x` and **every** rational `r` within the factor
`exp(± c · size (f x))` of `F (f x)`, the map `g`, reading `x` and `r`, outputs `[true]` exactly when
`x ∈ L`. Manuscript sha256 78a66d1f…, Theorem 1, p.2 (PDF p.4), and its proof, p.8 (PDF p.10).

**Formalization Note.** "NP-hard" is read as a polynomial-time reduction from every NP language
that queries an approximation **once** and post-processes the answer: the proof of Theorem 1 composes
one query each in Propositions 8 and 9, starting from a many-one gap problem. It implies hardness
under polynomial-time oracle (Cook) reductions. The size is that of the queried instance, not `|x|`.
Machines, `NP` and polynomial time are Cook's (`CookPvsNP`). -/
def ExpApproxNPHard {α : Type} (enc : α → List Bool) (Dom : α → Prop) (F : α → ℝ) (size : α → ℕ)
    (c : ℝ) : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym] (L : CookPvsNP.Lang Sym), L ∈ CookPvsNP.NP Sym →
    ∃ (f : List Sym → α) (g : List (Option (Sym ⊕ Bool)) → List Bool),
      CookPvsNP.PolyTimeComputable (fun x => enc (f x)) ∧
      CookPvsNP.PolyTimeComputable g ∧
      (∀ x, Dom (f x)) ∧
      ∀ (x : List Sym) (r : ℚ), WithinExp (c * size (f x)) (F (f x)) r →
        (g (IIDMatchHard.pairInput x r) = [true] ↔ x ∈ L)

/-- Approximating the number of proper `q`-colorings of an `n`-vertex bipartite graph of maximum
degree at most `Δ` within the factor `exp(cn)` is NP-hard. Manuscript sha256 78a66d1f…, Theorem 1,
p.2 (PDF p.4).

**Formalization Note.** Graphs are `SimpleGraph (Fin N)`, encoded by `encGraph` (`N`, then the `N²`
adjacency bits); `n` is the `N` of the queried graph. -/
def ColoringApproxNPHard (q Δ : ℕ) (c : ℝ) : Prop :=
  ExpApproxNPHard encGraph (fun I => I.G.IsBipartite ∧ MaxDegLe Δ I)
    (fun I => (coloringCount q I : ℝ)) GraphInput.N c

/-- The degree `D` of the coloring graphs: `D = q + 1` if `q ≥ 5` and `D = 5` if `q = 3`. Manuscript
sha256 78a66d1f…, §3, p.6 (PDF p.8).

**Formalization Note.** Only odd `q ≥ 3` is used; the value on other `q` is irrelevant. -/
def bipDeg (q : ℕ) : ℕ := if q = 3 then 5 else q + 1

/-- The encoding of a gap MAX-CUT instance `(F, τ)` (manuscript sha256 78a66d1f…, Theorem 6, p.6
(PDF p.8)): the graph, then the integer `τ` as a rational. -/
noncomputable def encGap (p : GraphInput × ℤ) : List Bool :=
  encGraph p.1 ++ ImpatientMatching.encRat (p.2 : ℚ)

end BipColorHard


