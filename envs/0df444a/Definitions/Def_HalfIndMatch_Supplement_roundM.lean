-- Prove2me | Definitions.Def_HalfIndMatch_Supplement_roundM
-- name    : HalfIndMatch_Supplement_roundM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:02:34.898167+00:00
-- url     : https://prove2.me/theorems/62dabb66-c566-43ce-b56c-f46183bd2633
-- title:
--   Definition 2.4 — rounding a polynomial $f:\mathbb R^m\to\mathbb R^m$ to an induced matching $\mathcal M^\eta_f(G)$
-- statement:
--   Let $\mathcal E_n=\binom{[n]}{2}$ be the set of potential edges on the vertex set $[n]$ and $m=|\mathcal E_n|=\binom n2$. A graph $G$ on $[n]$ is identified with its edge-indicator vector $(G_e)_{e\in\mathcal E_n}\in\{0,1\}^m$, $G_e=\mathbb 1\{e\in E(G)\}$. A **polynomial of degree at most $D$** is a map $f=(f_e)_{e\in\mathcal E_n}:\mathbb R^m\to\mathbb R^m$ whose every coordinate $f_e$ is a real polynomial of degree at most $D$ in the $m$ variables $(G_{e'})_{e'\in\mathcal E_n}$; $f(G)$ denotes its value at the indicator vector of $G$.
--
--   Two distinct edges of $G$ **conflict** if they share an endpoint or an edge of $G$ joins an endpoint of one to an endpoint of the other. Set
--
--   $$A=\{e\in E(G):f_e(G)\ge1\},\qquad \tilde A=\{e\in A:\text{no distinct }e'\in A\text{ conflicts with }e\text{ in }G\},\qquad B=\{e\in\mathcal E_n:f_e(G)\in(\tfrac12,1)\}.$$
--
--   For $\eta>0$ the **rounded output** is
--
--   $$\mathcal M^\eta_f(G)=\begin{cases}\tilde A,&\text{if }|A\setminus\tilde A|+|B|\le\eta m,\\ \varnothing,&\text{otherwise.}\end{cases}$$
--
--   Here $A$ is the candidate edge set, $\tilde A$ the set surviving conflict pruning and $B$ the set of potential edges about which $f$ is unsure; $\eta$ is a tolerance for rounding errors. The output is always an induced matching of $G$. This rounding turns a low-degree polynomial into an induced-matching algorithm, the object of Theorems 2.6 and 2.7.
--
--   **Formalization Note** Vertices are `Fin n` (0-based) and potential edges are non-diagonal `Sym2 (Fin n)` (`Edges n`), the edge convention of the published `HalfIndMatch.IsInducedMatching`. A polynomial is `f : Edges n → MvPolynomial (Edges n) ℝ`, its degree is `totalDegree`, and `evalPoly f G e` is $f_e(G)$. $m$ is `mEdges n = (n.choose 2 : ℝ)`. The test $|A\setminus\tilde A|+|B|\le\eta m$ is made in $\mathbb R$. The module also declares `Edges`, `mEdges`, `edgeInd`, `evalPoly` and `Conflicts`. `roundM` is defined for every real $\eta$; the paper uses it for $\eta>0$.
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), §2.3, p.10 (PDF p.12): 𝓔ₙ, m, indicator vectors, polynomials of degree at most D; Definition 2.4, pp.10–11 (PDF pp.12–13)

import Mathlib
import Definitions.Def_HalfIndMatch_IsInducedMatching

open scoped Classical

namespace HalfIndMatch.Supplement

/-- The set `𝓔ₙ = ([n] choose 2)` of potential edges of a graph on `Fin n`: the unordered pairs of
distinct vertices. It has `m = C(n, 2)` elements.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), §2.3,
p.10 (PDF p.12).

**Formalization Note** Vertices are `Fin n` (the paper's `[n]`, 0-based) and a potential edge is a
non-diagonal `Sym2 (Fin n)`, the same edge convention as `HalfIndMatch.IsInducedMatching`. -/
abbrev Edges (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- `m = |𝓔ₙ| = C(n, 2)`, as a real number. -/
noncomputable def mEdges (n : ℕ) : ℝ := (n.choose 2 : ℝ)

/-- The edge-indicator vector `(G_e)_{e ∈ 𝓔ₙ} ∈ {0, 1}^m` of a graph `G` on `Fin n`,
`G_e = 1{e ∈ E(G)}` (§2.3, p.10, PDF p.12). -/
noncomputable def edgeInd {n : ℕ} (G : SimpleGraph (Fin n)) : Edges n → ℝ :=
  fun e => if (e : Sym2 (Fin n)) ∈ G.edgeSet then 1 else 0

/-- A polynomial map `f = (f_e)_{e ∈ 𝓔ₙ} : ℝ^m → ℝ^m`, each coordinate a real polynomial in the `m`
variables `(G_{e'})_{e' ∈ 𝓔ₙ}`, evaluated at the indicator vector of `G`: the vector
`f(G) = (f_e(G))_{e ∈ 𝓔ₙ}`. It has degree at most `D` when `(f e).totalDegree ≤ D` for every `e`
(§2.3, p.10, PDF p.12). -/
noncomputable def evalPoly {n : ℕ} (f : Edges n → MvPolynomial (Edges n) ℝ)
    (G : SimpleGraph (Fin n)) : Edges n → ℝ :=
  fun e => MvPolynomial.eval (edgeInd G) (f e)

/-- Two distinct edges `e, e'` of `G` **conflict** if they share an endpoint or an edge of `G` joins
an endpoint of one to an endpoint of the other (Definition 2.4, p.10, PDF p.12). -/
def Conflicts {n : ℕ} (G : SimpleGraph (Fin n)) (e e' : Sym2 (Fin n)) : Prop :=
  e ∈ G.edgeSet ∧ e' ∈ G.edgeSet ∧ e ≠ e' ∧ ∃ u ∈ e, ∃ v ∈ e', u = v ∨ G.Adj u v

/-- **Definition 2.4** (rounding of a polynomial to an induced matching). For a graph `G` on `Fin n`,
a polynomial `f` and `η > 0`, with
* `A = {e ∈ E(G) : f_e(G) ≥ 1}`,
* `Ã = {e ∈ A : no distinct e' ∈ A conflicts with e in G}`,
* `B = {e ∈ 𝓔ₙ : f_e(G) ∈ (1/2, 1)}`,
the output is `M^η_f(G) = Ã` if `|A \ Ã| + |B| ≤ η m`, and `∅` otherwise.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…),
Definition 2.4, pp.10–11 (PDF pp.12–13).

**Formalization Note** `A` contains only edges of `G`, `B` ranges over all potential edges `𝓔ₙ` and
uses the open interval `(1/2, 1)`; the comparison `|A \ Ã| + |B| ≤ η m` is non-strict and made in
`ℝ` with `m = C(n, 2)`. The output is a set of `Sym2 (Fin n)` (the base convention for matchings);
its size is its cardinality. The definition is stated for every real `η`; the paper uses it only
for `η > 0`. -/
noncomputable def roundM {n : ℕ} (η : ℝ) (f : Edges n → MvPolynomial (Edges n) ℝ)
    (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) :=
  let A : Finset (Edges n) :=
    Finset.univ.filter fun e => (e : Sym2 (Fin n)) ∈ G.edgeSet ∧ 1 ≤ evalPoly f G e
  let At : Finset (Edges n) :=
    A.filter fun e => ∀ e' ∈ A, e' ≠ e → ¬ Conflicts G (e' : Sym2 (Fin n)) e
  let B : Finset (Edges n) :=
    Finset.univ.filter fun e => 1 / 2 < evalPoly f G e ∧ evalPoly f G e < 1
  if (((A \ At).card + B.card : ℕ) : ℝ) ≤ η * mEdges n then
    At.map (Function.Embedding.subtype _)
  else ∅

end HalfIndMatch.Supplement


