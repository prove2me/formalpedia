-- Prove2me | Definitions.Def_StrongConvPuderCore
-- name    : StrongConvPuderCore
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:36:42.711053+00:00
-- url     : https://prove2.me/theorems/1ebd4387-42b0-4835-8c50-9e871d4d0621
-- title:
--   Edges of the core graph Γ_X(J) of a subgroup J ≤ F_d, and words tracing each of them twice (Puder §3.2, Lemma 4.1)
-- statement:
--   Definitions for a subgroup $J$ of the free group $\mathbf F_d$ (`FreeGroup (Fin d)`) with basis $X = \{g_1, \dots, g_d\}$. The Schreier coset graph of $J$ has the right cosets $Jg$ as vertices and, for each coset $Jg$ and each generator $x$, an $x$-labelled edge from $Jg$ to $Jgx$. Here that edge is named by the pair $(g, x)$; the pairs $(g, x)$ and $(g', x)$ name the same edge when $Jg = Jg'$, that is, when $g g'^{-1} \in J$.
--
--   - `Puder.Traverses J w i g x`: write the reduced word of $w$ as $p\,a\,s$, where $p$ has length $i$ and $a$ is the letter $x$ or $x^{-1}$. Read as a walk from the vertex $J$, its $i$-th step (counting from $0$) crosses the $x$-labelled edge leaving $Jg$. If $a = x$, the walk is at $Jp = Jg$ and crosses it forwards. If $a = x^{-1}$, the walk is at $Jp = Jgx$ and crosses it backwards.
--   - `Puder.IsCoreEdge J g x`: the $x$-labelled edge leaving $Jg$ is an edge of the core graph $\Gamma_X(J)$, that is, the reduced word of some element of $J$ crosses it. The reduced closed walks at the basepoint of the Schreier graph are exactly the reduced words of the elements of $J$.
--   - `Puder.TracesEachCoreEdgeTwice J w`: the walk of the reduced word of $w$ crosses every edge of $\Gamma_X(J)$ at least twice, counting both directions together.
--
--   Puder, p. 12: “To understand how $\Gamma_X(H)$ is constructed, recall first the notion of the Schreier (right) coset graph of $H$ with respect to the basis $X$, denoted by $\overline\Gamma_X(H)$. This is a directed, pointed and edge-labeled graph. Its vertex set is the set of all right cosets of $H$ in $\mathbf F_k$, where the basepoint corresponds to the trivial coset $H$. For every coset $Hw$ and every basis-element $x_j$ there is a directed $j$-edge (short for $x_j$-edge) going from the vertex $Hw$ to the vertex $Hwx_j$.” and “The core graph $\Gamma_X(H)$ is obtained from $\overline\Gamma_X(H)$ by omitting all the vertices and edges of $\overline\Gamma_X(H)$ which are not traced by any reduced (i.e., non-backtracking) walk that starts and ends at the basepoint.” Lemma 4.1 (p. 14) speaks of “the closed walk in $\Gamma_X(N)$ corresponding to $w$” and says that it “traces every edge at least twice”.
--
--   *Formalization note.* The core graph is not built as a graph object. Only its edge set (`Puder.IsCoreEdge`) and the walk of a word through it (`Puder.Traverses`) are defined, which is all Lemma 4.1 and the count in the proof of Proposition 4.3 use. The walk of $w$ is the walk of its reduced word, starting at the basepoint $J$. For $w \in J$ it is Puder's closed walk corresponding to $w$.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, §3.2, pp. 12–13, and Lemma 4.1, p. 14).
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), pp. 12–14, §3.2 and Lemma 4.1, edges of the core graph and the walk of a word in it

import Mathlib

/-!
# Edges of the core graph `Γ_X(J)` and the walks of words in it (Puder)

Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015),
§3.2 and Lemma 4.1 (arXiv:1212.5216, pp. 12–14). The Schreier coset graph of `J ≤ F_d` has
the right cosets `J g` as vertices and an `x`-labelled edge from `J g` to `J g x` for each
generator `x`; it is recorded here by the pair `(g, x)`, two pairs `(g, x)`, `(g', x)` naming
the same edge when `g * g'⁻¹ ∈ J`.
-/

namespace Puder

/-- The `i`-th letter of the reduced word of `w` (counting from `0`), read as a step of the walk
from the coset `J` in the Schreier coset graph of `J`, traverses the `x`-labelled edge leaving
the coset `J g`: either the letter is `x` and the walk is at `J g`, or the letter is `x⁻¹` and
the walk is at `J g x`. -/
def Traverses {d : ℕ} (J : Subgroup (FreeGroup (Fin d))) (w : FreeGroup (Fin d)) (i : ℕ)
    (g : FreeGroup (Fin d)) (x : Fin d) : Prop :=
  ∃ (p s : List (Fin d × Bool)) (b : Bool), w.toWord = p ++ (x, b) :: s ∧ p.length = i ∧
    (if b then FreeGroup.mk p else FreeGroup.mk p * (FreeGroup.of x)⁻¹) * g⁻¹ ∈ J

/-- The `x`-labelled edge leaving the coset `J g` is an edge of the core graph `Γ_X(J)`: some
reduced closed walk at the coset `J`, that is, the reduced word of some element of `J`,
traverses it. -/
def IsCoreEdge {d : ℕ} (J : Subgroup (FreeGroup (Fin d))) (g : FreeGroup (Fin d)) (x : Fin d) :
    Prop :=
  ∃ h ∈ J, ∃ i : ℕ, Traverses J h i g x

/-- The walk of the reduced word of `w` traverses every edge of the core graph `Γ_X(J)` at least
twice. -/
def TracesEachCoreEdgeTwice {d : ℕ} (J : Subgroup (FreeGroup (Fin d))) (w : FreeGroup (Fin d)) :
    Prop :=
  ∀ (g : FreeGroup (Fin d)) (x : Fin d), IsCoreEdge J g x →
    2 ≤ {i : ℕ | Traverses J w i g x}.ncard

end Puder


