-- Prove2me | Definitions.Def_LysgaardCVRP_Shrink_SafeToShrink
-- name    : LysgaardCVRP_Shrink_SafeToShrink
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:38:55.010627+00:00
-- url     : https://prove2.me/theorems/788ccfb9-7772-4a90-93c5-530ac7a4ba71
-- title:
--   Safe shrinking of a customer set
-- statement:
--   Let $x$ be an edge vector on the complete graph with depot $0$ and customers $V_c = \{1, \dots, n\}$, and let $\rho$ define the inequalities $x(\delta(T)) \ge 2\rho(T)$ for customer sets $T$ with $|T| \ge 2$. **Shrinking** a customer set $S$ replaces it by a single supervertex; the supervertices of the shrunk graph are then $S$ and the single customers outside $S$, so a union of supervertices is a customer set $T'$ with $S \subseteq T'$ or $S \cap T' = \emptyset$.
--
--   Shrinking $S$ is **safe** if, whenever some inequality is violated, one is found among unions of supervertices with at least the same violation: for every customer set $T$ with $|T| \ge 2$ and $2\rho(T) - x(\delta(T)) > 0$ there is a customer set $T'$ with
--
--   1. $|T'| \ge 2$,
--   2. $S \subseteq T'$ or $S \cap T' = \emptyset$,
--   3. $2\rho(T) - x(\delta(T)) \le 2\rho(T') - x(\delta(T'))$.
--
--   Safe shrinking is what allows separation heuristics for capacity inequalities to work on a smaller graph without losing violated inequalities.
--
--   **Formalization Note** Customer sets are finite sets of vertices not containing the depot. The cut of a union of supervertices in the shrunk graph, where the edge $\{s, j\}$ gets weight $x(E(S : \{j\}))$, equals its cut in the original graph, so all cuts are computed in the original graph.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), §2.1, definition of safe shrinking

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_violation

namespace LysgaardCVRP.Shrink

/-- Safe shrinking of a customer set $S$ (Lysgaard, Letchford & Eglese, Math. Program. Ser. A 100
(2004), §2.1, p. 426, PDF p. 4): "we iteratively choose a customer set $S$ and shrink it to a single
supervertex $s$ having demand $q(S)$ [...] the shrinking is *safe*, which means that whenever there is
a violated capacity inequality in $G^*$, there exists a set of supervertices in the shrunk graph whose
union defines a capacity inequality with at least the same violation."

After shrinking $S$ the supervertices are $S$ and the singletons $\{j\}$, $j \notin S$; a union of
supervertices is a customer set $T'$ that contains $S$ or is disjoint from it, and it defines a
capacity inequality when $|T'| \ge 2$. So `SafeToShrink x ρ S` says: for every customer set $T$
with $|T| \ge 2$ whose inequality $x(\delta(T)) \ge 2\rho(T)$ is violated, there is a customer set
$T'$ with $|T'| \ge 2$, $S \subseteq T'$ or $S \cap T' = \emptyset$, whose violation is at least
that of $T$.

**Formalization Note.** Customer sets are `Finset`s of `Fin (n+1)` not containing the depot `0`.
The cut of a union of supervertices in the shrunk graph (edge $\{s, j\}$ weighted
$x(E(S : \{j\}))$) equals its cut in $G^*$, so violations are computed with `cut` in the original
graph. -/
def SafeToShrink {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (ρ : Finset (Fin (n + 1)) → ℕ)
    (S : Finset (Fin (n + 1))) : Prop :=
  ∀ T : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ T → 2 ≤ T.card → 0 < violation x ρ T →
    ∃ T' : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ T' ∧ 2 ≤ T'.card ∧
      (S ⊆ T' ∨ Disjoint S T') ∧ violation x ρ T ≤ violation x ρ T'

end LysgaardCVRP.Shrink


