-- Prove2me | Definitions.Def_GnpColoring_IsSeparator
-- name    : GnpColoring_IsSeparator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:34.841525+00:00
-- url     : https://prove2.me/theorems/481dd652-df24-41b7-9f07-cda58991cbd4
-- title:
--   Separator of a tree or unicyclic set (Lemma 5.5)
-- statement:
--   A set $C$ is a **separator** of $T$ if $C\subseteq T$, $G[C]$ is connected, and every connected component $T_i$ of $G[T\setminus C]$ is a tree attached to $C$ by exactly one edge $\{u,w_i\}$ with $u\in C$ and $w_i\in T_i$ low-degree ($\deg_G(w_i)\le\bar\Delta$). These are the properties Lemma 5.5 asserts; its proof builds one from a root (or the cycle) and the hubs reachable from it through hubs.
--
--   **Formalization Note** Lemma 5.5 also says conditioning on $C$ leaves an admissible boundary on each $T_i$; that follows from the listed properties when the boundary on $T$ is admissible.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Lemma 5.5, p.45

import Mathlib
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_IsTreeBlock
import Definitions.Def_GnpColoring_deltaBar

open scoped Classical
open Finset

namespace GnpColoring

/-- **A separator of `T` in the sense of Lemma 5.5**: `C ⊆ T`, `G[C]` is connected, and every
component `T_i` of `G[T ∖ C]` is a tree attached to `C` by exactly one edge `{u, w_i}`, `u ∈ C`,
whose endpoint `w_i ∈ T_i` is low-degree (`deg_G(w_i) ≤ Δ̄`).

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Lemma 5.5, p.45: "There is a connected separator C with the following properties. Enumerate
its vertices as C = {u1, . . . , uk}. Every component Ti of T ∖ C is a tree attached to C by exactly
one edge {u_parC(i), wi} for some index parC(i) ∈ [k], where wi ∈ Ti is low-degree. Conditioning on
any feasible coloring of C leaves an admissible boundary condition on each Ti."

**Formalization Note** The components of `G[T ∖ C]` are the blocks of `V ∖ (T ∖ C)`. The last
property of Lemma 5.5 (admissibility on each `T_i` after conditioning on `C`) follows from the
others when the boundary condition on `T` is admissible: the only new exterior neighbour of `T_i`
is at `w_i`, which is low-degree. -/
def IsSeparator {n : ℕ} (G : SimpleGraph (Fin n)) (d η : ℝ) (T Csep : Finset (Fin n)) : Prop :=
  Csep ⊆ T ∧ (G.induce (Csep : Set (Fin n))).Connected ∧
    ∀ Ti ∈ blocks G (univ \ (T \ Csep)), IsTreeBlock G Ti ∧
      ∃ u ∈ Csep, ∃ w ∈ Ti, G.Adj u w ∧ (G.degree w : ℝ) ≤ deltaBar d η ∧
        ∀ u' ∈ Csep, ∀ w' ∈ Ti, G.Adj u' w' → u' = u ∧ w' = w

end GnpColoring


