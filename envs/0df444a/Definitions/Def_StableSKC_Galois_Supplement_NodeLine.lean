-- Prove2me | Definitions.Def_StableSKC_Galois_Supplement_NodeLine
-- name    : StableSKC_Galois_Supplement_NodeLine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:15:38.234955+00:00
-- url     : https://prove2.me/theorems/8beb5f27-1e5d-4862-a28e-9342af3a0130
-- title:
--   §2, p. 6 — the knockout tournament arising from a node-line pair (x, ℓ) of the Fano plane
-- statement:
--   Eight players $0, 1, \dots, 7$ take part. The seven players $1, \dots, 7$ are the nodes of a **Fano plane**: a family of seven 3-element *lines* such that any two distinct nodes lie on exactly one common line. Player $0$ is not a node. Through every node pass exactly three lines.
--
--   A knockout tournament on the eight players is given by its seeding $s = s_0 s_1 \dots s_7$ (leaf position $\mapsto$ player); leaves $2j$ and $2j+1$ meet in round $1$.
--
--   Let $x$ be a node and $\ell$ a line through $x$. A knockout tournament $T$ **arises from the node-line pair $x, \ell$** if
--
--   1. $s_0 = 0$ and $s_1 = x$: player $0$ meets player $x$ in round $1$;
--   2. $\{s_2, s_3\} = \ell \setminus \{x\}$: the players of the two other nodes of $\ell$ meet each other;
--   3. $\bigl\{\{s_4, s_5\}, \{s_6, s_7\}\bigr\} = \bigl\{ m \setminus \{x\} : m \text{ a line through } x,\ m \ne \ell \bigr\}$: the remaining two matches are given by the two non-selected lines through $x$.
--
--   The order within the pairs at leaves 2–3, 4–5 and 6–7 and the order of the two second-half pairs are left free; leaves 0 and 1 are fixed as $0,x$ as in the partial seedings on p. 6; for $x = 1$ and $\ell = \{1,4,5\}$ in Figure 3, both $0145-2376$ (p. 6) and $0145-2367$ (Table 1) arise. These tournaments are the building blocks of the paper's stable serial knockout competition for eight players (Theorem 2.1).
--
--   **Formalization Note** The plane is a Steiner triple system `S : RolesForceSeven.STS 7` (published definition) on nodes `Fin 7`; node `j` is player `j + 1 : Fin 8` (`nodePlayer`), and `nodesToPlayers` maps a set of nodes to the corresponding players. Every Steiner triple system on seven points is the Fano plane up to relabelling. A tournament is the published `Seeding 3 (Fin 8)` of `StableSKC.Galois.Model`. `ArisesFrom S x ℓ T` does not itself require $\ell$ to be a line or $x \in \ell$; the theorems that use it assume both.
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, p. 6, construction of the seeding from a node-line pair (§2), Figure 3 (p. 7), Table 1 (p. 6)

import Mathlib
import Definitions.Def_StableSKC_Galois_Model
import Definitions.Def_RolesForceSeven_sts

namespace StableSKC.Galois.Supplement

open RolesForceSeven

/-- The Fano-plane nodes `0, …, 6` are the players `1, …, 7` of `Fin 8` (node `j` ↦ player
`j + 1`); player `0` is not a node (Lambers–Pendavingh–Spieksma, p. 6, Figure 3). -/
def nodePlayer (y : Fin 7) : Fin 8 := y.succ

/-- A set of nodes, read as a set of players. -/
def nodesToPlayers (m : Finset (Fin 7)) : Finset (Fin 8) := m.map (Fin.succEmb 7)

/-- p. 6: the knockout tournament `T` (a seeding `Fin 8 ≃ Fin 8`, leaf ↦ player) *arises from*
the node-line pair `x, ℓ` of the plane `S`: player `0` meets player `x` in round 1 (leaves 0, 1),
the players of the two other nodes of `ℓ` meet each other (leaves 2, 3), and the remaining two
round-1 matches (leaves 4, 5 and 6, 7) are given by the two lines through `x` other than `ℓ`, the
two other players of each such line meeting each other. The order inside each pair and of the two
second-half pairs is free. -/
def ArisesFrom (S : STS 7) (x : Fin 7) (ℓ : Finset (Fin 7)) (T : Seeding 3 (Fin 8)) : Prop :=
  T 0 = 0 ∧ T 1 = nodePlayer x ∧
  ({T 2, T 3} : Finset (Fin 8)) = nodesToPlayers (ℓ.erase x) ∧
  ({{T 4, T 5}, {T 6, T 7}} : Finset (Finset (Fin 8))) =
    (S.lines.filter fun m => x ∈ m ∧ m ≠ ℓ).image fun m => nodesToPlayers (m.erase x)

end StableSKC.Galois.Supplement


