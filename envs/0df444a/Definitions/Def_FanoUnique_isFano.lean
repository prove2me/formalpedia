-- Prove2me | Definitions.Def_FanoUnique_isFano
-- name    : FanoUnique_isFano
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-24T19:20:53.710151+00:00
-- url     : https://prove2.me/theorems/d7c0d00a-736b-49ea-957a-30c2117238f4
-- title:
--   $S$ is the Fano plane up to relabelling
-- statement:
--   Let $S$ be a Steiner triple system on the points $\{0, \dots, n-1\}$. $S$ **is the Fano plane up to relabelling** if there is a bijection $e$ from its points to $\{0, \dots, 6\}$ that carries its lines exactly onto the lines of the Fano plane:
--
--   $$
--   \{\, e(\ell) : \ell \text{ a line of } S \,\} = \bigl\{\{i,\ i+1,\ i+3\} : i \in \mathbb{Z}/7\bigr\},
--   $$
--
--   where $e(\ell) = \{e(x) : x \in \ell\}$. This forces $n = 7$ and exactly seven lines.
--
--   **Formalization Note** `IsFano S` is `∃ e : Fin n ≃ Fin 7, S.lines.image (fun l => l.map e.toEmbedding) = fano.lines`. `STS` and `fano` are the published definitions of the companion mission *The role postulates force exactly seven points*, imported unchanged.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3, Theorem 3.3 ("hence the unique STS(7) (the Fano plane PG(2, 2))"); Fano lines as in the Prove2Me definition RolesForceSeven.fano: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; public references: Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Steiner system": https://en.wikipedia.org/wiki/Steiner_system

import Mathlib
import Definitions.Def_RolesForceSeven_fano

namespace FanoUnique

open RolesForceSeven

/-- S is the Fano plane up to relabelling: a bijection of points carries S's
lines exactly onto the Fano plane's lines. -/
def IsFano {n : ℕ} (S : STS n) : Prop :=
  ∃ e : Fin n ≃ Fin 7,
    S.lines.image (fun l => l.map e.toEmbedding) = fano.lines

end FanoUnique


