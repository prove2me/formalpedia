-- Prove2me | Definitions.Def_DerandLDT_linesAlong
-- name    : DerandLDT_linesAlong
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:48.715879+00:00
-- url     : https://prove2.me/theorems/9133c083-1586-4f9b-b1d8-802824c57abd
-- title:
--   Lines of $\mathbb F^2$ along a set of directions $U$
-- statement:
--   Let $\mathbb F$ be a finite field. A **direction** in $\mathbb F^2$ is a one-dimensional linear subspace $\Delta \subseteq \mathbb F^2$ (equivalently, a nonzero vector up to scalar multiples). An affine line $L \subseteq \mathbb F^2$ is **along** $\Delta$ when its direction space $\{x - y : x, y \in L\}$ spans $\Delta$, i.e. $L = a + \Delta$ for a point $a$.
--
--   For a finite set $U$ of directions, the set of **lines along $U$** is
--   $$
--   \mathcal L(U) = \{ L \subseteq \mathbb F^2 \text{ an affine line} : \text{the direction of } L \text{ lies in } U \} = L_1 \cup \dots \cup L_r ,
--   $$
--   where $L_i$ is the set of the $q = |\mathbb F|$ parallel lines in the direction $u_i$. When $U$ consists of $r$ distinct directions, $|\mathcal L(U)| = rq$.
--
--   This is the line set of the derandomized line-point test: the test picks a uniformly random line of $\mathcal L(U)$ instead of a random line of $\mathbb F^2$.
--
--   **Formalization Note** Lines are the published `LineVsPoint.Line F 2` (point sets). Directions are submodules of `Fin 2 → F`; the definition accepts any finite set of submodules, and the theorems assume that each has dimension one.
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Theorem 1.2, p.5 ("the set of all lines along these r directions (i.e., |𝓛| = rq)") and Setup of Section 6, p.24

import Definitions.Def_LineVsPoint_AffFlat

set_option autoImplicit false

namespace DerandLDT

open Classical in
/-- **The lines along a set of directions** `𝓛 = L₁ ∪ ⋯ ∪ L_r`: Harsha, Kopparty, Kumar,
Saptharishi, Sudan, *On derandomizing the line-point low-degree test*, STOC 2027 submission
manuscript (sha256 d57e7d6f…80df), Theorem 1.2, p.5 ("let `𝓛` be the set of all lines along these
`r` directions (i.e., `|𝓛| = rq`)") and the Setup of Section 6, p.24 ("`Lᵢ` is the set of all
lines in the direction `uᵢ` in `F²`").

**Formalization Note.** A direction is a one-dimensional subspace of `F²` (a submodule of
`Fin 2 → F` of `finrank` one), so two proportional nonzero vectors are one direction, as in the
Setup ("`uᵢ` and `uⱼ` are not scalar multiples of each other"). A line (`LineVsPoint.Line F 2`,
a point set) is along the direction `Δ` when its direction space `vectorSpan F L` is `Δ`. The
definition takes any finite set `U` of submodules; that its members are one-dimensional is a
hypothesis of the theorems that use it. -/
noncomputable def linesAlong {F : Type*} [Field F] [Fintype F]
    (U : Finset (Submodule F (Fin 2 → F))) : Finset (LineVsPoint.Line F 2) :=
  Finset.univ.filter fun L => vectorSpan F L.carrier ∈ U

end DerandLDT


