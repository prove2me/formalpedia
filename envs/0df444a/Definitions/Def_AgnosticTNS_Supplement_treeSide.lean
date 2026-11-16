-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_treeSide
-- name    : AgnosticTNS_Supplement_treeSide
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:35:35.561214+00:00
-- url     : https://prove2.me/theorems/9415dd99-f829-458c-aacb-0b9a337dc1b0
-- title:
--   One side of a tree edge
-- statement:
--   For adjacent nodes $t,t'$ of a tree $T$, deleting the edge $\{t,t'\}$ (or the node $t$) leaves a component containing $t'$; this definition returns its node set, the nodes $s$ whose path to $t$ passes through $t'$. It is used for the components in the torso (Definition 6.5) and for the cuts induced by tree edges (Lemma 6.13, Theorem 6.14).
--
--   **Formalization Note** In a tree, $s$ is on the $t'$-side iff $\mathrm{dist}(t,s)=\mathrm{dist}(t',s)+1$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definitions 6.4–6.5, p.48; Lemma 6.13, p.55; Theorem 6.14, p.56

import Mathlib

namespace AgnosticTNS.Supplement

/-- **One side of a tree edge**, used in Definitions 6.4–6.5 (p.48) and Lemma 6.13 / Theorem 6.14
(pp.55–56) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): for adjacent nodes `t, t'` of a tree, the vertex set of
the component of `T − {t, t'}` (equivalently of `T − t`) containing `t'`: the nodes `s` whose path to
`t` passes through `t'`.

**Formalization Note** In a tree, `s` lies on the `t'`-side iff `dist(t, s) = dist(t', s) + 1`. -/
noncomputable def treeSide {N : ℕ} (T : SimpleGraph (Fin N)) (t t' : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun s => T.dist t s = T.dist t' s + 1

end AgnosticTNS.Supplement


