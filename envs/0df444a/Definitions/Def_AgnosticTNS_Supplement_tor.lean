-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_tor
-- name    : AgnosticTNS_Supplement_tor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:37:27.56062+00:00
-- url     : https://prove2.me/theorems/2e396f1c-53a2-48b0-b0dd-a5d2b5d53241
-- title:
--   Torso size $\mathrm{tor}(t)$
-- statement:
--   The **torso size** of a node $t$ is $\mathrm{tor}(t)=|V(\tilde H_t)|$, the number of vertices of the 3-centre $\tilde H_t$ of the torso $H_t$, obtained by suppressing peripheral vertices of degree at most $2$ until none is left. Core vertices are never suppressed, so $|X_t|\le\mathrm{tor}(t)$ (Remark 6.7).
--
--   **Formalization Note** $\mathrm{tor}(t)$ is defined as the least vertex count over all terminal results of the suppression process started at $H_t$. The 3-centre is unique in the literature, so this is its size; taking the minimum makes "width at most $k$" the weakest possible reading.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.5, Eq. (6.4), pp.48–49; Remark 6.7, p.49

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_torsoMult
import Definitions.Def_AgnosticTNS_Supplement_SuppressStep

namespace AgnosticTNS.Supplement

/-- **The torso size** `tor(t) = |V(H̃_t)|`, Eq. (6.4), Definition 6.5, pp.48–49 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
the number of vertices of the 3-centre `H̃_t` of the torso `H_t`, obtained by repeatedly suppressing
peripheral vertices of degree at most `2` until none remains.

**Formalization Note** Starting from `H_t` (vertex set `X_t ⊕ {u : u ~ t}`, matrix `torsoMult`), `tor(t)`
is the least vertex count over all terminal results of `SuppressStep` (core = `Sum.inl`). The 3-centre
is unique in the literature, so this is its size; the minimum makes "width at most `k`" the weakest
reading. Every terminal result contains `X_t`, so `|X_t| ≤ tor(t)` (Remark 6.7). -/
noncomputable def tor {n : ℕ} (G : SimpleGraph (Fin n)) (D : TreeCutDecomp n) (t : Fin D.N) : ℕ := by
  classical
  exact sInf {c | ∃ B : Finset (Fin n ⊕ Fin D.N) × (Fin n ⊕ Fin D.N → Fin n ⊕ Fin D.N → ℕ),
    Relation.ReflTransGen (SuppressStep fun a => a.isLeft = true)
      ((D.X t).disjSum (Finset.univ.filter fun u => D.T.Adj t u), torsoMult G D t) B ∧
    (¬ ∃ B', SuppressStep (fun a => a.isLeft = true) B B') ∧ B.1.card = c}

end AgnosticTNS.Supplement


