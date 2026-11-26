-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_JacobsonSpace
-- name    : ProEtale_Mathlib_Topology_JacobsonSpace
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:07.078805+00:00
-- url     : https://prove2.me/theorems/0f74107b-c236-4d93-870b-eb9f6fdefcc7
-- title:
--   Every point of the subspace of closed points is closed in that subspace
-- statement:
--   Let $X$ be a topological space and $\mathrm{cl}(X) \subseteq X$ its set of closed points, with the subspace topology. For every $x \in \mathrm{cl}(X)$, the singleton $\{x\}$ is closed in $\mathrm{cl}(X)$. Equivalently, $\mathrm{cl}(X)$ is a $T_1$ space. This holds because $\{x\}$ is the preimage of the closed set $\{x\} \subseteq X$ under the inclusion.
--
--   This is used when studying the space of closed points of spectral and w-local spaces.
--
--   **Formalization Note** The theorem is `closedPoints.isClosed_singleton`, stated for `x : closedPoints X`, with `closedPoints X` coerced to a subtype. It is placed (per a source comment) before Mathlib's `closedPoints_eq_univ`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/JacobsonSpace.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.JacobsonSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
variable {X : Type*} [TopologicalSpace X]

-- before `closedPoints_eq_univ`
theorem closedPoints.isClosed_singleton (x : closedPoints X) :
    IsClosed ({x} : Set (closedPoints X)) := by
  simpa [Set.preimage, Subtype.val_inj] using
      x.2.preimage (f := fun (x : closedPoints X) ↦ (x : X)) continuous_subtype_val


