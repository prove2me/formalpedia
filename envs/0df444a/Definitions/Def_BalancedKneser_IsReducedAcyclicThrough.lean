-- Prove2me | Definitions.Def_BalancedKneser_IsReducedAcyclicThrough
-- name    : BalancedKneser_IsReducedAcyclicThrough
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:44.016222+00:00
-- url     : https://prove2.me/theorems/8f5384ea-e20b-49b7-985d-2ecd963a7c56
-- title:
--   Vanishing of reduced homology $\tilde H_j(X;R)$ for $0\le j\le d$
-- statement:
--   Let $X$ be a topological space, $R$ a ring and $d\ge 0$. We say that **$\tilde H_j(X;R)=0$ for $0\le j\le d$** when
--
--   1. $X$ is path-connected (in particular nonempty), which for a nonempty space is $\tilde H_0(X;R)=0$; and
--   2. $H_j(X;R)=0$ for $1\le j\le d$ (reduced and ordinary homology agree in positive degrees).
--
--   Homology is singular homology with coefficients in $R$. Applied to the realization $|K|$ of a simplicial complex, this is the vanishing of the reduced simplicial homology $\tilde H_j(K;R)$ through degree $d$ used in Propositions B.5, C.8 and Theorem 11.1.
--
--   **Formalization Note** Homology is `Hatcher.Singular.H R j X` (the platform definition `Hatcher_SingularHomology`, Mathlib's singular homology with coefficients in $R$). Nonemptiness is built in through path-connectedness; the complexes the mission applies this to are nonempty.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §3.1, p.5 (PDF p.7): reduced homology and H̃₀; §11, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_Hatcher_SingularHomology

namespace BalancedKneser

/-- **Vanishing of reduced homology through degree `d`** (Alipour–Jafari, arXiv:2611.04486v1,
§3.1, p.5 (PDF p.7) and §11, p.27 (PDF p.29)): `H̃_j(X; R) = 0` for `0 ≤ j ≤ d`. Reduced and
ordinary homology agree in positive degrees, and for a nonempty space `H̃_0 = 0` means that the
space is (path-)connected. So the predicate is: `X` is path-connected (in particular nonempty),
and the singular homology `H_j(X; R)` vanishes for `1 ≤ j ≤ d`.

Formalization Note: homology is singular homology with coefficients in the ring `R`
(`Hatcher.Singular.H`). For a simplicial complex `K` it is applied to the realization `|K|`; the
source's simplicial homology of `K` agrees with it. Nonemptiness is built in; every complex the
mission applies this to is nonempty. -/
def IsReducedAcyclicThrough (R : Type) [Ring R] (X : Type) [TopologicalSpace X] (d : ℕ) : Prop :=
  PathConnectedSpace X ∧ ∀ j, 1 ≤ j → j ≤ d → Subsingleton (Hatcher.Singular.H R j X)

end BalancedKneser


