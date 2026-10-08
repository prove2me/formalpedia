-- Prove2me | Definitions.Def_ProjLikeRetr_Retractor_IsRetractor
-- name    : ProjLikeRetr_Retractor_IsRetractor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:09:15.152627+00:00
-- url     : https://prove2.me/theorems/1570579d-2bb6-44b7-9967-0dd053dfbf2d
-- title:
--   Definition 4.1, p. 15 — retractor: a C^{k-1} field of (n−d)-planes transverse to T_M(x) at u = 0
-- statement:
--   Let $\mathcal M$ be a $d$-dimensional submanifold of class $C^k$ ($k\ge2$) of an $n$-dimensional Euclidean space $\mathcal E$, and let $\mathrm{Gr}(n-d,\mathcal E)$ be the Grassmann manifold of $(n-d)$-dimensional linear subspaces of $\mathcal E$. A **retractor** on $\mathcal M$ is a mapping $D$ from the tangent bundle $\mathrm T\mathcal M$ into $\mathrm{Gr}(n-d,\mathcal E)$ such that
--
--   1. $D$ is defined and of class $C^{k-1}$ on a neighbourhood of the zero section $\{(x,0):x\in\mathcal M\}$ of $\mathrm T\mathcal M$;
--   2. for all $x\in\mathcal M$, $D(x,0)$ is transverse to $\mathrm T_{\mathcal M}(x)$:
--
--   $$D(x,0)\cap\mathrm T_{\mathcal M}(x)=\{0\}.$$
--
--   Since $\dim D(x,0)=n-d$ and $\dim\mathrm T_{\mathcal M}(x)=d$, transversality means $\mathcal E=D(x,0)\oplus\mathrm T_{\mathcal M}(x)$. A retractor prescribes, for every tangent step $(x,u)$, the directions along which one comes back to $\mathcal M$ from $x+u$; the constant field $D(x,u)=\mathrm N_{\mathcal M}(x)$ (orthographic retractor) and $D(x,u)=\mathrm N_{\mathcal M}(P_{\mathcal M}(x+u))$ (projective retractor) are examples.
--
--   **Formalization Note** $D$ is a total map $\mathcal E\times\mathcal E\to$ {subspaces of $\mathcal E$}; the neighbourhood of the zero section is $O\cap\mathrm T\mathcal M$ with $O$ open and $(x,0)\in O$ for every $x\in\mathcal M$, and on it $\dim D(x,u)=n-d$. Smoothness of a Grassmannian-valued map is encoded through the orthogonal projector: $(x,u)\mapsto P_{D(x,u)}\in L(\mathcal E)$ is $C^{k-1}$ on $O\cap\mathrm T\mathcal M$ (`ContDiffOn` on that set). The map $P\mapsto P_P$ is the standard smooth embedding of $\mathrm{Gr}(n-d,\mathcal E)$ into $L(\mathcal E)$, so this is the page's $C^{k-1}$ condition. $n-d$ is natural-number subtraction; $d\le n$ comes with the submanifold hypothesis.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 15, §4.1 (Grassmann manifold, transversality) and Definition 4.1

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ProjLikeRetr.Retractor

/-- Definition 4.1, p. 15: a retractor on the `d`-dimensional `C^k` submanifold `M` of the
`n`-dimensional Euclidean space `E` is a map `D` from `TM` to the Grassmannian `Gr(n - d, E)`,
defined and of class `C^{k-1}` on a neighbourhood `O ∩ TM` of the zero section of `TM`, such
that `D(x, 0)` is transverse to `T_M(x)` for every `x ∈ M`. A point of `Gr(n - d, E)` is an
`(n - d)`-dimensional subspace; the smooth structure of the Grassmannian is the one carried by
the orthogonal projector onto the subspace, so `C^{k-1}` dependence is `C^{k-1}` dependence of
the projector `P_{D(x,u)} : E →L[ℝ] E`. Transversality of subspaces of dimensions `d` and `n - d`
is trivial intersection. -/
def IsRetractor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (D : E × E → Submodule ℝ E) : Prop :=
  ∃ O : Set (E × E), IsOpen O ∧ (∀ x ∈ M, (x, (0 : E)) ∈ O) ∧
    (∀ p ∈ O ∩ tangentBundle M, Module.finrank ℝ (D p) = Module.finrank ℝ E - d) ∧
    ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun p => (D p).starProjection)
      (O ∩ tangentBundle M) ∧
    ∀ x ∈ M, D (x, 0) ⊓ tangentSpace M x = ⊥

end ProjLikeRetr.Retractor


