-- Prove2me | Definitions.Def_MonDepMW_Supplement_Translinear
-- name    : MonDepMW_Supplement_Translinear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:32:23.729202+00:00
-- url     : https://prove2.me/theorems/00469970-9e90-4c9d-a178-b0c57181fc25
-- title:
--   Translinear graph classes (Definition 9.1)
-- statement:
--   Let $\mathcal C$ be a graph class. Recall that a class $\mathcal D$ is **transducible** from $\mathcal C$ if there are $k$ and a first-order formula $\varphi(x,y)$ over $k$-colored graphs such that every $H\in\mathcal D$ is an induced subgraph of $\varphi(G^+)$ for some $k$-coloring $G^+$ of some $G\in\mathcal C$, and that a partition selector $\mathcal P$ has **growth ratio at most $\gamma$** on a graph $H$ if $|\mathcal P(H,A)|\le\gamma\cdot|A|$ for every non-empty $A\subseteq V(H)$; here $\mathcal T_1(H,A)$ is the partition of $V(H)$ into 1-types over $A$.
--
--   The class $\mathcal C$ is **translinear** if every class $\mathcal D$ transducible from $\mathcal C$ has linear neighborhood complexity: there is a constant $\gamma_{\mathcal D}$ such that, for every $H\in\mathcal D$ and every non-empty $A\subseteq V(H)$,
--
--   $$|\mathcal T_1(H,A)|\le\gamma_{\mathcal D}\cdot|A|.$$
--
--   Classes of bounded merge-width are translinear; the notion is the hypothesis of Theorem 9.2, which gives merge sequences of polylogarithmic width.
--
--   **Formalization Note** Transductions, graph classes (members on each vertex set $\{0,\dots,m-1\}$) and the growth ratio are the mission's published definitions; $\mathcal T_1$ is the selector of $1$-types. The constant $\gamma_{\mathcal D}$ is chosen after $\mathcal D$ and is uniform over the members of $\mathcal D$.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b06082b6e92c2408f95cd60971cd454258095371878ae2f448416bdfeb60b), Definition 9.1, p.34 (PDF p.36); transductions p.12 (PDF 14); Definition 5.4 p.19 (PDF 21)

import Mathlib
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_PartitionSelector

set_option autoImplicit false

namespace MonDepMW.Supplement

/-- **Definition 9.1 (translinear classes).** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph
Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §9, p.34 (PDF p.36):
"A graph class C is translinear if every graph class D transducible from C has linear neighborhood complexity: There is
a constant γ_D such that T1 has growth ratio at most γ_D on every H ∈ D."

**Formalization Note.** "`𝒟` transducible from `𝒞`" is the published `MonDepMW.Transduces 𝒞 𝒟` (Definition of
transductions, p.12); "`𝒯₁` has growth ratio at most `γ_𝒟` on `H`" is `(rTypeSelector 1).GrowthLE H γ_𝒟`
(Definition 5.4, p.19), and `rTypeSelector 1` is the selector `A ↦ 𝒯₁(H, A)` of 1-types (`rType H A 1 = oneType H A`).
The constant `γ_𝒟` is chosen after `𝒟` and is uniform over the members of `𝒟`. Graph classes are
`MonDepMW.GraphClass` (members on each `Fin m`). -/
def Translinear (𝒞 : GraphClass) : Prop :=
  ∀ 𝒟 : GraphClass, Transduces 𝒞 𝒟 →
    ∃ γ : ℕ, ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ∈ 𝒟 m → (rTypeSelector 1).GrowthLE H γ

end MonDepMW.Supplement


