-- Prove2me | Definitions.Def_ValiantModel_Supplement_OnePointClosure
-- name    : ValiantModel_Supplement_OnePointClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:22:07.855038+00:00
-- url     : https://prove2.me/theorems/b2dd527f-1f4c-409e-96c6-068f0f464c1b
-- title:
--   The 1-point closure class $\mathrm{Cl}_1(H)$ over a general domain
-- statement:
--   Let $H\subseteq\{0,1\}^X$. For a non-empty subfamily $G\subseteq H$ let $\mathrm{Closure}(G):=\bigcap_{h\in G}\mathrm{supp}(h)$, and for a point $p\in X$ let $V(p,H):=\{h\in H:\ p\in\mathrm{supp}(h)\}$. The **1-point closure class** is
--   $$\mathrm{Cl}_1(H):=\{\mathrm{Closure}(V(p,H))\;:\;p\in X\},$$
--   each set identified with its indicator function.
--
--   Theorem A.11 uses it to show that on an infinite domain the closure class can have much larger VC dimension than the class itself.
--
--   **Formalization Note** $\mathrm{Closure}$ is defined on the page only for non-empty families, so a point $p$ with $V(p,H)=\emptyset$ contributes no member. The published `ValiantModel.ClosureClass` is for $\{0,1\}^d$ only and is not reused.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), §A.3 and Theorem A.11, p.54 (PDF p.56)

import Mathlib

namespace ValiantModel.Supplement

/-- The **1-point closure class** `Cl₁(H) = {Closure(V(p, H)) : p ∈ X}` of Theorem A.11, Hanneke,
Mehrotra, Velegkas, Zampetakis, arXiv:2605.13840 (version held, sha256 f793f255…), p.54 (PDF p.56),
over a general domain: for `p ∈ X`, `V(p, H) = {h ∈ H : p ∈ supp(h)}` and, for non-empty `G ⊆ H`,
`Closure(G) = ⋂_{h ∈ G} supp(h)`, represented by its indicator.

**Formalization Note.** `Closure` is defined on the page only for non-empty families, so a point `p`
with `V(p, H) = ∅` contributes no member. The published `ValiantModel.ClosureClass` is for `{0,1}^d`
only and is not reused. -/
def onePointClosureClass {X : Type} (H : Set (X → Bool)) : Set (X → Bool) :=
  {g | ∃ p : X, (∃ h ∈ H, h p = true) ∧ ∀ x, g x = true ↔ ∀ h ∈ H, h p = true → h x = true}

end ValiantModel.Supplement


