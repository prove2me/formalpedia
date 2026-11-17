-- Prove2me | Definitions.Def_ValiantModel_Supplement_Halfspaces
-- name    : ValiantModel_Supplement_Halfspaces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:22:31.435024+00:00
-- url     : https://prove2.me/theorems/41b81299-213d-4d3d-8529-4f61b37b2f33
-- title:
--   Halfspaces in $\mathbb R^d$ and intersections of $s$ halfspaces
-- statement:
--   A (closed) **halfspace** of $\mathbb R^d$ is a set $\{x\in\mathbb R^d:\ \langle n,x\rangle\ge c\}$ with a normal vector $n\neq0$ and $c\in\mathbb R$. The class of halfspaces of Theorem 1.6 consists of their indicator functions.
--
--   For $s\ge1$, the class of **intersections of $s$ halfspaces** of Theorem A.1 consists of the indicators of $P=H_1\cap\cdots\cap H_s$, each $H_t$ a halfspace. Repetitions among the $H_t$ are allowed, so intersections of fewer halfspaces are included.
--
--   **Formalization Note** The published `VanderbeiLP.StrictComp.IsHalfspace` ($\{x: a\cdot x\le\beta\}$, $a\ne0$) is reused. Since $\{\langle n,x\rangle\ge c\}=\{\langle -n,x\rangle\le -c\}$, the two families coincide. $\mathbb R^d$ is `Fin d → ℝ` with the dot product.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Theorem 1.6, p.6 (PDF p.8); §5.5, p.38 (PDF p.40); Definition 16, p.42 (PDF p.44); Theorem A.1, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_Polyhedron

namespace ValiantModel.Supplement

/-- The class of **halfspaces in `ℝ^d`** of Theorem 1.6, Hanneke, Mehrotra, Velegkas, Zampetakis,
arXiv:2605.13840 (version held, sha256 f793f255…), p.6 (PDF p.8), as set on p.38 (PDF p.40): the
indicators of closed halfspaces `{x : ⟨n, x⟩ ≥ c}` with normal vector `n ≠ 0`.

**Formalization Note.** Reuses the published `VanderbeiLP.StrictComp.IsHalfspace`
(`{x : a ⬝ᵥ x ≤ β}`, `a ≠ 0`); `{⟨n, x⟩ ≥ c} = {⟨-n, x⟩ ≤ -c}`, so the two families coincide. `ℝ^d`
is `Fin d → ℝ` with the dot product (the Euclidean inner product) and its Borel σ-algebra. -/
def halfspaceClass (d : ℕ) : Set ((Fin d → ℝ) → Bool) :=
  {g | VanderbeiLP.StrictComp.IsHalfspace {x | g x = true}}

/-- The class of **intersections of `s` halfspaces in `ℝ^d`** of Theorem A.1, arXiv:2605.13840
(version held), p.50 (PDF p.52): indicators of `H₁ ∩ ⋯ ∩ H_s`, each `H_t` a closed halfspace with
non-zero normal; repetitions are allowed (p.50), so intersections of fewer halfspaces are included. -/
def halfspaceIntersections (d s : ℕ) : Set ((Fin d → ℝ) → Bool) :=
  {g | ∃ P : Fin s → Set (Fin d → ℝ), (∀ t, VanderbeiLP.StrictComp.IsHalfspace (P t)) ∧
    {x | g x = true} = ⋂ t, P t}

end ValiantModel.Supplement


