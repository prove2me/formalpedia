-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
-- name    : ExtensionComplexity_TSP_extensionComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:47:25.730785+00:00
-- url     : https://prove2.me/theorems/dfc2fa97-44fe-45a3-a834-19ed97f2ee55
-- title:
--   Extended formulations of size $r$ and the extension complexity $\mathrm{xc}(P)$
-- statement:
--   Let $\iota$ be a finite index set and $P\subseteq\mathbb R^{\iota}$. An **extended formulation** (EF) of $P$ is a linear system
--
--   $$E^{=}x+F^{=}y=g^{=},\qquad E^{\le}x+F^{\le}y\le g^{\le}\tag{1}$$
--
--   in variables $(x,y)\in\mathbb R^{\iota}\times\mathbb R^{k}$, where $E^{=},F^{=},E^{\le},F^{\le}$ are real matrices with $|\iota|,k,|\iota|,k$ columns and $g^{=},g^{\le}$ are column vectors, such that $x\in P$ if and only if there exists $y$ for which (1) holds. The **size** of an EF is its number of inequalities, i.e. the number of rows of $E^{\le}$; equations are not counted. The **extension complexity** of $P$ is the minimum size of an EF of $P$:
--
--   $$\mathrm{xc}(P)=\min\{r\in\mathbb N : P \text{ has an EF of size } r\}.$$
--
--   Extension complexity measures how compactly a polytope can be written as the projection of a polyhedron; every lower bound in the mission is a lower bound on $\mathrm{xc}$.
--
--   **Formalization Note** `IsEFOfSize P r` asserts an EF with exactly $r$ inequalities, some number $p$ of equations and some number $k\ge 0$ of extra variables. `extensionComplexity P` is the natural number `sInf {r | IsEFOfSize P r}`. Every polytope has an EF, so on polytopes this is a true minimum; it is not valued in $\mathbb N\cup\{\infty\}$, so no lower bound can hold vacuously through an infinite value.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:2, eq. (1); p. 17:3 (size of an EF); p. 17:9, (1) and (3)

import Mathlib

namespace ExtensionComplexity.TSP

open Matrix

/-- **Extended formulation of size `r`** (Fiorini–Massar–Pokutta–Tiwary–de Wolf, J. ACM 62(2) (2015),
Art. 17, p. 17:2, eq. (1); size: p. 17:3; p. 17:9, (1)). A set `P ⊆ ℝ^ι` has an EF of size `r` if there
are `k, p : ℕ` and a linear system
`E^= x + F^= y = g^=`, `E^≤ x + F^≤ y ≤ g^≤` in the variables `(x, y) ∈ ℝ^ι × ℝ^k`, with `p` equations and
exactly `r` inequalities, such that `x ∈ P` if and only if some `y` satisfies the system.
The size of an EF is its number of inequalities; the equations are not counted. The order on
`Fin r → ℝ` is componentwise. -/
def IsEFOfSize {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (r : ℕ) : Prop :=
  ∃ (k p : ℕ) (Eeq : Matrix (Fin p) ι ℝ) (Feq : Matrix (Fin p) (Fin k) ℝ) (geq : Fin p → ℝ)
    (Ele : Matrix (Fin r) ι ℝ) (Fle : Matrix (Fin r) (Fin k) ℝ) (gle : Fin r → ℝ),
    ∀ x : ι → ℝ, x ∈ P ↔
      ∃ y : Fin k → ℝ, Eeq *ᵥ x + Feq *ᵥ y = geq ∧ Ele *ᵥ x + Fle *ᵥ y ≤ gle

/-- **Extension complexity** `xc(P)` (p. 17:9, (3)): the minimum size (number of inequalities) of an
EF of `P`, a natural number. Every polytope has an EF, so for polytopes the infimum is attained;
on a set with no EF at all, `sInf ∅ = 0` (never used: every statement applies it to polytopes). -/
noncomputable def extensionComplexity {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : ℕ :=
  sInf {r : ℕ | IsEFOfSize P r}

end ExtensionComplexity.TSP


