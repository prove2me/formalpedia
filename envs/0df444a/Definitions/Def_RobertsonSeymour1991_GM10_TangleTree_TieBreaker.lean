-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TieBreaker
-- name    : RobertsonSeymour1991_GM10_TangleTree_TieBreaker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:46.617169+00:00
-- url     : https://prove2.me/theorems/ac7897d1-a69e-4a52-85c2-5eb2661ef039
-- title:
--   §9–§10, pp. 177–181 — tie-breaker λ, λ-robust separations, distinguishing tangles, (𝒯₁, 𝒯₂)-distinction
-- statement:
--   A **tie-breaker** $\lambda$ in a hypergraph $G$ is a function from the separations of $G$ into a linearly ordered set $(\Lambda,<)$; $\lambda(A,B)$ is the **$\lambda$-order** of $(A,B)$. It must satisfy, for all separations $(A,B)$, $(C,D)$ of $G$:
--
--   1. $(A,B)$ and $(C,D)$ have the same $\lambda$-order if and only if $(A,B)=(C,D)$ or $(A,B)=(D,C)$;
--   2. either $\lambda(A\cup C,B\cap D)\le\lambda(A,B)$ or $\lambda(A\cap C,B\cup D)<\lambda(C,D)$;
--   3. if $(A,B)$ has smaller order than $(C,D)$, then $\lambda(A,B)<\lambda(C,D)$.
--
--   A separation $(A,B)$ is **$\lambda$-robust** if for every separation $(C,D)$ of the hypergraph $A$ (so $C\cup D=A$, $E(C\cap D)=\emptyset$), one of $(C,B\cup D)$, $(D,B\cup C)$ has $\lambda$-order at least $\lambda(A,B)$; it is **doubly $\lambda$-robust** if $(A,B)$ and $(B,A)$ are both $\lambda$-robust.
--
--   For tangles $\mathcal T_1,\mathcal T_2$ in $G$, a separation $(A,B)$ **distinguishes** $\mathcal T_1$ from $\mathcal T_2$ if
--   $$(A,B)\in\mathcal T_1\quad\text{and}\quad(B,A)\in\mathcal T_2,$$
--   and it is a **$(\mathcal T_1,\mathcal T_2)$-distinction** if it has minimum $\lambda$-order among all separations distinguishing $\mathcal T_1$ from $\mathcal T_2$.
--
--   The tie-breaker makes "the" minimum separation between two tangles unique, which is what allows the distinctions of many tangles to be arranged without crossings.
--
--   **Formalization Note** $\lambda$ is a function `G.Sub × G.Sub → Λ` on all pairs of subhypergraphs; every axiom quantifies over separations only, so its values on other pairs are irrelevant. $\Lambda$ is an arbitrary type with a `LinearOrder`. `IsDistinction` asserts the separation is a separation, distinguishes the two tangles, and has $\lambda$-order at most that of every separation distinguishing them.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), pp. 177–178 (tie-breaker and its three axioms), p. 180 (λ-robust, doubly λ-robust, distinguishes), p. 181 ((𝒯₁, 𝒯₂)-distinction)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph

namespace RobertsonSeymour1991.GM10.TangleTree

variable {V E : Type}

namespace Hypergraph

/-- pp. 177–178: `λ` is a tie-breaker in `G`, with values in the linearly ordered set `Λ`.
The three tie-breaker axioms quantify over separations only; values of `λ` on pairs that are
not separations are never used. -/
def IsTieBreaker {Λ : Type} [LinearOrder Λ] (G : Hypergraph V E) (lam : G.Sub × G.Sub → Λ) :
    Prop :=
  (∀ A B C D : G.Sub, IsSeparation A B → IsSeparation C D →
    (lam (A, B) = lam (C, D) ↔ ((A, B) = (C, D) ∨ (A, B) = (D, C)))) ∧
  (∀ A B C D : G.Sub, IsSeparation A B → IsSeparation C D →
    lam (A.union C, B.inter D) ≤ lam (A, B) ∨ lam (A.inter C, B.union D) < lam (C, D)) ∧
  (∀ A B C D : G.Sub, IsSeparation A B → IsSeparation C D →
    order A B < order C D → lam (A, B) < lam (C, D))

/-- p. 180: `(A, B)` is `λ`-robust: for every separation `(C, D)` of the hypergraph `A`
(that is, `C ∪ D = A` and `E(C ∩ D) = ∅`), one of `(C, B ∪ D)`, `(D, B ∪ C)` has `λ`-order at
least that of `(A, B)`. -/
def IsRobust {Λ : Type} [LinearOrder Λ] {G : Hypergraph V E} (lam : G.Sub × G.Sub → Λ)
    (A B : G.Sub) : Prop :=
  ∀ C D : G.Sub, C.union D = A → C.edges ∩ D.edges = ∅ →
    lam (A, B) ≤ lam (C, B.union D) ∨ lam (A, B) ≤ lam (D, B.union C)

/-- p. 180: `(A, B)` is doubly `λ`-robust if both `(A, B)` and `(B, A)` are `λ`-robust. -/
def IsDoublyRobust {Λ : Type} [LinearOrder Λ] {G : Hypergraph V E} (lam : G.Sub × G.Sub → Λ)
    (A B : G.Sub) : Prop :=
  IsRobust lam A B ∧ IsRobust lam B A

/-- p. 180: the separation `(A, B)` distinguishes `𝒯₁` from `𝒯₂`: `(A, B) ∈ 𝒯₁` and
`(B, A) ∈ 𝒯₂`. -/
def Distinguishes {G : Hypergraph V E} (𝒯₁ 𝒯₂ : Set (G.Sub × G.Sub)) (A B : G.Sub) : Prop :=
  (A, B) ∈ 𝒯₁ ∧ (B, A) ∈ 𝒯₂

/-- p. 181: `(A, B)` is a `(𝒯₁, 𝒯₂)`-distinction: a separation distinguishing `𝒯₁` from `𝒯₂`
of minimum `λ`-order among all separations distinguishing `𝒯₁` from `𝒯₂`. -/
def IsDistinction {Λ : Type} [LinearOrder Λ] {G : Hypergraph V E} (lam : G.Sub × G.Sub → Λ)
    (𝒯₁ 𝒯₂ : Set (G.Sub × G.Sub)) (A B : G.Sub) : Prop :=
  IsSeparation A B ∧ Distinguishes 𝒯₁ 𝒯₂ A B ∧
    ∀ C D : G.Sub, IsSeparation C D → Distinguishes 𝒯₁ 𝒯₂ C D → lam (A, B) ≤ lam (C, D)

end Hypergraph

end RobertsonSeymour1991.GM10.TangleTree


