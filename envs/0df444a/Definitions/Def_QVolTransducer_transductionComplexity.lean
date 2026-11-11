-- Prove2me | Definitions.Def_QVolTransducer_transductionComplexity
-- name    : QVolTransducer_transductionComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:53.953089+00:00
-- url     : https://prove2.me/theorems/4cc2f1cb-28f2-430d-9e94-7eebb6cecd0b
-- title:
--   Transducers, transduction $\lvert\sigma\rangle\overset{U}{\rightsquigarrow}\lvert\tau\rangle$ and transduction complexity $W(U,\lvert\sigma\rangle)$
-- statement:
--   A **transducer** is a unitary $U$ on $\mathcal V\oplus\mathcal H$, with **public space** $\mathcal V$ and **private space** $\mathcal H$. If for a state $|\sigma\rangle\in\mathcal V$ and a **catalyst** $|w\rangle\in\mathcal H$ we have
--
--   $$
--   U\bigl(|\sigma\rangle\oplus|w\rangle\bigr)=|\tau\rangle\oplus|w\rangle ,
--   $$
--
--   we write $|\sigma\rangle\overset{U}{\rightsquigarrow}|\tau\rangle$. The **transduction complexity** is the least squared norm of such a catalyst,
--
--   $$
--   W(U,|\sigma\rangle):=\min\bigl\{\||w\rangle\|^2 : |w\rangle\in\mathcal H,\ |\sigma\rangle\oplus|w\rangle\overset{U}{\mapsto}|\tau\rangle\oplus|w\rangle\bigr\}.
--   $$
--
--   The module also provides the direct sum $|\sigma\rangle\oplus|w\rangle$, the canonical embeddings of a summand into $\mathcal A\oplus\mathcal B$, the predicate "$|\sigma\rangle\rightsquigarrow|\tau\rangle$ with a given catalyst", and the predicate "$|\sigma\rangle\rightsquigarrow|\tau\rangle$ with complexity at most $b$", i.e. some catalyst of squared norm at most $b$ works.
--
--   Transducers are the idealized algorithms of Belovs, Jeffery and Yolcu; every complexity statement of the mission is a bound on $W$.
--
--   **Formalization Note** All spaces are coordinate spaces $\mathbb C^V$ over finite index types, the finite-dimensional setting of Theorem 2.8, where the target $|\tau\rangle$ is unique and the minimum is attained. The minimum is written as the infimum of the set of squared catalyst norms; in finite dimension this set is nonempty, so the value is the paper's minimum, and "with complexity at most $b$" is equivalent to the transduction together with $W(U,|\sigma\rangle)\le b$.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definition 2.7, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QVolTransducer

open QAlgorithms

/-- The direct sum `|σ⟩ ⊕ |w⟩` of a vector of the public space `ℂ^V` and a vector of the private
space `ℂ^H`, as a vector of `ℂ^(V ⊕ H)` (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Definition 2.7, p.13). -/
noncomputable def pubCat {V H : Type*} (σ : EuclideanSpace ℂ V) (w : EuclideanSpace ℂ H) :
    EuclideanSpace ℂ (V ⊕ H) :=
  WithLp.toLp 2 (Sum.elim (fun i => σ i) (fun j => w j))

/-- The embedding `|σ⟩ ↦ |σ⟩ ⊕ 0` of `ℂ^A` into `ℂ^(A ⊕ B)` (the canonical embedding of a summand,
arXiv:2609.40217, p.14: "we take V := V_I ⊕ V_O, and embed |σ_x⟩ and |τ_x⟩ into V in the canonical
way"). -/
noncomputable def embL {A B : Type*} (σ : EuclideanSpace ℂ A) : EuclideanSpace ℂ (A ⊕ B) :=
  WithLp.toLp 2 (Sum.elim (fun i => σ i) (fun _ => 0))

/-- The embedding `|τ⟩ ↦ 0 ⊕ |τ⟩` of `ℂ^B` into `ℂ^(A ⊕ B)` (arXiv:2609.40217, p.14). -/
noncomputable def embR {A B : Type*} (τ : EuclideanSpace ℂ B) : EuclideanSpace ℂ (A ⊕ B) :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun j => τ j))

/-- Transduction with a given catalyst (arXiv:2609.40217, Definition 2.7, p.13: "If for a state
|σ⟩ ∈ V and |w⟩ ∈ H, we have U(|σ⟩ ⊕ |w⟩) = |τ⟩ ⊕ |w⟩, then we write |σ⟩ ⇝_U |τ⟩"). The
transducer is the operator `U` on `ℂ^(V ⊕ H)`, with public space `ℂ^V` and private space `ℂ^H`;
`TransducesWith U σ τ w` says `U (|σ⟩ ⊕ |w⟩) = |τ⟩ ⊕ |w⟩`.

**Formalization Note** All spaces are finite-dimensional coordinate spaces `ℂ^V` over finite index
types, the setting of Theorem 2.8 and of Part II of the paper (p.36). -/
def TransducesWith {V H : Type*} [Fintype V] [Fintype H] (U : Matrix (V ⊕ H) (V ⊕ H) ℂ)
    (σ τ : EuclideanSpace ℂ V) (w : EuclideanSpace ℂ H) : Prop :=
  act U (pubCat σ w) = pubCat τ w

/-- `|σ⟩ ⇝_U |τ⟩`: some catalyst `|w⟩` of the private space satisfies
`U(|σ⟩ ⊕ |w⟩) = |τ⟩ ⊕ |w⟩` (arXiv:2609.40217, Definition 2.7, p.13). -/
def Transduces {V H : Type*} [Fintype V] [Fintype H] (U : Matrix (V ⊕ H) (V ⊕ H) ℂ)
    (σ τ : EuclideanSpace ℂ V) : Prop :=
  ∃ w, TransducesWith U σ τ w

/-- `|σ⟩ ⇝_U |τ⟩` with complexity at most `b`: some catalyst `|w⟩` with `‖w‖² ≤ b` satisfies
`U(|σ⟩ ⊕ |w⟩) = |τ⟩ ⊕ |w⟩` (arXiv:2609.40217, Definition 2.7, p.13). In finite dimension the
minimum defining `W(U, |σ⟩)` is attained (Theorem 2.8), so this is the same as
`|σ⟩ ⇝_U |τ⟩` together with `W(U, |σ⟩) ≤ b`. -/
def TransducesWithin {V H : Type*} [Fintype V] [Fintype H] (U : Matrix (V ⊕ H) (V ⊕ H) ℂ)
    (σ τ : EuclideanSpace ℂ V) (b : ℝ) : Prop :=
  ∃ w, TransducesWith U σ τ w ∧ ‖w‖ ^ 2 ≤ b

/-- The transduction complexity (arXiv:2609.40217, Definition 2.7, p.13):
`W(U, |σ⟩) := min{‖|w⟩‖² : |w⟩ ∈ H, |σ⟩ ⊕ |w⟩ ↦_U |τ⟩ ⊕ |w⟩}`, the least squared norm of a
catalyst with which `U` transduces `|σ⟩` (to its unique target `|τ⟩`, Theorem 2.8).

**Formalization Note** The minimum is written as the infimum of the set of squared catalyst norms.
In finite dimension this set is nonempty and the infimum is attained (Theorem 2.8, p.13), so the
value is the paper's minimum. -/
noncomputable def transductionComplexity {V H : Type*} [Fintype V] [Fintype H]
    (U : Matrix (V ⊕ H) (V ⊕ H) ℂ) (σ : EuclideanSpace ℂ V) : ℝ :=
  sInf {c : ℝ | ∃ (τ : EuclideanSpace ℂ V) (w : EuclideanSpace ℂ H),
    TransducesWith U σ τ w ∧ c = ‖w‖ ^ 2}

end QVolTransducer


