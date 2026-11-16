-- Prove2me | Definitions.Def_SemAC02_Supplement_ResXor
-- name    : SemAC02_Supplement_ResXor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:41:37.318848+00:00
-- url     : https://prove2.me/theorems/4db1e94b-4875-46a5-9914-1600cc9c8457
-- title:
--   Semantic resolution over parities Res(⊕)
-- statement:
--   A **linear clause** over $\mathbb F_2$ is a disjunction $(\ell_1=b_1)\vee\dots\vee(\ell_w=b_w)$ of linear equations, $\ell_i=\sum_j a_{i,j}x_j$, $b_i\in\mathbb F_2$; the literals $x_i$ and $\neg x_i$ are the equations $x_i=1$ and $x_i=0$. An **arity-2 semantic Res(⊕) refutation** of a CNF $\varphi$ is a sequence of linear clauses in which every line is an axiom clause of $\varphi$ or a semantic consequence $C\wedge D\models E$ of two earlier lines (with $C=D$ allowed, which covers weakening), ending with the empty clause. Lines may be reused, and the size is the number of lines, axiom lines included.
--
--   Theorem 2.3 simulates this system in semantic ΣΠΣ-PC.
--
--   **Formalization Note** A linear equation is a coefficient vector with a right-hand side; an axiom line is the list of the clause's literals as equations, in any order.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2.1, p.16 (PDF p.18); §2.2, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace SemAC02.Supplement

open LiftSAParity

/-- A linear equation `ℓ = b` over `𝔽₂` in the variables `σ` (Alekseev–Gryaznov–Itsykson–Pitassi–
Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), §2.1, p.16): the coefficient vector `a` of the linear form `ℓ = ∑_j a_j x_j` and the
right-hand side `b ∈ 𝔽₂`. -/
abbrev LinEq (σ : Type) := (σ → ZMod 2) × ZMod 2

/-- A **linear clause** `(ℓ₁ = b₁) ∨ ⋯ ∨ (ℓ_w = b_w)` (p.16), the proof line of Res(⊕). -/
abbrev LinClause (σ : Type) := List (LinEq σ)

/-- The assignment `x` satisfies the linear equation `∑_j a_j x_j = b`. -/
def LinEq.Sat {σ : Type} [Fintype σ] (x : σ → Bool) (e : LinEq σ) : Prop :=
  ∑ j, e.1 j * (if x j then 1 else 0) = e.2

/-- The assignment `x` satisfies the linear clause: some equation of it holds. The empty clause is
satisfied by no assignment. -/
def LinClause.Sat {σ : Type} [Fintype σ] (x : σ → Bool) (C : LinClause σ) : Prop :=
  ∃ e ∈ C, e.Sat x

/-- An ordinary literal as a linear equation (p.16): `x_i` is `x_i = 1` and `¬x_i` is `x_i = 0`. -/
def litLinEq {σ : Type} [DecidableEq σ] (l : σ × Bool) : LinEq σ :=
  (Pi.single l.1 1, if l.2 then 1 else 0)

/-- An **arity-2 semantic Res(⊕) refutation** of a CNF `φ` (§2.1, p.16 and §2.2, p.17): a sequence
of linear clauses in which every line is an axiom clause of `φ` (its literals written as linear
equations, in any order) or a semantic consequence of two earlier lines (`C ∧ D ⊨ E`; `i = j`
allowed, which covers weakening), ending with the empty clause. Lines may be reused, so the
proof is DAG-like, and its size is its number of lines `π.length`, axiom lines included.

**Formalization Note** The axiom clause `C` (a finite set of literals) is written as the list
`C.toList.map litLinEq` up to permutation. -/
def IsSemResXorRef {σ : Type} [Fintype σ] [DecidableEq σ] (φ : CNF σ)
    (π : List (LinClause σ)) : Prop :=
  (∀ (k : ℕ) (hk : k < π.length),
    (∃ C ∈ φ, π[k].Perm (C.toList.map litLinEq)) ∨
    (∃ (i j : ℕ) (hi : i < k) (hj : j < k), ∀ x : σ → Bool,
      LinClause.Sat x (π[i]'(hi.trans hk)) → LinClause.Sat x (π[j]'(hj.trans hk)) →
        LinClause.Sat x π[k])) ∧
  π.getLast? = some []

end SemAC02.Supplement


