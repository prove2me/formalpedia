-- Prove2me | Definitions.Def_CopylessCRA_IsRep
-- name    : CopylessCRA_IsRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:35.332197+00:00
-- url     : https://prove2.me/theorems/8db594d2-c59b-4bbd-82ef-bdcd7c9ee781
-- title:
--   Linear representations of a series, minimality, invertible series
-- statement:
--   Words are finite lists over the alphabet $\Sigma$, and for letter matrices $(M_a)_{a\in\Sigma}$ the word matrix is $M_{a_1\cdots a_n}=M_{a_1}\cdots M_{a_n}$ (left to right), $M_\varepsilon=I$.
--
--   1. A *representation* of $f:\Sigma^*\to\mathbb Q$ on $\mathbb Q^\iota$ ($\iota$ finite) is a row vector $\lambda$, matrices $M_a$ and a column vector $\gamma$ with $f(w)=\lambda M_w\gamma$ for all words $w$.
--   2. It is *minimal* if the row vectors $\lambda M_w$ span the dual space and the columns $M_w\gamma$ span the space ($w$ over all words, $\varepsilon$ included).
--   3. $f$ is *invertible* if it has a minimal representation $\mathbb Q^d$ whose letter matrices are invertible.
--   4. Display (2): for a representation, $W=\operatorname{span}\{M_w\gamma\}$ (the reachable space) and $\{h:\lambda M_vh=0\ \forall v\}$ (the unobservable vectors); $N$ is their intersection.
--   5. For an endomorphism $B$ leaving subspaces $N$ and $W$ invariant, the operator induced on the subquotient $W/(N\cap W)$.
--
--   These notions carry the hypotheses of Theorem 1 and the subquotient arguments of §2.2, §3 and Lemma 15.
--
--   **Formalization Note** $\lambda$ is written `lam`. Minimal representations are unique up to simultaneous conjugation, so "some minimal representation has invertible letter matrices" is the paper's "its minimal letter matrices are invertible".
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), §1, p.1 (PDF p.3); §2.2 and display (2), p.6 (PDF p.8)

import Mathlib
open Matrix

namespace CopylessCRA

/-- The word matrix `M_w = M_{a₁} ⋯ M_{aₙ}` for `w = a₁⋯aₙ` (left to right), with `M_ε = I`.
Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), §1, p.1 (PDF p.3). -/
def wordMat {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : α → Matrix ι ι R) (w : List α) : Matrix ι ι R :=
  (w.map M).prod

/-- A **representation** of `f : Σ* → ℚ` (§2.2, p.6, PDF p.8): a row vector `λ`, matrices `M_a`
and a column vector `γ` with `f(w) = λ M_w γ` for every word `w`. The state space is `ℚ^ι` for a
finite index type `ι`.

**Formalization Note** `λ` is written `lam` (reserved word in Lean). -/
def IsRep {α ι : Type*} [Fintype ι] [DecidableEq ι] (f : List α → ℚ) (lam : ι → ℚ)
    (M : α → Matrix ι ι ℚ) (γ : ι → ℚ) : Prop :=
  ∀ w, f w = lam ⬝ᵥ (wordMat M w *ᵥ γ)

/-- A representation is **minimal** (§2.2, p.6) if the row vectors `λ M_w` span the dual space and
the columns `M_w γ` span the space (`w` ranges over all words, the empty word included). -/
def IsMinimalRep {α ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℚ)
    (M : α → Matrix ι ι ℚ) (γ : ι → ℚ) : Prop :=
  Submodule.span ℚ (Set.range fun w : List α => Matrix.vecMul lam (wordMat M w)) = ⊤ ∧
  Submodule.span ℚ (Set.range fun w : List α => wordMat M w *ᵥ γ) = ⊤

/-- `f` is an **invertible rational series** (§1, p.1, PDF p.3): it has a minimal representation
whose letter matrices are invertible.

**Formalization Note** Minimal representations are unique up to simultaneous conjugation (§2.2), so
"some minimal representation has invertible letter matrices" is the paper's "its minimal letter
matrices are invertible". -/
def IsInvertibleSeries {α : Type*} (f : List α → ℚ) : Prop :=
  ∃ (d : ℕ) (lam : Fin d → ℚ) (M : α → Matrix (Fin d) (Fin d) ℚ) (γ : Fin d → ℚ),
    IsRep f lam M γ ∧ IsMinimalRep lam M γ ∧ ∀ a, IsUnit (M a)

/-- The reachable space `span{M_w γ : w ∈ Σ*}` of a representation, the space `W` of display (2),
§2.2, p.6 (PDF p.8). -/
def reachSpan {α ι : Type*} [Fintype ι] [DecidableEq ι] (M : α → Matrix ι ι ℚ) (γ : ι → ℚ) :
    Submodule ℚ (ι → ℚ) :=
  Submodule.span ℚ (Set.range fun w : List α => wordMat M w *ᵥ γ)

/-- The unobservable vectors `{h : λ M_v h = 0 for all v ∈ Σ*}`; display (2) puts
`N = W ∩ unobservable`, §2.2, p.6 (PDF p.8). -/
def unobservable {α ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℚ)
    (M : α → Matrix ι ι ℚ) : Submodule ℚ (ι → ℚ) where
  carrier := {h | ∀ v : List α, lam ⬝ᵥ (wordMat M v *ᵥ h) = 0}
  add_mem' := by
    intro a b ha hb v
    simp [Matrix.mulVec_add, dotProduct_add, ha v, hb v]
  zero_mem' := by intro v; simp
  smul_mem' := by
    intro c a ha v
    simp [Matrix.mulVec_smul, dotProduct_smul, ha v]

/-- The operator induced on a subquotient `W / N` (with `N` read inside `W`) by an endomorphism `B`
that leaves `W` and `N` invariant. Used for `ρ(y)` (§3, p.8) and for the induced operators of §2.2
and Lemma 15. -/
def quotOp {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (B : Module.End F V)
    (W N : Submodule F V) (hW : ∀ h ∈ W, B h ∈ W) (hN : ∀ h ∈ N, B h ∈ N) :
    Module.End F (W ⧸ N.comap W.subtype) :=
  (N.comap W.subtype).mapQ (N.comap W.subtype) (B.restrict hW) (fun _ hx => hN _ hx)

end CopylessCRA


