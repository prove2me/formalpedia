-- Prove2me | Definitions.Def_PopularMixed_Double
-- name    : PopularMixed_Double
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:40.026261+00:00
-- url     : https://prove2.me/theorems/55ea9725-cb9f-40c5-bf07-d510767fa3b7
-- title:
--   The doubled instance $H$ and the maps $f$, $h$ (Section 4)
-- statement:
--   From $G=(A\cup B,E)$ build $H=(V\cup V',E')$ with $V=A_0\cup B_1$, $V'=B_0\cup A_1$, where $A_i=\{a_i\}$, $B_i=\{b_i\}$, and
--   $$E'=E_0\cup E_1\cup\{(u_0,u_1):u\in A\cup B\},\qquad E_i=\{(a_i,b_i):(a,b)\in E\}.$$
--   Each $u_i$ ranks its neighbours $v_i$ as $u$ ranks $v$ in $G$, and ranks $u_{1-i}$ last among its neighbours.
--
--   1. $f(\vec x)=\vec z$ with $z(a_0,b_0)=z(a_1,b_1)=x(a,b)$ for $(a,b)\in E$ and $z(u_0,u_1)=x(u,\ell(u))$.
--   2. $h(\vec z)=\vec y$ with $y(a,b)=\big(z(a_0,b_0)+z(b_1,a_1)\big)/2$ for $(a,b)\in E$ and $y(u,\ell(u))=z(u_0,u_1)$.
--
--   Through $H$, which always has a perfect stable matching (Lemma 4.1), the integrality of Theorem 3.1 yields half-integrality in $G$ (Theorem 4.1).
--
--   **Formalization Note** $V$ is `A ⊕ B` (`inl a` = $a_0$, `inr b` = $b_1$) and $V'$ is `B ⊕ A` (`inl b` = $b_0$, `inr a` = $a_1$). $u_{1-i}$ gets rank `topA`/`topB`, one more than the largest rank in $u$'s list. `hMap` gives only the genuine-edge coordinates; its last-resort coordinate is $1-\sum_v y(u,v)$, which equals $z(u_0,u_1)$ whenever the last resorts of $u_0,u_1$ carry weight $0$ in $\vec z$, in particular for every $\vec z\in\mathcal P_H$.
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 4, PDF p.11 (H, Fig. 7, f, h).

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-!
Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017),
Section 4, PDF p.11: the doubled instance `H = (V ∪ V′, E′)` and the maps `f` and `h`.

**Formalization Note.** `V = A₀ ∪ B₁` is `A ⊕ B` (`inl a` = `a₀`, `inr b` = `b₁`) and
`V′ = B₀ ∪ A₁` is `B ⊕ A` (`inl b` = `b₀`, `inr a` = `a₁`). The edges are `(a₀, b₀)` and
`(b₁, a₁)` for `(a,b) ∈ E`, `(a₀, a₁)` for `a ∈ A` and `(b₁, b₀)` for `b ∈ B`. Each `u_i` ranks its
neighbours `v_i` as `u` ranks `v` in `G`, and ranks `u_{1−i}` below all of them, with rank
`1 + max_v rank_u(v)` (`topA`, `topB`). In `h`, the last-resort coordinate of `h(z)` is not a
separate value (`lrA`, `lrB` of the Fractional bundle): it is `1 − Σ_v h(z)(u,v)`, which equals
the paper's `z(u₀,u₁)` whenever the last resorts of `u₀, u₁` in `H` carry weight `0`, in
particular for every `z ∈ P_H` (`H` has a perfect stable matching, Lemma 4.1).
-/

open Finset

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

namespace Instance

variable (G : Instance A B)

/-- A rank of `a` below every rank used in `a`'s list. -/
def topA (a : A) : ℕ := (univ.sup (G.rankA a)) + 1

/-- A rank of `b` below every rank used in `b`'s list. -/
def topB (b : B) : ℕ := (univ.sup (G.rankB b)) + 1

omit [DecidableEq A] [DecidableEq B] in
/-- Every rank in `a`'s list is below `topA a`. -/
lemma rankA_lt_topA (a : A) (b : B) : G.rankA a b < G.topA a :=
  Nat.lt_succ_of_le (Finset.le_sup (f := G.rankA a) (Finset.mem_univ b))

omit [DecidableEq A] [DecidableEq B] in
/-- Every rank in `b`'s list is below `topB b`. -/
lemma rankB_lt_topB (b : B) (a : A) : G.rankB b a < G.topB b :=
  Nat.lt_succ_of_le (Finset.le_sup (f := G.rankB b) (Finset.mem_univ a))

/-- Adjacency in `H` (PDF p.11): `E′ = E₀ ∪ E₁ ∪ {(u₀,u₁) : u ∈ A ∪ B}`. -/
def dAdj : A ⊕ B → B ⊕ A → Prop
  | Sum.inl a, Sum.inl b => (a, b) ∈ G.E
  | Sum.inr b, Sum.inr a => (a, b) ∈ G.E
  | Sum.inl a, Sum.inr a' => a = a'
  | Sum.inr b, Sum.inl b' => b = b'

instance (u : A ⊕ B) (v : B ⊕ A) : Decidable (G.dAdj u v) := by
  cases u <;> cases v <;> unfold dAdj <;> infer_instance

/-- Ranks of the `V`-side vertices of `H`. -/
def dRankA : A ⊕ B → B ⊕ A → ℕ
  | Sum.inl a, Sum.inl b => G.rankA a b
  | Sum.inl a, Sum.inr _ => G.topA a
  | Sum.inr b, Sum.inr a => G.rankB b a
  | Sum.inr b, Sum.inl _ => G.topB b

/-- Ranks of the `V′`-side vertices of `H`. -/
def dRankB : B ⊕ A → A ⊕ B → ℕ
  | Sum.inl b, Sum.inl a => G.rankB b a
  | Sum.inl b, Sum.inr _ => G.topB b
  | Sum.inr a, Sum.inr b => G.rankA a b
  | Sum.inr a, Sum.inl _ => G.topA a

/-- The doubled instance `H` of Section 4 (PDF p.11). -/
def double : Instance (A ⊕ B) (B ⊕ A) where
  E := univ.filter fun p => G.dAdj p.1 p.2
  rankA := G.dRankA
  rankB := G.dRankB
  rankA_inj := by
    intro u v v' hv hv' h
    simp only [mem_filter, mem_univ, true_and] at hv hv'
    rcases u with a | b <;> rcases v with b1 | a1 <;> rcases v' with b2 | a2 <;>
      simp only [dAdj, dRankA] at hv hv' h ⊢
    · exact congrArg _ (G.rankA_inj a b1 b2 hv hv' h)
    · exact absurd h (G.rankA_lt_topA a b1).ne
    · exact absurd h.symm (G.rankA_lt_topA a b2).ne
    · rw [← hv, ← hv']
    · rw [← hv, ← hv']
    · exact absurd h (G.rankB_lt_topB b a2).ne'
    · exact absurd h (G.rankB_lt_topB b a1).ne
    · exact congrArg _ (G.rankB_inj b a1 a2 hv hv' h)
  rankB_inj := by
    intro v u u' hu hu' h
    simp only [mem_filter, mem_univ, true_and] at hu hu'
    rcases v with b | a <;> rcases u with a1 | b1 <;> rcases u' with a2 | b2 <;>
      simp only [dAdj, dRankB] at hu hu' h ⊢
    · exact congrArg _ (G.rankB_inj b a1 a2 hu hu' h)
    · exact absurd h (G.rankB_lt_topB b a1).ne
    · exact absurd h.symm (G.rankB_lt_topB b a2).ne
    · rw [hu, hu']
    · rw [hu, hu']
    · exact absurd h (G.rankA_lt_topA a b2).ne'
    · exact absurd h (G.rankA_lt_topA a b1).ne
    · exact congrArg _ (G.rankA_inj a b1 b2 hu hu' h)

end Instance

/-- The map `f` (PDF p.11): `z(a₀,b₀) = z(a₁,b₁) = x(a,b)` for `(a,b) ∈ E` and
`z(u₀,u₁) = x(u, ℓ(u))` for `u ∈ A ∪ B`. -/
def fMap (x : A → B → ℝ) : A ⊕ B → B ⊕ A → ℝ
  | Sum.inl a, Sum.inl b => x a b
  | Sum.inr b, Sum.inr a => x a b
  | Sum.inl a, Sum.inr a' => if a = a' then lrA x a else 0
  | Sum.inr b, Sum.inl b' => if b = b' then lrB x b else 0

/-- The map `h` (PDF p.11): `y(a,b) = (z(a₀,b₀) + z(b₁,a₁))/2` for `(a,b) ∈ E`. -/
noncomputable def hMap (z : A ⊕ B → B ⊕ A → ℝ) : A → B → ℝ :=
  fun a b => (z (Sum.inl a) (Sum.inl b) + z (Sum.inr b) (Sum.inr a)) / 2

end PopularMixed


