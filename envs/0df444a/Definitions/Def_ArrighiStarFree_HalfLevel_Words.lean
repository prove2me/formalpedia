-- Prove2me | Definitions.Def_ArrighiStarFree_HalfLevel_Words
-- name    : ArrighiStarFree_HalfLevel_Words
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:06:08.988723+00:00
-- url     : https://prove2.me/theorems/8afb7184-08d2-4b65-9c82-10fab7682573
-- title:
--   Finite words, shuffle ideals and the first half-level
-- statement:
--   A word over an alphabet $\Sigma$ is a finite list of letters, including the empty word $\varepsilon$; a language is a set of words. A word $z$ is a shuffle of $u$ and $v$ when, for some $k\ge0$, there are factorizations $u=u_0\cdots u_k$, $v=v_0\cdots v_k$ and $z=u_0v_0\cdots u_kv_k$, allowing empty factors. A language $L$ is a shuffle ideal when every shuffle of a member of $L$ with an arbitrary word belongs to $L$.
--
--   For a pattern $p=a_1\cdots a_k$, its monomial consists of words containing $p$ as a scattered subword, equivalently $\Sigma^*a_1\Sigma^*\cdots a_k\Sigma^*$. The first half-level consists of finite, possibly empty, unions of these monomials. Thus the empty union gives the empty language and the empty pattern gives $\Sigma^*$.
--
--   For a finite indexed family $(L_i)_{i<m}$, define
--   $$\operatorname{Product}(L)=\{w_0\cdots w_{m-1}: w_i\in L_i\},\qquad \operatorname{Intersection}(L)=\{w:\forall i<m,\ w\in L_i\}.$$
--   The shortest length is $\min\{|w|:w\in L\}$ for nonempty $L$, and zero for empty $L$. Given an alphabet enumeration $a$, the cyclic word with exponent $\ell$ is the concatenation of $\ell$ copies of $a$.
--
--   These definitions are independent of automata and computation. Shuffle ideals and half-level membership are defined separately; their equivalence is not assumed as a field or an axiom.
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), §2–3, printed pp. 23:4–23:7, PDF pp. 4–7

import Mathlib.Computability.NFA
import Mathlib.Order.Lattice.Nat

namespace ArrighiStarFree.HalfLevel

/-- Literal factorization definition of shuffle (§3, PDF p. 7). -/
def Shuffle {α : Type*} (u v w : List α) : Prop :=
  ∃ (k : ℕ) (us vs : Fin (k + 1) → List α),
    u = (List.ofFn us).flatten ∧ v = (List.ofFn vs).flatten ∧
    w = (List.ofFn (fun i => us i ++ vs i)).flatten

def ShuffleIdeal {α : Type*} (L : Language α) : Prop :=
  ∀ u ∈ L, ∀ v w, Shuffle u v w → w ∈ L

/-- The marked product Σ* a₁ Σ* ... aₖ Σ*, expressed by scattered occurrence. -/
def Monomial {α : Type*} (pattern : List α) : Language α :=
  {w | pattern.Sublist w}

/-- Finite, possibly empty, unions of marked products; the empty pattern gives Σ*. -/
def FirstHalfLevel {α : Type*} (L : Language α) : Prop :=
  ∃ patterns : List (List α), ∀ w, w ∈ L ↔ ∃ p ∈ patterns, w ∈ Monomial p

def LanguageProduct {α : Type*} {m : ℕ} (L : Fin m → Language α) : Language α :=
  {w | ∃ ws : Fin m → List α, (∀ i, ws i ∈ L i) ∧ w = (List.ofFn ws).flatten}

def LanguageIntersection {α : Type*} {m : ℕ} (L : Fin m → Language α) : Language α :=
  {w | ∀ i, w ∈ L i}

/-- Minimum word length, totalized to zero for the empty language. -/
noncomputable def shortestLength {α : Type*} (L : Language α) : ℕ :=
  sInf {n | ∃ w ∈ L, w.length = n}

def cycleWord {α : Type*} (alphabet : List α) (n : ℕ) : List α :=
  (List.replicate n alphabet).flatten

end ArrighiStarFree.HalfLevel


