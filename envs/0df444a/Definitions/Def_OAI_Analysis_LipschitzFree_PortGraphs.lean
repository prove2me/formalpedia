-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
-- name    : OAI_Analysis_LipschitzFree_PortGraphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:54:52.173029+00:00
-- url     : https://prove2.me/theorems/22696b80-97fa-420c-a6ea-d7ef4b87ec50
-- title:
--   Port graphs, walks along words of ports, reduced words and capped distance labels
-- statement:
--   This file sets up the combinatorial graph model of the construction: graphs in which each edge leaving a vertex is named by a *port*, walks along words of ports, and capped distances from a vertex to the colour classes of a vertex colouring.
--
--   1. **Port graphs.** A port graph with vertex set $X$ and port set $D$ consists of an involution $e\mapsto\bar e$ of $D$ (the reverse port, $\bar{\bar e}=e$) and a move map $X\times D\to X$, $(x,e)\mapsto x\cdot e$, such that
--   $$(x\cdot e)\cdot\bar e=x\qquad\text{for all } x\in X,\ e\in D .$$
--   Thus every move can be undone by the reverse port. The incidence reversal of the port graph is the permutation $(x,e)\mapsto(x\cdot e,\bar e)$ of $X\times D$; it is an involution.
--
--   2. **Walks, reduced words, nearness.** For a word $w=e_1e_2\cdots e_m$ over $D$ (a finite list of ports) and $x\in X$, the walk from $x$ along $w$ ends at
--   $$x\cdot w=(\cdots((x\cdot e_1)\cdot e_2)\cdots)\cdot e_m ,$$
--   with $x\cdot w=x$ for the empty word. A word is *reduced* if it never immediately backtracks: $e_{t+1}\neq\bar e_t$ for all $1\le t<m$. For $n\in\mathbb{N}$, a vertex $y$ is *$n$-near* to $x$ if $y=x\cdot w$ for some word $w$ of length $|w|\le n$.
--
--   3. **Capped distance labels.** Let $\chi:X\to C$ be a colouring of the vertices by a set $C$ of colours and let $\mathrm{cap}\in\mathbb{N}$. For a colour $i\in C$ and a vertex $x$ the label
--   $$\lambda_i(x)=\min\Bigl(\{\mathrm{cap}\}\cup\bigl\{\,|w| : w \text{ a word over } D \text{ with } \chi(x\cdot w)=i\,\bigr\}\Bigr)$$
--   is the length of a shortest walk from $x$ to a vertex of colour $i$, truncated at $\mathrm{cap}$. The file records that $\lambda_i(x)\le\mathrm{cap}$, that $\lambda_i(x)\le|w|$ whenever $\chi(x\cdot w)=i$, and that $\lambda_{\chi(x)}(x)=0$.
--
--   4. **Bounded words.** For $n\in\mathbb{N}$, $W_{\le n}(D)$ is the set of words over $D$ of length at most $n$. It is finite when $D$ is finite; $W_{\le 0}(D)$ consists of the empty word only (so it has exactly one element); and splitting off the first letter gives a bijection
--   $$W_{\le n+1}(D)\;\cong\;\{\varnothing\}\sqcup\bigl(D\times W_{\le n}(D)\bigr).$$
--
--   Port graphs are the graphs from which the metric blocks of the construction are built (every vertex has exactly one outgoing move per port, so for finite $D$ the graph has bounded degree). The labels $\lambda(x)=(\lambda_i(x))_{i\in C}$ place every vertex in the finite box $\{0,\dots,\mathrm{cap}\}^C$, and bounded words are used to count the vertices reachable by short walks.
--
--   **Formalization Note** `PortGraph X D` is a structure with fields `reverse`, `move` and the axioms `reverse_involutive`, `move_reverse`; `incidenceReverse` is the incidence reversal as an `Equiv.Perm (X × D)`. `walk`, `Reduced` (via `List.IsChain`), `Near` and `label` are as above; `label` is defined with `Nat.find` as the least $n$ such that $n=\mathrm{cap}$ or some word of length exactly $n$ reaches colour $i$. Walks use arbitrary (not necessarily reduced) words. `BoundedWords D n` is the subtype of `List D` of lists of length at most $n$, with the equivalences `zeroEquiv`, `succEquiv` and `card_zero`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/PortGraphs.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/PortGraphs.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree

namespace OAI

/-!
# Port graphs, reduced walks, and capped-distance labels
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree
open scoped BigOperators Classical

structure PortGraph (X D : Type*) where
  reverse : D → D
  reverse_involutive : Function.Involutive reverse
  move : X → D → X
  move_reverse : ∀ x e, move (move x e) (reverse e) = x

namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)

def incidenceReverse : Equiv.Perm (X × D) :=
  (show Function.Involutive (fun z : X × D => (G.move z.1 z.2, G.reverse z.2)) from by
    rintro ⟨x, e⟩
    simp only [G.move_reverse, G.reverse_involutive e]).toPerm

@[simp] theorem incidenceReverse_apply (x : X) (e : D) :
    G.incidenceReverse (x, e) = (G.move x e, G.reverse e) := rfl

def walk (x : X) : List D → X
  | [] => x
  | e :: w => walk (G.move x e) w

@[simp] theorem walk_nil (x : X) : G.walk x [] = x := rfl
@[simp] theorem walk_cons (x : X) (e : D) (w : List D) :
    G.walk x (e::w) = G.walk (G.move x e) w := rfl

def Reduced (w : List D) : Prop := w.IsChain (fun e f => f ≠ G.reverse e)

def Near (n : ℕ) (x y : X) : Prop := ∃ w : List D, w.length ≤ n ∧ G.walk x w = y

def label {C : Type*} (color : X → C) (cap : ℕ) (i : C) (x : X) : ℕ :=
  Nat.find (show ∃ n : ℕ, n = cap ∨ ∃ w : List D,
    w.length = n ∧ color (G.walk x w) = i from ⟨cap, Or.inl rfl⟩)

theorem label_le {C : Type*} (color : X → C) (cap : ℕ) (i : C) (x : X) :
    G.label color cap i x ≤ cap := Nat.find_min' _ (Or.inl rfl)

theorem label_le_of_walk {C : Type*} (color : X → C) (cap : ℕ) (i : C)
    (x : X) (w : List D) (hw : color (G.walk x w) = i) :
    G.label color cap i x ≤ w.length := Nat.find_min' _ (Or.inr ⟨w, rfl, hw⟩)

@[simp] theorem label_own_color {C : Type*} (color : X → C) (cap : ℕ) (x : X) :
    G.label color cap (color x) x = 0 :=
  Nat.eq_zero_of_le_zero (G.label_le_of_walk color cap (color x) x [] rfl)

end PortGraph

def BoundedWords (D : Type*) (n : ℕ) := {w : List D // w.length ≤ n}

instance {D : Type*} [Finite D] (n : ℕ) : Fintype (BoundedWords D n) :=
  (List.finite_length_le D n).fintype

namespace BoundedWords
variable {D : Type*}

def zeroEquiv : BoundedWords D 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], le_rfl⟩
  left_inv w := Subtype.ext (by have := w.property; simp_all)
  right_inv _ := rfl

def succEquiv (n : ℕ) : BoundedWords D (n+1) ≃ Unit ⊕ (D × BoundedWords D n) where
  toFun w := match w with
    | ⟨[], _⟩ => Sum.inl ()
    | ⟨d::w, h⟩ => Sum.inr (d, ⟨w, Nat.le_of_succ_le_succ h⟩)
  invFun w := match w with
    | Sum.inl _ => ⟨[], by simp⟩
    | Sum.inr (d, w) => ⟨d::w.val, Nat.succ_le_succ w.property⟩
  left_inv w := by rcases w with ⟨(_|⟨d,w⟩),h⟩ <;> rfl
  right_inv w := by rcases w with (_|⟨d,w⟩) <;> rfl

@[simp] theorem card_zero [Finite D] : Fintype.card (BoundedWords D 0) = 1 := by
  simpa using Fintype.card_congr (zeroEquiv (D := D))

end BoundedWords

namespace PortGraph
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

end PortGraph
end DiscreteFree

end

end

end OAI


