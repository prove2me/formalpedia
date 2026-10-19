-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_Colors
-- name    : OAI_ModelTheory_Categoricity_Colors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:32:54.995977+00:00
-- url     : https://prove2.me/theorems/f7423d6e-6e46-4263-9f5c-ef31515ae536
-- title:
--   Colors modulo finite change, coding of finite diagrams under CH, and diagram tests for tuples
-- statement:
--   This file defines the palette of colors carried by bit sequences, a coding of finite diagrams by colors under the continuum hypothesis, finite tuples with their subtuples, and the diagram test that tuples must pass. Write $[k] = \{0, \dots, k-1\}$.
--
--   1. **Colors modulo finite change.** Binary sequences $a, b : \mathbb{N} \to \{0, 1\}$ are equivalent, $a \sim b$, if the set $\{ n : a(n) \neq b(n) \}$ is finite; this is an equivalence relation. A color is a class $[a] \in 2^{\mathbb{N}}/\!\sim$, and $[a] = [b]$ if and only if $a \sim b$. With a fixed pairing bijection $\mathbb{N} \to \mathbb{N} \times \mathbb{N}$ and $\pi_1$ its first coordinate, the repetition $\hat a = a \circ \pi_1$ repeats every bit of $a$ infinitely often, and $a \mapsto [\hat a]$ is injective. The number of colors is
--   $$
--   \bigl| 2^{\mathbb{N}} /\!\sim \bigr| = 2^{\aleph_0}.
--   $$
--   The palette is this set of colors, lifted to the working universe and still of cardinality $2^{\aleph_0}$; every color has a chosen representative sequence.
--
--   2. **Coding diagrams under CH.** If $A$ is countable and $|B| \le 2^{\aleph_0}$, then the set $B^A$ of functions $A \to B$ has $|B^A| \le 2^{\aleph_0}$. Recall that a diagram on a set $A$ is a triple consisting of two binary relations on labels and a tag function from labels to $\omega_1$, where a label is a pair $(J, i)$ of a nonempty finite $J \subseteq A$ and $i \in \mathbb{N}$. Assume the continuum hypothesis $\mathrm{CH}$, i.e. $2^{\aleph_0} = \aleph_1$. Then for every $n$ there are at most $2^{\aleph_0}$ diagrams on $[n]$, and the code is a fixed injection
--   $$
--   \mathrm{code} : \bigsqcup_{n \in \mathbb{N}} \mathrm{Diag}([n+1]) \hookrightarrow \mathrm{Palette},
--   $$
--   chosen once and for all, which sends a pair $(n, d)$ with $d$ a diagram on $[n+1]$ to a color.
--
--   3. **Tuples and subtuples.** A tuple in a set $I$ is a nonempty finite injective sequence $t = (t_0, \dots, t_n)$ of elements of $I$, i.e. an injection $[n+1] \hookrightarrow I$. For a strictly increasing map $e : [m+1] \to [n+1]$, the subtuple $t \circ e = (t_{e(0)}, \dots, t_{e(m)})$ is again a tuple, and the identity map gives back $t$.
--
--   4. **Diagram tests.** Assume CH and fix $n \in \mathbb{N}$. Let $s$ assign a palette color $s(m, e)$ to every $m \in \mathbb{N}$ and every strictly increasing $e : [m+1] \to [n+1]$. Then $s$ passes if there is a diagram $d$ on $[n+1]$ such that for all such $m$ and $e$ the restriction $d|_e$ (the diagram on $[m+1]$ obtained by pulling relations and tags back along $(J, i) \mapsto (e[J], i)$) is valid and
--   $$
--   \mathrm{code}(m, d|_e) = s(m, e).
--   $$
--   For a coloring $c$ of the tuples in $I$ by palette colors, a tuple $t = (t_0, \dots, t_n)$ passes the test for $c$ if the assignment $(m, e) \mapsto c(t \circ e)$ passes: the colors of all subtuples of $t$, including $t$ itself, are the codes of the restrictions of one diagram on the positions of $t$, all of which are valid. Here a diagram is valid if its first relation is an equivalence relation, its second relation and its tags are invariant under it, tags strictly increase along the second relation, the second relation is extensional modulo the equivalence, and distinct points $a \neq b$ have inequivalent root labels $(\{a\}, 0)$ and $(\{b\}, 0)$. The file also records that there are no labels on the empty set and fixes the empty diagram on it.
--
--   Under CH the palette is large enough to code every diagram on a finite set, and this is how bits carry structural information in the main construction: a column of bits $n \mapsto \beta(n)$ determines a color, and the test asks that the colors on the subtuples of a tuple be coherent codes of a single diagram. A separate result shows that no sequence of colors that depends only on the length of the tuple passes at every length; this drives the bound on the size of index sets.
--
--   **Formalization Note** `Sequence` is the type of Boolean sequences, `equivalent` and `eventualSetoid` give the relation, `Color` is the quotient with class map `color`, `repeatSequence` uses `Nat.unpair`, `Palette` is the `ULift` of `Color` to universe $u$, and `representative` is `Quotient.out`. `CH` is the proposition $2^{\aleph_0} = \aleph_1$ for cardinals in universe $u$; `diagram_bound` and `code` take a proof of it, and `code` is obtained with `Classical.choice`. `Tuple I` is the sigma type over $n$ of embeddings of `Fin (n + 1)` into `I`, and `sub` takes an order embedding of `Fin (m + 1)` into `Fin (t.1 + 1)`. `Passes` and `Test` are the predicates of item 4, and `emptyLabel` and `emptyDiagram` handle the empty index set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Colors.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Colors.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CHObstruction mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Colors

abbrev Sequence := ℕ → Bool

def equivalent (a b : Sequence) : Prop := {n | a n ≠ b n}.Finite

def eventualSetoid : Setoid Sequence where
  r := equivalent
  iseqv := ⟨by intro a; simp [equivalent], by
    intro a b h
    simpa only [equivalent, ne_comm] using h, by
    intro a b c hab hbc
    apply (hab.union hbc).subset
    intro n hn
    by_cases hab' : a n = b n
    · exact Or.inr (fun hbc' => hn (hab'.trans hbc'))
    · exact Or.inl hab' ⟩

abbrev Color := Quotient eventualSetoid

def color (a : Sequence) : Color := Quotient.mk _ a

theorem color_eq_iff (a b : Sequence) : color a = color b ↔ equivalent a b :=
  Quotient.eq

def repeatSequence (a : Sequence) : Sequence := fun i => a (Nat.unpair i).1

theorem repeat_injective : Function.Injective (fun a => color (repeatSequence a)) := by
  intro a b hab
  have h := (color_eq_iff _ _).1 hab
  funext n
  by_contra hn
  have hi : Function.Injective (Nat.pair n) := by
    intro j k heq
    have := congrArg Nat.unpair heq
    simpa only [Nat.unpair_pair, Prod.mk.injEq, true_and] using this
  have hf : (Set.range (Nat.pair n)).Finite := h.subset (by
    rintro _ ⟨m, rfl⟩
    simpa only [repeatSequence, Nat.unpair_pair, Set.mem_ofPred_eq] using hn)
  exact Set.infinite_univ ((hf.preimage hi.injOn).subset (fun _ _ => Set.mem_range_self _))

theorem cardinal : #Color = (𝔠 : Cardinal) := by
  have h : #Sequence = (𝔠 : Cardinal) := by simp [Sequence]
  apply le_antisymm
  · exact Cardinal.mk_quotient_le.trans h.le
  · exact h.symm.le.trans (Cardinal.mk_le_of_injective repeat_injective)

abbrev Palette := ULift.{u} Color

theorem palette_cardinal : #Palette.{u} = (𝔠 : Cardinal.{u}) := by
  rw [Cardinal.mk_uLift, cardinal, Cardinal.lift_continuum]

def representative (s : Color) : Sequence := Quotient.out s

theorem function_bound (A : Type) [Countable A] (B : Type u)
    (hB : #B ≤ (𝔠 : Cardinal.{u})) : #(A → B) ≤ (𝔠 : Cardinal.{u}) := by
  rw [Cardinal.mk_arrow, Cardinal.lift_uzero]
  have hA : Cardinal.lift.{u} #A ≤ (ℵ₀ : Cardinal.{u}) := by
    simpa only [Cardinal.lift_aleph0] using
      (Cardinal.lift_le.{u, 0}.2 (Cardinal.mk_le_aleph0 (α := A)))
  exact ((Cardinal.power_le_power_right hB).trans
    (Cardinal.power_le_power_left Cardinal.continuum_ne_zero hA)).trans_eq
    Cardinal.continuum_power_aleph0

open Diagrams

theorem diagram_bound (hCH : CH.{u}) (n : ℕ) :
    #(Diagram.{u} (Fin n)) ≤ (𝔠 : Cardinal.{u}) := by
  let A := Label (Fin n)
  have hc : Cardinal.lift.{u} #(A → A → Prop) ≤ (𝔠 : Cardinal.{u}) := by
    have h : #(A → A → Prop) ≤ (𝔠 : Cardinal) :=
      function_bound A _ (function_bound A Prop (by rw [Cardinal.mk_Prop]; exact (Cardinal.nat_lt_continuum 2).le))
    simpa only [Cardinal.lift_continuum] using
      (Cardinal.lift_le.{u, 0}.2 h)
  have ht : #(A → Tag.{u}) ≤ (𝔠 : Cardinal.{u}) :=
    function_bound A _ (by rw [Cardinal.mk_toType, Ordinal.card_omega, ← Cardinal.two_power_aleph0, hCH])
  let f : Diagram.{u} (Fin n) → ((A → A → Prop) × (A → A → Prop)) × (A → Tag.{u}) :=
    fun d => ((d.eqv, d.rel), d.tag)
  have hf : Function.Injective f := by
    intro d e h
    cases d; cases e
    simpa only [f, Prod.mk.injEq, Diagram.mk.injEq, and_assoc] using h
  apply (Cardinal.mk_le_of_injective hf).trans
  simp only [Cardinal.mk_prod, Cardinal.lift_mul, Cardinal.lift_id, Cardinal.lift_uzero]
  exact (mul_le_mul' (mul_le_mul' hc hc) ht).trans_eq (by
    rw [Cardinal.mul_eq_self Cardinal.aleph0_le_continuum,
      Cardinal.mul_eq_self Cardinal.aleph0_le_continuum])

def code (hCH : CH.{u}) : (Σ n : ℕ, Diagram.{u} (Fin (n + 1))) ↪ Palette.{u} := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).1
  rw [palette_cardinal, Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun n : ℕ => #(Diagram.{u} (Fin (n + 1)))) ≤
        Cardinal.sum (fun _ : ℕ => (𝔠 : Cardinal.{u})) :=
      Cardinal.sum_le_sum _ _ (fun n => diagram_bound hCH (n + 1))
    _ = (𝔠 : Cardinal.{u}) := by
      simp only [Cardinal.sum_const, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
      exact Cardinal.aleph0_mul_continuum

end Colors

namespace Tuples

abbrev Tuple (I : Type v) := Σ n : ℕ, Fin (n + 1) ↪ I

def sub {I : Type v} (t : Tuple I) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    Tuple I := ⟨m, e.toEmbedding.trans t.2⟩

@[simp] theorem sub_refl {I : Type v} (t : Tuple I) :
    sub t (OrderIso.refl _).toOrderEmbedding = t := by
  cases t
  rfl

end Tuples

namespace Tests

open Diagrams Colors Tuples

variable (hCH : CH.{u})

def Passes {n : ℕ}
    (s : ∀ m : ℕ, (Fin (m + 1) ↪o Fin (n + 1)) → Palette.{u}) : Prop :=
  ∃ d : Diagram.{u} (Fin (n + 1)), ∀ m (e : Fin (m + 1) ↪o Fin (n + 1)),
    (d.restrict e.toEmbedding).Valid ∧
      code hCH ⟨m, d.restrict e.toEmbedding⟩ = s m e

def Test {I : Type v} (c : Tuple I → Palette.{u}) (t : Tuple I) : Prop :=
  Passes hCH (fun _ e => c (sub t e))

instance emptyLabel : IsEmpty (Label (Fin 0)) := ⟨fun l => by
  obtain ⟨x, _⟩ := l.1.property
  exact Fin.elim0 x⟩

def emptyDiagram : Diagram.{u} (Fin 0) where
  eqv a := isEmptyElim a
  rel a := isEmptyElim a
  tag a := isEmptyElim a

end Tests

end CHObstruction

end

end OAI


