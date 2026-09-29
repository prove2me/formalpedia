-- Prove2me | Definitions.Def_CerednikDrinfeld_WalkOverlap
-- name    : CerednikDrinfeld_WalkOverlap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/07f5b22a-c761-5893-866d-3309e1531d9c
-- title:
--   Signed dart-overlap pairing of walks in a graph
-- statement:
--   Fix a type $W$ of vertices with decidable equality and a simple graph $\mathcal T$ on $W$. For walks $P : \mathcal T.\mathrm{Walk}\,u\,v$ and $Q : \mathcal T.\mathrm{Walk}\,u'\,v'$, [`CerednikDrinfeld.Mumford.walkOverlap`](../def/CerednikDrinfeld_WalkOverlap.html#L40) is the integer
--   $$\sum_{d \in \operatorname{darts}(P)} \bigl(\#\{\,d \text{ in } \operatorname{darts}(Q)\,\} - \#\{\,\bar d \text{ in } \operatorname{darts}(Q)\,\}\bigr),$$
--   where $\operatorname{darts}(\cdot)$ is Mathlib's list of oriented edges traversed by a walk, $\bar d$ is the dart with its two ends exchanged, and the counts are multiplicities in the list; the outer sum likewise runs over the list of darts of $P$ with multiplicity, so a dart traversed repeatedly by $P$ contributes once for each traversal. Thus each oriented edge traversal of $P$ contributes $+1$ for every traversal of the same edge by $Q$ in the same direction and $-1$ for every traversal in the opposite direction.
--
--   The module establishes the formal properties of this pairing: it vanishes when either walk is the constant walk; it satisfies the evident recursion when a dart is prepended to the left argument; it is additive under concatenation in each argument separately (`walkOverlap_append_left`, `walkOverlap_append_right`); it changes sign under reversal of either argument (`walkOverlap_reverse_left`, `walkOverlap_reverse_right`); and it is unchanged if an injective graph homomorphism $f : \mathcal T \to_g \mathcal T'$ is applied to both walks (`walkOverlap_map`). Auxiliary declarations record that integer-valued list sums commute with pointwise negation and addition, and that an injective graph homomorphism induces an injective map on darts.
--
--   **Relation to Mathlib.** Walks, their dart lists, dart reversal and the induced map on darts are Mathlib's; the signed overlap pairing itself is the project's own notion.
--
--   **Where it is used.** The pairing is used in the Čerednik–Drinfeld/Mumford uniformisation strand, where walks in the Bruhat–Tits tree of $\mathrm{PGL}_2$ over a local field are compared: for geodesics in a tree it measures the signed length of the common segment, and the additivity, oddness under reversal and equivariance under injective graph homomorphisms are what make it usable as an intersection pairing on translates of a cycle and in valuations of cross ratios of ends.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_WalkOverlap.lean

import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CerednikDrinfeld
namespace Mumford

variable {W : Type} [DecidableEq W] {𝒯 : SimpleGraph W}

namespace WalkOverlapAux
variable {α : Type}

theorem sum_map_neg_int (l : List α) (f : α → ℤ) : (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_add_int (l : List α) (f g : α → ℤ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

omit [DecidableEq W] in
theorem mapDart_injective {W' : Type} {𝒯' : SimpleGraph W'} (f : 𝒯 →g 𝒯') (hf : Function.Injective f) :
    Function.Injective f.mapDart := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
  have h' := congrArg SimpleGraph.Dart.toProd h
  simp only [SimpleGraph.Hom.mapDart, Prod.map, Prod.mk.injEq] at h'
  obtain ⟨h1, h2⟩ := h'
  cases hf h1
  cases hf h2
  rfl

end WalkOverlapAux

def walkOverlap {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') : ℤ :=
  (P.darts.map fun d => ((Q.darts.count d : ℕ) : ℤ) - ((Q.darts.count d.symm : ℕ) : ℤ)).sum

theorem walkOverlap_eq_sum {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P Q = (P.darts.map fun d => ((Q.darts.count d : ℕ) : ℤ) - ((Q.darts.count d.symm : ℕ) : ℤ)).sum :=
  rfl

@[simp] theorem walkOverlap_nil_left (u : W) {u' v' : W} (Q : 𝒯.Walk u' v') :
    walkOverlap (SimpleGraph.Walk.nil : 𝒯.Walk u u) Q = 0 := by
  simp [walkOverlap]

@[simp] theorem walkOverlap_nil_right {u v : W} (P : 𝒯.Walk u v) (u' : W) :
    walkOverlap P (SimpleGraph.Walk.nil : 𝒯.Walk u' u') = 0 := by
  simp [walkOverlap]

theorem walkOverlap_cons_left {u v w u' v' : W} (h : 𝒯.Adj u v) (P : 𝒯.Walk v w) (Q : 𝒯.Walk u' v') :
    walkOverlap (SimpleGraph.Walk.cons h P) Q =
      (((Q.darts.count ⟨(u, v), h⟩ : ℕ) : ℤ) - ((Q.darts.count (⟨(u, v), h⟩ : 𝒯.Dart).symm : ℕ) : ℤ)) +
        walkOverlap P Q := by
  simp [walkOverlap]

theorem walkOverlap_append_left {u v w u' v' : W} (P₁ : 𝒯.Walk u v) (P₂ : 𝒯.Walk v w) (Q : 𝒯.Walk u' v') :
    walkOverlap (P₁.append P₂) Q = walkOverlap P₁ Q + walkOverlap P₂ Q := by
  simp [walkOverlap, SimpleGraph.Walk.darts_append, List.sum_append]

theorem walkOverlap_append_right {u v u' v' w' : W} (P : 𝒯.Walk u v) (Q₁ : 𝒯.Walk u' v') (Q₂ : 𝒯.Walk v' w') :
    walkOverlap P (Q₁.append Q₂) = walkOverlap P Q₁ + walkOverlap P Q₂ := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_append, List.count_append, Nat.cast_add, ← WalkOverlapAux.sum_map_add_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  ring

theorem walkOverlap_reverse_left {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P.reverse Q = -walkOverlap P Q := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map,
    ← WalkOverlapAux.sum_map_neg_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  simp only [Function.comp_apply, SimpleGraph.Dart.symm_symm]
  ring

theorem walkOverlap_reverse_right {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P Q.reverse = -walkOverlap P Q := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_reverse, ← WalkOverlapAux.sum_map_neg_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  have h1 : (Q.darts.map SimpleGraph.Dart.symm).reverse.count d = Q.darts.count d.symm := by
    rw [List.count_reverse, ← SimpleGraph.Dart.symm_symm d, List.count_map_of_injective _ _
      SimpleGraph.Dart.symm_involutive.injective, SimpleGraph.Dart.symm_symm]
  have h2 : (Q.darts.map SimpleGraph.Dart.symm).reverse.count d.symm = Q.darts.count d := by
    rw [List.count_reverse, List.count_map_of_injective _ _ SimpleGraph.Dart.symm_involutive.injective]
  rw [h1, h2]
  ring

theorem walkOverlap_map {W' : Type} [DecidableEq W'] {𝒯' : SimpleGraph W'} (f : 𝒯 →g 𝒯')
    (hf : Function.Injective f) {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap (P.map f) (Q.map f) = walkOverlap P Q := by
  have hinj : Function.Injective f.mapDart := WalkOverlapAux.mapDart_injective f hf
  simp only [walkOverlap, SimpleGraph.Walk.darts_map, List.map_map]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  simp only [Function.comp_apply]
  rw [List.count_map_of_injective _ _ hinj, show (f.mapDart d).symm = f.mapDart d.symm from rfl,
    List.count_map_of_injective _ _ hinj]

end Mumford
end CerednikDrinfeld


