-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
-- name    : OAI_GroupTheory_Hyperbolic_Dipoles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:46:43.654286+00:00
-- url     : https://prove2.me/theorems/8b10f1a1-306f-4871-a378-5da048d305f1
-- title:
--   Cancelling dipoles in triangle fillings
-- statement:
--   Pairs of cancelling triangles in a triangle filling, and walks traced by corners.
--
--   1. **Active count.** The active count of a filling is its number of darts in components that meet the boundary.
--   2. **Dipoles.** A dipole in a filling is an embedding of the six darts $0,\dots,5$ of the two-triangle model into interior darts, with the active dart $0$, satisfying:
--   - the face permutation acts on them as $(0\,1\,2)(3\,4\,5)$;
--   - the reverse involution sends dart $0$ to dart $3$, so the two triangles share an edge;
--   - the labels of darts $0,1$ and of $1,2$ have different colours;
--   - the labels are mirrored across the shared edge:
--   $$
--   \mathrm{label}(5)=\mathrm{flip}(\mathrm{label}(1)),\qquad \mathrm{label}(4)=\mathrm{flip}(\mathrm{label}(2)).
--   $$
--   Such a pair of faces cancels; the outside partners of the darts may be connected arbitrarily elsewhere.
--   3. **Triangle embeddings.** If $f^3a=a\ne fa$ then $i\mapsto f^ia$ embeds $\{0,1,2\}$, and two such triangles on different cycles embed $\{0,\dots,5\}$.
--   4. **Cyclic link walks.** If $f:A\to A$ and labels into a graph have each $\mathrm{label}(a)$ adjacent to $\mathrm{label}(fa)$, the successive corners trace a walk of length $n$ from $\mathrm{label}(a)$ to $\mathrm{label}(f^na)$, which need not be simple.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Dipoles.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Dipoles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words

namespace OAI

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def activeCount {w : List E} (D : TriangleFilling flip color face w) : ℕ :=
  (Finset.univ.filter D.Active).card

/-- The six oriented incidences of two faces which cancel across their common
edge. Outside partners may reconnect arbitrarily elsewhere in the filling. -/
structure Dipole {w : List E} (D : TriangleFilling flip color face w) where
  dart : Fin 6 ↪ D.Dart
  next_dart : ∀ j, D.next (dart j) = dart (dipoleFace j)
  reverse_zero : D.reverse (dart 0) = dart 3
  not_boundary : ∀ j, dart j ∉ D.boundary
  active : D.Active (dart 0)
  color10 : color (D.label (dart 1)) ≠ color (D.label (dart 0))
  color21 : color (D.label (dart 2)) ≠ color (D.label (dart 1))
  label51 : D.label (dart 5) = flip (D.label (dart 1))
  label42 : D.label (dart 4) = flip (D.label (dart 2))

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

noncomputable def triangleEmbedding (f : Perm A) (a : A)
    (hp : (f^3) a = a) (hn : f a ≠ a) : Fin 3 ↪ A where
  toFun i := (f^i.val) a
  inj' := by
    intro i j h
    apply Fin.ext
    have hm : Function.minimalPeriod (f : A → A) a = 3 :=
      (orbit_card_eq_minimalPeriod f a).symm.trans (orbit_card_three f a hp hn)
    exact Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) (by rw [hm]; exact i.isLt) (by rw [hm]; exact j.isLt) h

noncomputable def trianglePairEmbedding (f : Perm A) (a b : A)
    (hpa : (f^3) a = a) (hna : f a ≠ a) (hpb : (f^3) b = b) (hnb : f b ≠ b)
    (hab : ¬ f.SameCycle a b) : Fin 6 ↪ A :=
  let ca := triangleEmbedding f a hpa hna
  let cb := triangleEmbedding f b hpb hnb
  let e : Fin 3 ⊕ Fin 3 ↪ A := {
    toFun := Sum.elim ca cb
    inj' := by
      intro i j h
      cases i with
      | inl i => cases j with
        | inl j => exact congrArg Sum.inl (ca.injective h)
        | inr j =>
          change ca i = cb j at h
          have hh : f.SameCycle a b := by
            have hi : f.SameCycle a (ca i) := (Perm.SameCycle.refl f a).pow_right
            have hj : f.SameCycle b (cb j) := (Perm.SameCycle.refl f b).pow_right
            exact hi.trans (by rw [h]; exact hj.symm)
          exact (hab hh).elim
      | inr i => cases j with
        | inl j =>
          change cb i = ca j at h
          have hh : f.SameCycle b a := by
            have hi : f.SameCycle b (cb i) := (Perm.SameCycle.refl f b).pow_right
            have hj : f.SameCycle a (ca j) := (Perm.SameCycle.refl f a).pow_right
            exact hi.trans (by rw [h]; exact hj.symm)
          exact (hab hh.symm).elim
        | inr j => exact congrArg Sum.inr (cb.injective h) }
  finSumFinEquiv.symm.toEmbedding.trans e

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
-- [generator] dropped: variable {w : List E} (D : TriangleFilling flip color face w)

end Release075.TriangleFilling

namespace Release075
namespace CyclicLink
variable {A V : Type*} {G : SimpleGraph V}

/-- The actual link walk traced by successive corners, without assuming its image
is simple. This is why reduced closed walks, rather than only cycles, are needed. -/
def walk (f : A → A) (label : A → V) (adj : ∀ a, G.Adj (label a) (label (f a)))
    (n : ℕ) (a : A) : G.Walk (label a) (label (f^[n] a)) :=
  match n with
  | 0 => .nil
  | n+1 => (walk f label adj n (f a)).cons (adj a)

@[simp] theorem length_walk (f : A → A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a))) (n : ℕ) (a : A) :
    (walk f label adj n a).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [walk,ih]

end CyclicLink
end Release075

end OAI


