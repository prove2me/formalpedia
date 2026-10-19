-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
-- name    : OAI_Combinatorics_Hamiltonian_CycleReversal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:30:37.638478+00:00
-- url     : https://prove2.me/theorems/e6f7f427-3971-45e9-bd8d-c4a57b99b977
-- title:
--   Opposite cycles of a state and the reversal involution on its partner states
-- statement:
--   Let $T$ be a triangle system: a family of triangles indexed by a set $A$, where each $a \in A$ has an injective corner labelling $i \mapsto v_a(i) \in V$, $i \in \mathbb{Z}/3$, and no two distinct triangles share two corners. For $X \subseteq V$, a state is a corner choice $s : A \to \mathbb{Z}/3$ such that $a \mapsto \bar s(a) := v_a(s(a))$ is a bijection $A \to X$, and two states $r, s$ are partners if $r(a) \neq s(a)$ for all $a$. The opposite graph of $s$ joins two distinct vertices when they are corners of a common triangle $a$ and both differ from the chosen corner $\bar s(a)$. For $i \neq j$ in $\mathbb{Z}/3$, $\theta(i, j) = -(i + j)$ is the remaining index.
--
--   1. **Opposite cycle.** An opposite cycle of a state $s$ is a cycle $x_0, \dots, x_{m-1}$ in the opposite graph of $s$ ($m \geq 3$, distinct vertices, $x_i$ adjacent to $x_{i+1}$, indices mod $m$) together with pairwise distinct triangles $a_0, \dots, a_{m-1}$ and corner indices $\ell_i, \rho_i \in \mathbb{Z}/3$ such that
--   $$
--   v_{a_i}(\ell_i) = x_i, \qquad v_{a_i}(\rho_i) = x_{i+1}, \qquad \ell_i \neq s(a_i), \qquad \rho_i \neq s(a_i).
--   $$
--   Each step of the cycle thus runs along the side of $a_i$ opposite to the corner chosen by $s$; necessarily $\ell_i \neq \rho_i$.
--
--   2. **Behaviour of partners.** If $r$ is a partner of $s$, then for each $i$ the corner $\bar r(a_i)$ is one of $x_i, x_{i+1}$ and the third corner $v_{a_i}(\theta(r(a_i), s(a_i)))$ is the other one. Moreover the choice is coherent around the cycle: either $\bar r(a_i) = x_i$ for all $i$, or $\bar r(a_i) = x_{i+1}$ for all $i$.
--
--   3. **Reversal.** For a partner $r$ of $s$, the reversed corner choice changes $r$ exactly on the triangles of the cycle:
--   $$
--   r^{C}(a) = \begin{cases} \theta\bigl(r(a), s(a)\bigr) & \text{if } a = a_i \text{ for some } i, \\ r(a) & \text{otherwise.} \end{cases}
--   $$
--   Its chosen corners are those of $r$ shifted by one step along the cycle: there is a permutation $\pi$ of $A$ with $v_a(r^C(a)) = \bar r(\pi(a))$ for all $a$. Hence $r^C$ is again a state with target $X$; it is again a partner of $s$, and $(r^C)^C = r$.
--
--   4. **Reversal map on partners.** $\operatorname{Partners}(s)$ is the set of states that are partners of $s$, and $r \mapsto r^C$ is an involution of $\operatorname{Partners}(s)$ determined by the opposite cycle $C$.
--
--   Reversing the choices of a partner along an opposite cycle of $s$ is the pairing behind a cancellation argument: under a condition on the index steps along the cycle, the phase-weighted sum over all partners of $s$ vanishes. In this way the contribution of a state whose opposite graph contains a cycle can be shown to cancel.
--
--   **Formalization Note** `OppositeCycle s` has fields `cycle : CycleCoordinates (T.oppositeGraph s)`, an embedding `face`, `leftCorner`, `rightCorner` and the four conditions above. The lemmas are `corner_ne`, `partner_endpoints`, `partner_orientation` and `changed_assignment_permutation`; the corner choice is `changedCorners`, the reversed state is `reverse` (with `reverse_val`, `reverse_partner`, `reverse_reverse`), `Partners s` is a subtype of states, and `reversal` is the induced map on it. Two private lemmas about `ite` are local rewriting helpers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CycleReversal.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CycleReversal.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Reversal involutions on partners of a fixed incidence state. -/

namespace Barnette

open Fin.NatCast

variable {V : Type*} {G : SimpleGraph V}

namespace TriangleSystem

variable {A : Type*} (T : TriangleSystem A V) {X : Set V}

structure OppositeCycle (s : T.State X) where
  cycle : CycleCoordinates (T.oppositeGraph s)
  face : Fin (cycle.n + 3) ↪ A
  leftCorner : Fin (cycle.n + 3) → Fin 3
  rightCorner : Fin (cycle.n + 3) → Fin 3
  left_eq : ∀ i, T.vertex (face i) (leftCorner i) = cycle.vertex i
  right_eq : ∀ i, T.vertex (face i) (rightCorner i) = cycle.vertex (i + 1)
  left_ne : ∀ i, leftCorner i ≠ s.val (face i)
  right_ne : ∀ i, rightCorner i ≠ s.val (face i)

namespace OppositeCycle

variable {T} {s r : T.State X} (C : T.OppositeCycle s)

theorem corner_ne (i : Fin (C.cycle.n + 3)) : C.leftCorner i ≠ C.rightCorner i := by
  intro h
  have heq : C.cycle.vertex i = C.cycle.vertex (i + 1) :=
    (C.left_eq i).symm.trans (h ▸ C.right_eq i)
  apply cyclic_one_ne_zero C.cycle.n
  exact add_left_cancel (by simpa using (C.cycle.vertex.injective heq).symm : i + 1 = i + 0)

theorem partner_endpoints (hrs : T.Partner r s) (i : Fin (C.cycle.n + 3)) :
    (r.value (C.face i) = C.cycle.vertex i ∧
      T.vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
        C.cycle.vertex (i + 1)) ∨
    (r.value (C.face i) = C.cycle.vertex (i + 1) ∧
      T.vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
        C.cycle.vertex i) := by
  have hne : r.val (C.face i) ≠ s.val (C.face i) :=
    fun h => hrs _ ((State.value_eq_iff r s _).mpr h)
  have h := other_corners (C.leftCorner i) (C.rightCorner i)
    (r.val (C.face i)) (s.val (C.face i)) (C.corner_ne i) (C.left_ne i) (C.right_ne i) hne
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    exact ⟨by change T.vertex _ _ = _; rw [← h₁, C.left_eq],
      by rw [← h₂, C.right_eq]⟩
  · right
    exact ⟨by change T.vertex _ _ = _; rw [← h₁, C.right_eq],
      by rw [← h₂, C.left_eq]⟩

theorem partner_orientation (hrs : T.Partner r s) :
    (∀ i, r.value (C.face i) = C.cycle.vertex i) ∨
      (∀ i, r.value (C.face i) = C.cycle.vertex (i + 1)) := by
  apply C.cycle.tail_orientation C.face r.value r.value_injective
  intro i
  exact (C.partner_endpoints hrs i).imp And.left And.left

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette.TriangleSystem

open Fin.NatCast

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V} {s : T.State X}

namespace OppositeCycle

variable (C : T.OppositeCycle s)

noncomputable def changedCorners (r : T.State X) (t : A) : Fin 3 := by
  classical
  exact if t ∈ Set.range C.face then thirdIndex (r.val t) (s.val t) else r.val t

@[simp] theorem changedCorners_image (r : T.State X) (i : Fin (C.cycle.n + 3)) :
    C.changedCorners r (C.face i) = thirdIndex (r.val (C.face i)) (s.val (C.face i)) := by
  classical
  simp [changedCorners]

theorem changed_assignment_permutation (r : T.State X) (hrs : T.Partner r s) :
    ∃ e : Equiv.Perm A, ∀ t, T.vertex t (C.changedCorners r t) = r.value (e t) := by
  classical
  let f := Equiv.ofInjective C.face C.face.injective
  rcases C.partner_orientation hrs with hforward | hbackward
  · let e := (Equiv.addRight (1 : Fin (C.cycle.n + 3))).extendDomain f
    refine ⟨e, ?_⟩
    intro t
    by_cases ht : t ∈ Set.range C.face
    · obtain ⟨i, rfl⟩ := ht
      have he : e (C.face i) = C.face (i + 1) := by
        exact (Equiv.Perm.extendDomain_apply_image _ f i)
      rw [C.changedCorners_image, he, hforward]
      rcases C.partner_endpoints hrs i with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact ((C.cycle.adjacent i).1 ((hforward i).symm.trans h)).elim
    · rw [changedCorners, ite_eq_right ht, Equiv.Perm.extendDomain_apply_not_subtype _ f ht]
      rfl
  · let e := (Equiv.addRight (-1 : Fin (C.cycle.n + 3))).extendDomain f
    refine ⟨e, ?_⟩
    intro t
    by_cases ht : t ∈ Set.range C.face
    · obtain ⟨i, rfl⟩ := ht
      have he : e (C.face i) = C.face (i - 1) := by
        calc
          e (C.face i) = C.face (i + (-1 : Fin (C.cycle.n + 3))) :=
            Equiv.Perm.extendDomain_apply_image _ f i
          _ = C.face (i - 1) := congrArg C.face (sub_eq_add_neg i 1).symm
      rw [C.changedCorners_image, he, hbackward, sub_add_cancel]
      rcases C.partner_endpoints hrs i with ⟨h, _⟩ | ⟨_, h⟩
      · exact ((C.cycle.adjacent i).1 (h.symm.trans (hbackward i))).elim
      · exact h
    · rw [changedCorners, ite_eq_right ht, Equiv.Perm.extendDomain_apply_not_subtype _ f ht]
      rfl

noncomputable def reverse (r : T.State X) (hrs : T.Partner r s) : T.State X := by
  let e := (C.changed_assignment_permutation r hrs).choose
  have he : ∀ t, T.vertex t (C.changedCorners r t) = r.value (e t) :=
    (C.changed_assignment_permutation r hrs).choose_spec
  refine ⟨C.changedCorners r, ?_, ?_⟩
  · intro t u h
    change T.vertex t (C.changedCorners r t) = T.vertex u (C.changedCorners r u) at h
    rw [he t, he u] at h
    exact e.injective (r.value_injective h)
  · calc
      Set.range (fun t => T.vertex t (C.changedCorners r t)) = Set.range r.value := by
        ext v
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨e t, (he t).symm⟩
        · rintro ⟨u, rfl⟩
          refine ⟨e.symm u, ?_⟩
          change T.vertex (e.symm u) (C.changedCorners r (e.symm u)) = r.value u
          rw [he, e.apply_symm_apply]
      _ = X := r.value_range

@[simp] theorem reverse_val (r : T.State X) (hrs : T.Partner r s) :
    (C.reverse r hrs).val = C.changedCorners r := rfl

theorem reverse_partner (r : T.State X) (hrs : T.Partner r s) :
    T.Partner (C.reverse r hrs) s := by
  classical
  intro t h
  have hi : C.changedCorners r t = s.val t :=
    T.vertex_injective t h
  by_cases ht : t ∈ Set.range C.face
  · rw [changedCorners, ite_eq_left ht] at hi
    have hne : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
    exact (thirdIndex_distinct _ _ hne).2 hi
  · rw [changedCorners, ite_eq_right ht] at hi
    exact hrs t ((State.value_eq_iff r s t).mpr hi)

@[simp] theorem reverse_reverse (r : T.State X) (hrs : T.Partner r s) :
    C.reverse (C.reverse r hrs) (C.reverse_partner r hrs) = r := by
  classical
  apply Subtype.ext
  funext t
  change C.changedCorners (C.reverse r hrs) t = r.val t
  by_cases ht : t ∈ Set.range C.face
  · simp only [changedCorners, ht, ite_true, reverse_val, thirdIndex_involution]
  · simp only [changedCorners, ht, ite_false, reverse_val]

end OppositeCycle

def Partners (s : T.State X) := {r : T.State X // T.Partner r s}

namespace OppositeCycle

variable (C : T.OppositeCycle s)

noncomputable def reversal (r : T.Partners s) : T.Partners s :=
  ⟨C.reverse r.val r.property, C.reverse_partner r.val r.property⟩

end OppositeCycle
end Barnette.TriangleSystem

end OAI


