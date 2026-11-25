-- Prove2me | Definitions.Def_DetDLP_S8H_NamedWires
-- name    : DetDLP_S8H_NamedWires
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:28:21.47844+00:00
-- url     : https://prove2.me/theorems/854a87e8-c366-4ea3-86a0-c2e54893463c
-- title:
--   Bounded-degree copy cycles for named circuit signals
-- statement:
--   Given a list of gate incidences carrying signal names, form a cyclic permutation on the occurrences of each name. The factor graph obtained by inserting equality checks has satisfying assignments in bijection with valuations of the used names that pass the original gate checks. Original gate degrees are the multiplicities of their incidence labels, and each added equality gate has degree two.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8H_CopyCycle
import Definitions.Def_DetDLP_S8C_LayoutSum

set_option autoImplicit false
namespace DetDLP.S8H.NamedWires
open S8C CopyCycle
attribute [-simp] Fin.natAdd_eq_addNat

variable {n g : ℕ} {K : Type} [DecidableEq K] (name : Fin n → K)

def fiber (k : K) := (List.finRange n).filter fun i => decide (name i = k)

@[simp] theorem mem_fiber {k : K} {i : Fin n} : i ∈ fiber name k ↔ name i = k := by simp [fiber]

theorem fiber_nodup (k : K) : (fiber name k).Nodup := (List.nodup_finRange n).filter _

def next : Equiv.Perm (Fin n) where
  toFun i := (fiber name (name i)).formPerm i
  invFun i := (fiber name (name i)).formPerm.symm i
  left_inv i := by
    have hi : i ∈ fiber name (name i) := by simp
    have he := (mem_fiber name).mp (List.formPerm_apply_mem_of_mem hi)
    simp only [he,Equiv.symm_apply_apply]
  right_inv i := by
    have hi : i ∈ fiber name (name i) := by simp
    have he : (fiber name (name i)).formPerm.symm i ∈ fiber name (name i) := by
      apply List.mem_of_formPerm_apply_mem; simpa using hi
    simp only [(mem_fiber name).mp he,Equiv.apply_symm_apply]

@[local simp] theorem name_next (i : Fin n) : name (next name i) = name i :=
  (mem_fiber name).mp (List.formPerm_apply_mem_of_mem (by simp))

theorem constant {a : Fin n → Bool} (h : ∀ i, a i = a (next name i)) {i j : Fin n}
    (hij : name i = name j) : a i = a j := by
  let l := fiber name (name i)
  have hi : i ∈ l := by simp [l]
  have hj : j ∈ l := by simp [l,hij]
  have hpos : 0 < l.length := List.length_pos_of_mem hi
  have hu (k : ℕ) (hk : k < l.length) : a l[k] = a (l.get ⟨0,hpos⟩) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < l.length := by omega
      have hmem : l[k] ∈ fiber name (name i) := List.getElem_mem hk'
      have hh := h l[k]
      change a l[k] = a ((fiber name (name l[k])).formPerm l[k]) at hh
      rw [(mem_fiber name).mp hmem] at hh
      change a l[k] = a (l.formPerm l[k]) at hh
      rw [List.formPerm_apply_lt_getElem l (fiber_nodup name _) k hk] at hh
      exact hh.symm.trans (ih hk')
  obtain ⟨x,hx,ex⟩ := List.mem_iff_getElem.mp hi
  obtain ⟨y,hy,ey⟩ := List.mem_iff_getElem.mp hj
  exact (congrArg a ex.symm).trans ((hu x hx).trans ((hu y hy).symm.trans (congrArg a ey)))

variable (owner : Fin n → Fin g) (test : (v : Fin g) → ({i // owner i = v} → Bool) → Bool)

abbrev satisfies (x : K → Bool) := ∀ v, test v (fun i => x (name i.val)) = true

/-- Only signal names with an occurrence are counted. Every used signal has one chosen occurrence. -/
def wireEquiv (rep : K → Fin n) (hr : ∀ k, name (rep k) = k) :
    {x // (w3_factorGraph (layout owner (next name))).Satisfies
      (w3_factorChecks _ (checks owner (next name) test)) x} ≃ {x // satisfies name owner test x} := by
  refine (w3_factorEquiv _ _).trans ?_
  refine { toFun := fun a => ⟨fun k => a.1 (rep k),?_⟩,
           invFun := fun x => ⟨x.1 ∘ name,?_⟩,
           left_inv := ?_, right_inv := ?_ }
  · obtain ⟨ht,hn⟩ := (checks_iff owner (next name) test a.1).mp a.2
    intro v
    have he (i : {j // owner j = v}) : a.1 (rep (name i.val)) = a.1 i.val := constant name hn (hr _)
    simpa only [he] using ht v
  · exact (checks_iff owner (next name) test _).mpr ⟨x.2,by simp [Function.comp_def]⟩
  · intro a; apply Subtype.ext; funext i
    exact constant name ((checks_iff owner (next name) test _).mp a.2).2 (hr _)
  · intro x; apply Subtype.ext; funext k; simp [Function.comp_def,hr]

private theorem ranges (a b : ℕ) : List.finRange (a+b) =
    (List.finRange a).map (Fin.castAdd b) ++ (List.finRange b).map (Fin.natAdd a) := by
  have H := @List.ofFn_add (Fin (a+b)) a b id
  simp only [List.ofFn_eq_map,Function.comp_def,id_eq,List.map_id_fun] at H
  exact H

private theorem sep {a b : ℕ} (i : Fin a) (j : Fin b) : Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem oldDegree (v : Fin g) : (w3_factorGraph (layout owner (next name))).deg
    (Fin.castAdd n (Fin.castAdd n v)) = multiplicity owner v := by
  rw [w3_gateDegree]; simp [S8C.multiplicity,layout,ranges n (n+n),ranges n n,List.filter_map,
    Function.comp_def, Ne.symm (sep _ _)]

theorem eqDegree (i : Fin n) : (w3_factorGraph (layout owner (next name))).deg
    (Fin.castAdd n (Fin.natAdd g i)) = 2 := by
  rw [w3_gateDegree]; simp [layout,ranges n (n+n),ranges n n,List.filter_map,
    Function.comp_def,sep]
  let l := (List.finRange n).filter (fun x => decide (x = i))
  have h : l.toFinset = {i} := by ext j; simp [l]
  have nd : l.Nodup := (List.nodup_finRange _).filter _
  change l.length+l.length = 2
  rw [← List.toFinset_card_of_nodup nd,h,Finset.card_singleton]

end DetDLP.S8H.NamedWires


