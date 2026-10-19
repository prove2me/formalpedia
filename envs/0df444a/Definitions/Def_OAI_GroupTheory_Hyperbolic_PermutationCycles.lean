-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
-- name    : OAI_GroupTheory_Hyperbolic_PermutationCycles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:38:31.398393+00:00
-- url     : https://prove2.me/theorems/ba8d24b0-7dc1-420e-afce-d61723dd7db5
-- title:
--   Cycle counts of permutations and the Euler bound for combinatorial maps
-- statement:
--   Cycle counting for permutations $f$ of a finite set $A$, as used for combinatorial maps.
--
--   1. **Cycles.** The cycles of $f$ are the classes of the same-cycle relation, and fixed points count as cycles; $\mathrm{cyc}(f)$ is their number. The orbit of $a$ has size equal to the minimal period of $a$, and $|A|=n\cdot\mathrm{cyc}(f)$ when all orbits have size $n$. A fixed-point-free involution has orbits of size $2$, and a point with $f^3a=a\ne fa$ has an orbit of size $3$. Any function invariant under $f$ descends to the cycles.
--   2. **Swap surgery.** Composing with a transposition $(a\,b)$ merges the cycles of $a$ and $b$ when they differ and splits their common cycle when $a\ne b$ lie on one cycle:
--   $$
--   \mathrm{cyc}\bigl((a\,b)f\bigr)=\mathrm{cyc}(f)\mp1 .
--   $$
--   3. **Components.** For two permutations $f,g$ the components are the classes of the join of their same-cycle relations, counted by $\mathrm{comp}(f,g)$. Joining two classes of a partition loses exactly one class, and the cycles of $fg$ lie inside components.
--   4. **Euler bound.** For any $f,g$, without assuming planarity,
--   $$
--   \mathrm{cyc}(f)+\mathrm{cyc}(g)+\mathrm{cyc}(fg)\le|A|+2\,\mathrm{comp}(f,g).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/PermutationCycles.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/PermutationCycles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace Release075
open scoped BigOperators
open Equiv

namespace PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

abbrev Cycles (f : Perm A) := Quotient (Perm.SameCycle.setoid f)
noncomputable instance (f : Perm A) : Fintype (Cycles f) := Fintype.ofFinite _

def cl (f : Perm A) (a : A) : Cycles f := Quotient.mk _ a

omit [Fintype A] in
@[simp] theorem cl_eq_iff (f : Perm A) (a b : A) :
    cl f a = cl f b ↔ f.SameCycle a b := Quotient.eq

omit [Fintype A] in
theorem cl_surjective (f : Perm A) : Function.Surjective (cl f) := Quotient.mk_surjective

noncomputable def orbit (f : Perm A) (a : A) : Finset A := by
  classical
  exact Finset.univ.filter (f.SameCycle a)

@[simp] theorem mem_orbit (f : Perm A) (a b : A) : b ∈ orbit f a ↔ f.SameCycle a b := by
  classical
  simp [orbit]

theorem orbit_eq_image (f : Perm A) (a : A) {n : ℕ} (hn : 0 < n)
    (hp : (f^n) a = a) :
    orbit f a = Finset.univ.image (fun i : Fin n => (f^i.val) a) := by
  classical
  ext b
  rw [mem_orbit,Finset.mem_image]
  constructor
  · intro hb
    obtain ⟨k,hk⟩ := hb.exists_nat_pow_eq
    refine ⟨⟨k % n,Nat.mod_lt _ hn⟩,Finset.mem_univ _,?_⟩
    have hp' : Function.IsPeriodicPt (f : A → A) n a := by
      change f^[n] a = a
      simpa only [← Perm.coe_pow] using hp
    calc
      (f^(k%n)) a = f^[k%n] a := rfl
      _ = f^[k] a := hp'.iterate_mod_apply k
      _ = b := hk
  · rintro ⟨⟨k,hk⟩,_,rfl⟩
    exact (Perm.sameCycle_pow_right).mpr (Perm.SameCycle.refl f a)

theorem orbit_card_of_period (f : Perm A) (a : A) {n : ℕ} (hn : 0 < n)
    (hp : (f^n) a = a) (hinj : Function.Injective (fun i : Fin n => (f^i.val) a)) :
    (orbit f a).card = n := by
  classical
  rw [orbit_eq_image f a hn hp,Finset.card_image_of_injective _ hinj,Finset.card_univ,
    Fintype.card_fin]

noncomputable def fiberOrbitEquiv (f : Perm A) (a : A) :
    {b : A // cl f b = cl f a} ≃ (orbit f a) where
  toFun b := ⟨b, by simpa only [mem_orbit] using (cl_eq_iff f b a).mp b.property |>.symm⟩
  invFun b := ⟨b, (cl_eq_iff f b a).mpr ((mem_orbit f a b).mp b.property).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fiber (f : Perm A) (a : A) :
    Fintype.card {b : A // cl f b = cl f a} = (orbit f a).card := by
  classical
  simpa only [Fintype.card_coe] using Fintype.card_congr (fiberOrbitEquiv f a)

theorem sum_card_fibers (f : Perm A) :
    (∑ c : Cycles f, Fintype.card {a : A // cl f a = c}) = Fintype.card A := by
  classical
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (cl f))

theorem card_eq_mul_cycles (f : Perm A) (n : ℕ)
    (h : ∀ a, (orbit f a).card = n) :
    Fintype.card A = n * Fintype.card (Cycles f) := by
  classical
  rw [← sum_card_fibers f]
  have hf (c : Cycles f) : Fintype.card {a : A // cl f a = c} = n := by
    obtain ⟨a,rfl⟩ := cl_surjective f c
    rw [card_fiber f a,h a]
  simp [hf,mul_comm]

/-- A fixed-point-free involution has precisely two darts in each edge orbit. -/
theorem orbit_card_involution (f : Perm A) (h : Function.Involutive f)
    (hne : ∀ a, f a ≠ a) (a : A) : (orbit f a).card = 2 := by
  apply orbit_card_of_period f a (by omega : 0 < 2)
  · simpa [pow_two] using h a
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pow_one,pow_zero,eq_comm]

/-- A three-cycle orbit is counted with all corners, not merely its moved support. -/
theorem orbit_card_three (f : Perm A) (a : A) (hp : (f^3) a = a)
    (hne : f a ≠ a) : (orbit f a).card = 3 := by
  apply orbit_card_of_period f a (by omega : 0 < 3) hp
  have h2 : (f^2) a ≠ a := by
    intro he
    have hx := congrArg f he
    have hh : f ((f^2) a) = a := by simpa [pow_succ',Perm.mul_apply] using hp
    rw [hh] at hx
    exact hne hx.symm
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (hne (by simpa using hij.symm))
  · exact False.elim (h2 (by simpa using hij.symm))
  · exact False.elim (hne (by simpa using hij))
  · rfl
  · have hx : f a = f (f a) := by simpa [pow_two] using hij
    exact False.elim (hne (f.injective hx).symm)
  · exact False.elim (h2 (by simpa using hij))
  · have hx : f (f a) = f a := by simpa [pow_two] using hij
    exact False.elim (hne (f.injective hx))
  · rfl

theorem minimalPeriod_pos (f : Perm A) (a : A) :
    0 < Function.minimalPeriod (f : A → A) a :=
  Function.minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts a)

theorem orbit_card_eq_minimalPeriod (f : Perm A) (a : A) :
    (orbit f a).card = Function.minimalPeriod (f : A → A) a := by
  apply orbit_card_of_period f a (minimalPeriod_pos f a)
  · exact Function.iterate_minimalPeriod
  · intro i j hij
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt hij

omit [Fintype A] in
@[simp] theorem cl_apply (f : Perm A) (a : A) : cl f (f a) = cl f a :=
  (cl_eq_iff f _ _).mpr ((Perm.sameCycle_apply_left).mpr (Perm.SameCycle.refl f a))

end PermCycles
end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- Any function invariant under one permutation step is constant on entire
cycles. This includes negative powers without any infinite search. -/
theorem invariant_sameCycle {B : Type*} (f : Perm A) (q : A → B)
    (h : ∀ x, q (f x) = q x) {x y : A} (hxy : f.SameCycle x y) : q x = q y := by
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [pow_succ',Perm.mul_apply,h] using ih

noncomputable def descend {B : Type*} (f : Perm A) (q : A → B)
    (h : ∀ x, q (f x) = q x) : Cycles f → B :=
  Quotient.lift q (fun _ _ hh => invariant_sameCycle f q h hh)

@[simp] theorem descend_cl {B : Type*} (f : Perm A) (q : A → B)
    (h : ∀ x, q (f x) = q x) (a : A) : descend f q h (cl f a) = q a := rfl

/-- Switching the two outgoing cycle destinations joins distinct cycles. This
is the elementary surgery used when gluing or cancelling planar picture arcs. -/
theorem swap_merges (f : Perm A) {a b : A} (hab : ¬ f.SameCycle a b) :
    (Equiv.swap a b * f).SameCycle a b := by
  let g := Equiv.swap a b * f
  let n := Function.minimalPeriod (f : A → A) a
  have hn : 0 < n := minimalPeriod_pos f a
  have ha : (f^n) a = a := Function.iterate_minimalPeriod
  have hnfix (k : ℕ) (hk : 0 < k) (hkn : k < n) : (f^k) a ≠ a := by
    intro he
    have hij := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) hkn hn he
    omega
  have hnb (k : ℕ) : (f^k) a ≠ b := by
    intro he
    apply hab
    exact he ▸ ((Perm.sameCycle_pow_right).mpr (Perm.SameCycle.refl f a))
  have hm (k : ℕ) (hk : k < n) : (g^k) a = (f^k) a := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',Perm.mul_apply,ih (by omega),pow_succ',Perm.mul_apply]
      change Equiv.swap a b (f ((f^k) a)) = f ((f^k) a)
      apply Equiv.swap_apply_of_ne_of_ne
      · simpa only [pow_succ',Perm.mul_apply] using hnfix (k+1) (by omega) hk
      · simpa only [pow_succ',Perm.mul_apply] using hnb (k+1)
  have hg : (g^n) a = b := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [hk,pow_succ',Perm.mul_apply,hm k (by omega)]
    change Equiv.swap a b (f ((f^k) a)) = b
    have hh : f ((f^k) a) = a := by simpa only [hk,pow_succ',Perm.mul_apply] using ha
    rw [hh,Equiv.swap_apply_left]
  exact ⟨(n : ℤ), by simpa only [zpow_natCast] using hg⟩

theorem old_cycles_of_swap_merged (f : Perm A) (a b : A)
    (hm : (Equiv.swap a b * f).SameCycle a b) {x y : A}
    (hxy : f.SameCycle x y) : (Equiv.swap a b * f).SameCycle x y := by
  let g := Equiv.swap a b * f
  have step (z : A) : cl g (f z) = cl g z := by
    have hz := cl_apply g z
    change cl g (Equiv.swap a b (f z)) = cl g z at hz
    by_cases ha : f z = a
    · rw [ha,Equiv.swap_apply_left] at hz
      rw [ha]
      exact ((cl_eq_iff g a b).mpr hm).trans hz
    by_cases hb : f z = b
    · rw [hb,Equiv.swap_apply_right] at hz
      rw [hb]
      exact ((cl_eq_iff g a b).mpr hm).symm.trans hz
    · simpa only [Equiv.swap_apply_of_ne_of_ne ha hb] using hz
  exact (cl_eq_iff g x y).mp (invariant_sameCycle f (cl g) step hxy)

theorem card_subtype_ne_add_one {C : Type*} [Fintype C] (c : C) :
    Nat.card {x : C // x ≠ c} + 1 = Fintype.card C := by
  classical
  have he : Finset.univ.filter (fun x : C => x ≠ c) = Finset.univ.erase c := by
    ext x
    simp
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,he]
  simpa only [Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ c)

/-- Exact cycle count for merging two different cycles by one swap. Fixed points
are included in the count, unlike the support-cycle count in permutation sign. -/
theorem cycles_card_swap_of_not_same (f : Perm A) {a b : A} (hab : ¬ f.SameCycle a b) :
    Fintype.card (Cycles (Equiv.swap a b * f)) + 1 = Fintype.card (Cycles f) := by
  let g := Equiv.swap a b * f
  have hm : g.SameCycle a b := swap_merges f hab
  have hc : cl f a ≠ cl f b := fun h => hab ((cl_eq_iff f a b).mp h)
  let collapse : Cycles f → Cycles f := fun c => if c = cl f b then cl f a else c
  have ha : collapse (cl f a) = cl f a := by simp [collapse]
  have hb : collapse (cl f b) = cl f a := by simp [collapse]
  have hne (c : Cycles f) : collapse c ≠ cl f b := by
    by_cases h : c = cl f b
    · simpa only [collapse,ite_eq_left h] using hc
    · simpa only [collapse,ite_eq_right h] using h
  have hswap (z : A) : collapse (cl f (Equiv.swap a b z)) = collapse (cl f z) := by
    by_cases hza : z = a
    · subst z; simp only [Equiv.swap_apply_left,ha,hb]
    by_cases hzb : z = b
    · subst z; simp only [Equiv.swap_apply_right,ha,hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hza hzb]
  let q : A → {c : Cycles f // c ≠ cl f b} := fun x => ⟨collapse (cl f x),hne _⟩
  have hq (x : A) : q (g x) = q x := by
    apply Subtype.ext
    change collapse (cl f (Equiv.swap a b (f x))) = collapse (cl f x)
    rw [hswap,cl_apply]
  let Q := descend g q hq
  let j : Cycles f → Cycles g := Quotient.lift (cl g) (by
    intro x y h
    exact (cl_eq_iff g x y).mpr (old_cycles_of_swap_merged f a b hm h))
  have hj : j (cl f a) = j (cl f b) := (cl_eq_iff g a b).mpr hm
  have hjc (c : Cycles f) : j (collapse c) = j c := by
    by_cases h : c = cl f b
    · simpa [collapse,h] using hj
    · simp only [collapse,ite_eq_right h]
  have hleft : Function.LeftInverse (fun c => j c.val) Q := by
    intro c
    induction c using Quotient.inductionOn with
    | h x => exact hjc (cl f x)
  have hsurj : Function.Surjective Q := by
    intro c
    obtain ⟨x,hx⟩ := cl_surjective f c.val
    refine ⟨cl g x,?_⟩
    apply Subtype.ext
    change collapse (cl f x) = c.val
    rw [hx]
    simp only [collapse,ite_eq_right c.property]
  have hcard := Fintype.card_congr (Equiv.ofBijective Q ⟨hleft.injective,hsurj⟩)
  rw [hcard]
  rw [← Nat.card_eq_fintype_card]
  exact card_subtype_ne_add_one (cl f b)

/-- Switching the destinations within one cycle cuts it into two. The proof
uses the initial orbit segment from `a` to `b`, rather than assuming an
unproved topological separation statement. -/
theorem swap_splits (f : Perm A) {a b : A} (hne : a ≠ b) (hab : f.SameCycle a b) :
    ¬ (Equiv.swap a b * f).SameCycle a b := by
  let n := Function.minimalPeriod (f : A → A) a
  have hn : 0 < n := minimalPeriod_pos f a
  have hp : (f^n) a = a := Function.iterate_minimalPeriod
  have hb : b ∈ orbit f a := (mem_orbit f a b).mpr hab
  rw [orbit_eq_image f a hn hp,Finset.mem_image] at hb
  obtain ⟨⟨k,hkn⟩,_,hk⟩ := hb
  have hk0 : 0 < k := by
    by_contra hh
    have hz : k = 0 := by omega
    simp only [hz,pow_zero,Perm.one_apply] at hk
    exact hne hk
  have hfb (j : ℕ) (hjk : j < k) : (f^j) a ≠ b := by
    intro hj
    have he : (f^j) a = (f^k) a := hj.trans hk.symm
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) (by omega : j < n) hkn he
    omega
  have hfa (j : ℕ) (hj : 0 < j) (hjk : j < k) : (f^j) a ≠ a := by
    intro he
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) (by omega : j < n) hn he
    omega
  let g := Equiv.swap a b * f
  have hgf (j : ℕ) (hjk : j < k) : (g^j) a = (f^j) a := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ',Perm.mul_apply,ih (by omega),pow_succ',Perm.mul_apply]
      change Equiv.swap a b (f ((f^j) a)) = f ((f^j) a)
      apply Equiv.swap_apply_of_ne_of_ne
      · simpa only [pow_succ',Perm.mul_apply] using hfa (j+1) (by omega) hjk
      · simpa only [pow_succ',Perm.mul_apply] using hfb (j+1) hjk
  have hgk : (g^k) a = a := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [pow_succ',Perm.mul_apply,hgf j (by omega)]
    change Equiv.swap a b (f ((f^j) a)) = a
    have hh : f ((f^j) a) = b := by simpa only [pow_succ',Perm.mul_apply] using hk
    rw [hh,Equiv.swap_apply_right]
  intro hgab
  have hmem := (mem_orbit g a b).mpr hgab
  rw [orbit_eq_image g a hk0 hgk,Finset.mem_image] at hmem
  obtain ⟨⟨j,hjk⟩,_,hj⟩ := hmem
  exact hfb j hjk ((hgf j hjk).symm.trans hj)

theorem cycles_card_swap_of_same (f : Perm A) {a b : A} (hne : a ≠ b)
    (hab : f.SameCycle a b) :
    Fintype.card (Cycles (Equiv.swap a b * f)) = Fintype.card (Cycles f) + 1 := by
  have h := cycles_card_swap_of_not_same (Equiv.swap a b * f) (swap_splits f hne hab)
  have he : Equiv.swap a b * (Equiv.swap a b * f) = f := by
    rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
  rw [he] at h
  exact h.symm

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- Join just two classes of a partition. -/
def joinPair (s : Setoid A) (a b : A) : Setoid A :=
  Relation.EqvGen.setoid (fun x y => s x y ∨ (x = a ∧ y = b))

omit [Fintype A] in
theorem le_joinPair (s : Setoid A) (a b : A) : s ≤ joinPair s a b :=
  fun x y h => Relation.EqvGen.rel x y (Or.inl h)

omit [Fintype A] in
theorem joinPair_rel (s : Setoid A) (a b : A) : joinPair s a b a b :=
  Relation.EqvGen.rel a b (Or.inr ⟨rfl,rfl⟩)

omit [Fintype A] in
theorem joinPair_le {s t : Setoid A} {a b : A} (h : s ≤ t) (hab : t a b) :
    joinPair s a b ≤ t := by
  apply Setoid.eqvGen_le
  intro x y hh
  rcases hh with hh | ⟨rfl,rfl⟩
  · exact h hh
  · exact hab

omit [Fintype A] in
theorem joinPair_eq_of_rel (s : Setoid A) {a b : A} (hab : s a b) :
    joinPair s a b = s := le_antisymm (joinPair_le le_rfl hab) (le_joinPair s a b)

/-- The exact loss of one component when two distinct classes are joined. -/
theorem card_joinPair (s : Setoid A) {a b : A} (hab : ¬ s a b) :
    Nat.card (Quotient (joinPair s a b)) + 1 = Nat.card (Quotient s) := by
  let : Fintype (Quotient s) := Fintype.ofFinite _
  let : Fintype (Quotient (joinPair s a b)) := Fintype.ofFinite _
  let c : A → Quotient s := Quotient.mk s
  have hc : c a ≠ c b := fun h => hab (Quotient.exact h)
  let collapse : Quotient s → Quotient s := fun v => if v = c b then c a else v
  have hne (v : Quotient s) : collapse v ≠ c b := by
    by_cases h : v = c b
    · simpa only [collapse,ite_eq_left h] using hc
    · simpa only [collapse,ite_eq_right h] using h
  let q : A → {v : Quotient s // v ≠ c b} := fun x => ⟨collapse (c x),hne _⟩
  have hq : joinPair s a b ≤ Setoid.ker q := by
    apply joinPair_le
    · intro x y h
      apply Subtype.ext
      change collapse (c x) = collapse (c y)
      rw [show c x = c y from Quotient.sound h]
    · apply Subtype.ext
      change collapse (c a) = collapse (c b)
      simp [collapse]
  let Q : Quotient (joinPair s a b) → {v : Quotient s // v ≠ c b} :=
    Quotient.lift q (fun _ _ h => hq h)
  let j : Quotient s → Quotient (joinPair s a b) := Setoid.map_of_le (le_joinPair s a b)
  have hj : j (c a) = j (c b) := Quotient.sound (joinPair_rel s a b)
  have hjc (v : Quotient s) : j (collapse v) = j v := by
    by_cases h : v = c b
    · simpa [collapse,h] using hj
    · simp only [collapse,ite_eq_right h]
  have hleft : Function.LeftInverse (fun v => j v.val) Q := by
    intro v
    induction v using Quotient.inductionOn with
    | h x => exact hjc (c x)
  have hsurj : Function.Surjective Q := by
    intro v
    obtain ⟨x,hx⟩ := Quotient.mk_surjective v.val
    refine ⟨Quotient.mk _ x,?_⟩
    apply Subtype.ext
    change collapse (c x) = v.val
    rw [show c x = v.val from hx]
    simp only [collapse,ite_eq_right v.property]
  rw [Nat.card_congr (Equiv.ofBijective Q ⟨hleft.injective,hsurj⟩)]
  simpa only [Nat.card_eq_fintype_card] using card_subtype_ne_add_one (c b)

/-- Components of the graph generated by two permutations; cycles of their
product are contained in these components. -/
abbrev components (f g : Perm A) : Setoid A :=
  Perm.SameCycle.setoid f ⊔ Perm.SameCycle.setoid g

noncomputable def cycleCount (f : Perm A) : ℕ := Nat.card (Cycles f)
noncomputable def componentCount (f g : Perm A) : ℕ := Nat.card (Quotient (components f g))

theorem sameCycle_le_of_step (f : Perm A) (s : Setoid A) (h : ∀ a, s a (f a)) :
    Perm.SameCycle.setoid f ≤ s := by
  intro x y hxy
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact s.refl x
  | succ n ih =>
    rw [pow_succ',Perm.mul_apply]
    exact s.trans ih (h _)

theorem sameCycle_mul_le_components (f g : Perm A) :
    Perm.SameCycle.setoid (f*g) ≤ components f g := by
  apply sameCycle_le_of_step
  intro a
  exact (components f g).trans
    ((show Perm.SameCycle.setoid g ≤ components f g from le_sup_right)
      ((Perm.sameCycle_apply_right).mpr (Perm.SameCycle.refl g a)))
    ((show Perm.SameCycle.setoid f ≤ components f g from le_sup_left)
      ((Perm.sameCycle_apply_right).mpr (Perm.SameCycle.refl f (g a))))

theorem components_swap_of_not_same (f g : Perm A) {a b : A}
    (hab : ¬ f.SameCycle a b) :
    components (Equiv.swap a b * f) g = joinPair (components f g) a b := by
  let t := joinPair (components f g) a b
  have oldle : components f g ≤ t := le_joinPair _ a b
  have hswap (z : A) : t z (Equiv.swap a b z) := by
    by_cases ha : z = a
    · subst z
      rw [Equiv.swap_apply_left]
      exact joinPair_rel _ a b
    by_cases hb : z = b
    · subst z
      rw [Equiv.swap_apply_right]
      exact t.symm (joinPair_rel _ a b)
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  apply le_antisymm
  · apply sup_le
    · apply sameCycle_le_of_step
      intro z
      exact t.trans (oldle ((show Perm.SameCycle.setoid f ≤ components f g from le_sup_left)
        ((Perm.sameCycle_apply_right).mpr (Perm.SameCycle.refl f z)))) (hswap (f z))
    · exact le_trans le_sup_right oldle
  · apply joinPair_le
    · apply sup_le
      · intro x y hxy
        exact (show Perm.SameCycle.setoid (Equiv.swap a b * f) ≤
          components (Equiv.swap a b * f) g from le_sup_left)
          (old_cycles_of_swap_merged f a b (swap_merges f hab) hxy)
      · exact le_sup_right
    · exact (show Perm.SameCycle.setoid (Equiv.swap a b * f) ≤
        components (Equiv.swap a b * f) g from le_sup_left) (swap_merges f hab)

theorem cycleCount_one : cycleCount (1 : Perm A) = Fintype.card A := by
  have hinj : Function.Injective (cl (1 : Perm A)) := by
    intro x y h
    exact Perm.sameCycle_one.mp ((cl_eq_iff 1 x y).mp h)
  have hh := Nat.card_congr (Equiv.ofBijective (cl (1 : Perm A)) ⟨hinj,cl_surjective 1⟩)
  simpa only [cycleCount,Nat.card_eq_fintype_card] using hh.symm

omit [Fintype A] in
theorem components_one (g : Perm A) : components 1 g = Perm.SameCycle.setoid g := by
  apply sup_eq_right.mpr
  intro x y h
  have he := Perm.sameCycle_one.mp h
  subst y
  exact Perm.SameCycle.refl g x

omit [Fintype A] in
theorem componentCount_one (g : Perm A) : componentCount 1 g = cycleCount g := by
  simp only [componentCount,components_one,cycleCount,Cycles]

theorem cycleCount_swap_of_not_same (f : Perm A) {a b : A} (hab : ¬ f.SameCycle a b) :
    cycleCount (Equiv.swap a b * f) + 1 = cycleCount f := by
  simpa only [cycleCount,Nat.card_eq_fintype_card] using cycles_card_swap_of_not_same f hab

theorem cycleCount_swap_le (f : Perm A) (a b : A) :
    cycleCount (Equiv.swap a b * f) ≤ cycleCount f + 1 := by
  by_cases h : a = b
  · subst b
    simp only [Equiv.swap_self]
    change cycleCount (1*f) ≤ cycleCount f + 1
    rw [one_mul]
    omega
  by_cases hab : f.SameCycle a b
  · have hs := cycles_card_swap_of_same f h hab
    simpa only [cycleCount,Nat.card_eq_fintype_card] using hs.le
  · have hs := cycleCount_swap_of_not_same f hab
    omega

/-- Euler's upper bound for an arbitrary oriented combinatorial map, allowing
multiple components and positive genus. No planarity theorem is assumed. -/
theorem euler_bound (f g : Perm A) :
    cycleCount f + cycleCount g + cycleCount (f*g) ≤
      Fintype.card A + 2 * componentCount f g := by
  generalize hn : f.support.card = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hf : f = 1
    · subst f
      simp only [cycleCount_one,one_mul,componentCount_one]
      omega
    have hex : ∃ x, f x ≠ x := by
      by_contra hh
      push Not at hh
      exact hf (Equiv.ext hh)
    obtain ⟨x,hx⟩ := hex
    let f' := Equiv.swap x (f x) * f
    have hsm : f.SameCycle x (f x) :=
      Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f x)
    have hns : ¬ f'.SameCycle x (f x) := swap_splits f hx.symm hsm
    have hdec : f'.support.card < n := by
      rw [← hn]
      exact Perm.card_support_swap_mul hx
    have hi := ih _ hdec (f := f') rfl
    have hret : Equiv.swap x (f x) * f' = f := by
      dsimp [f']
      rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hc : cycleCount f + 1 = cycleCount f' := by
      have h := cycleCount_swap_of_not_same f' hns
      rwa [hret] at h
    have hj : components f g = joinPair (components f' g) x (f x) := by
      have h := components_swap_of_not_same f' g hns
      rwa [hret] at h
    have hprod : Equiv.swap x (f x) * (f'*g) = f*g := by rw [← mul_assoc,hret]
    by_cases hxy : components f' g x (f x)
    · have hcomp : componentCount f g = componentCount f' g := by
        simp only [componentCount,hj,joinPair_eq_of_rel _ hxy]
      have hp := cycleCount_swap_le (f'*g) x (f x)
      rw [hprod] at hp
      omega
    · have hcomp : componentCount f g + 1 = componentCount f' g := by
        simpa only [componentCount,hj] using card_joinPair (components f' g) hxy
      have hnp : ¬ (f'*g).SameCycle x (f x) := fun h =>
        hxy (sameCycle_mul_le_components f' g h)
      have hp := cycleCount_swap_of_not_same (f'*g) hnp
      rw [hprod] at hp
      omega

end Release075.PermCycles

end OAI


