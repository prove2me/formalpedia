-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
-- name    : OAI_Combinatorics_Hamiltonian_PairPhases
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:32:35.545717+00:00
-- url     : https://prove2.me/theorems/f088c5f8-b9a5-4857-89e4-a902c556863d
-- title:
--   Phases, partner pairs of states, cycle classes of permutations, and cycle-wise flips
-- statement:
--   Let $T$ be a triangle system on a vertex set $V$ indexed by a set $A$: each $a \in A$ has an injective corner labelling $i \mapsto v_a(i)$, $i \in \mathbb{Z}/3$, and no two distinct triangles share two corners. For $X \subseteq V$, a state is a corner choice $s : A \to \mathbb{Z}/3$ such that $\bar s(a) := v_a(s(a))$ defines a bijection $\bar s : A \to X$; states $r, s$ are partners if $r(a) \neq s(a)$ for all $a$. Let $\theta(i, j) = -(i + j)$ (the third index when $i \neq j$), and let $\delta(i, j) \in \mathbb{Z}$ be $0$ if $i = j$, $1$ if $j = i + 1$ and $-1$ if $j = i - 1$.
--
--   1. **Phase and index sums.** For $n \in \mathbb{Z}$ the phase is
--   $$
--   \operatorname{ph}(n) = \mathrm{i}^{\lfloor n/3 \rfloor} \in \mathbb{C},
--   $$
--   where $\mathrm{i}$ is the imaginary unit. For finite $A$ and states $r, s$, the raw index sum is $\Sigma(r, s) = \sum_{a \in A} \delta(r(a), s(a))$. The opposite graph of $s$ joins distinct vertices that are corners of a common triangle $a$ other than $\bar s(a)$; for an opposite cycle $C$ of $s$, i.e. a cycle $x_0, \dots, x_{m-1}$ ($m \geq 3$) in this graph whose step from $x_i$ to $x_{i+1}$ is realised by distinct triangles $a_i$ having $x_i, x_{i+1}$ as corners different from $\bar s(a_i)$, the face set is $\{a_0, \dots, a_{m-1}\}$ and the cyclic delta of a state $r$ is $\sum_{i} \delta\bigl(r(a_i), \theta(r(a_i), s(a_i))\bigr)$.
--
--   2. **Cycle classes of a permutation.** For a permutation $p$ of $A$, the cycle classes are the classes of the equivalence relation "$b = p^k(a)$ for some $k \in \mathbb{Z}$", and $[a]_p$ denotes the class of $a$; thus $[p(a)]_p = [a]_p$. For finite $A$, a function $f$ on $A$ with $f(p(a)) = f(a)$ for all $a$ is constant on cycle classes and descends to them. If $b : A \to \{\text{true}, \text{false}\}$ is $p$-invariant, the partial permutation of $p$ along $b$ applies $p$ where $b$ is true and fixes every other point.
--
--   3. **Pairs and the successor permutation.** A pair is an ordered pair $P = (r, s)$ of partner states with target $X$. Its successor permutation $\nu_P = \bar r^{-1} \circ \bar s$ of $A$ is characterised by
--   $$
--   \bar r(\nu_P(a)) = \bar s(a) \qquad \text{for all } a \in A,
--   $$
--   and has no fixed points. The third-corner function of $P$ is $a \mapsto \theta(r(a), s(a))$, and the group of $P$ is the set of all pairs whose third-corner function equals that of $P$.
--
--   4. **Flips.** If $b : A \to \{\text{true}, \text{false}\}$ is invariant under $\nu_P$, flipping $P$ along $b$ swaps the two choices on the triangles where $b$ is true:
--   $$
--   r'(a) = \begin{cases} s(a) & \text{if } b(a), \\ r(a) & \text{otherwise}, \end{cases} \qquad s'(a) = \begin{cases} r(a) & \text{if } b(a), \\ s(a) & \text{otherwise}. \end{cases}
--   $$
--   The invariance guarantees that $r'$ and $s'$ are states again: their chosen corners are those of $r$ and $s$ composed with the partial permutations of $\nu_P$ and $\nu_P^{-1}$ along $b$ (in general, a corner choice $c$ with $v_a(c(a)) = \bar s(\pi(a))$ for a state $s$ and a permutation $\pi$ of $A$ is a state). The flipped pair $(r', s')$ is again a pair and lies in the group of $P$.
--
--   5. **Parametrisation of a group.** For finite $A$, every pair in the group of $P$ arises from $P$ by flipping along a unique union of cycle classes of $\nu_P$: flipping gives a bijection
--   $$
--   \{\text{true}, \text{false}\}^{A/\langle \nu_P \rangle} \xrightarrow{\ \sim\ } \operatorname{Group}(P),
--   $$
--   where $A/\langle \nu_P \rangle$ is the set of cycle classes of $\nu_P$. In particular the group of $P$ has exactly $2^{c}$ elements, $c$ being the number of cycles of $\nu_P$.
--
--   Pairs of partner states are the objects counted in the phase-weighted polynomial argument of the proof: the phase turns integer index sums into complex units, and the decomposition of each group into independent flips on the cycles of the successor permutation allows the contributions of a group to be analysed cycle by cycle.
--
--   **Formalization Note** `phase n` is `Complex.I ^ (n / 3)`, an integer power with Lean's integer division, which rounds down for the positive divisor $3$. The file defines `rawIndexSum`, `OppositeCycle.faceSet`, `OppositeCycle.cyclicDelta`, `CycleClass p` (the quotient by `Equiv.Perm.SameCycle`) with `classOf`, `invariant_on_cycle`, `descendCycle` and `partialPerm`, `State.ofPermutation`, and `Pair X` (a subtype of `State X × State X`) with `left`, `right`, `next`, `third`, `Group`, `flipCorners`, `flipLeft`, `flipRight`, `flip`, `orient`, `bits`, `orientations` and the equivalence `groupEquiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/PairPhases.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/PairPhases.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Paired states, permutation cycle classes, and phase cancellation. -/

namespace Barnette

noncomputable def phase (n : ℤ) : ℂ := Complex.I ^ (n / 3)

namespace TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

def rawIndexSum [Fintype A] (r s : T.State X) : ℤ :=
  ∑ t, indexDelta (r.val t) (s.val t)

noncomputable instance [Fintype A] (s : T.State X) : Fintype (T.Partners s) :=
  Fintype.ofFinite {r : T.State X // T.Partner r s}

namespace OppositeCycle

variable {s : T.State X} (C : T.OppositeCycle s)

noncomputable def faceSet : Finset A := by
  classical
  exact Finset.univ.image C.face

@[simp] theorem mem_faceSet (t : A) : t ∈ C.faceSet ↔ t ∈ Set.range C.face := by
  classical
  simp [faceSet]

def cyclicDelta (r : T.State X) : ℤ :=
  ∑ i, indexDelta (r.val (C.face i)) (thirdIndex (r.val (C.face i)) (s.val (C.face i)))

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette

variable {A : Type*}

def CycleClass (p : Equiv.Perm A) := Quotient (Equiv.Perm.SameCycle.setoid p)

def classOf (p : Equiv.Perm A) (a : A) : CycleClass p := Quotient.mk _ a

noncomputable instance [Finite A] (p : Equiv.Perm A) : Fintype (CycleClass p) :=
  Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid p))

@[simp] theorem classOf_apply (p : Equiv.Perm A) (a : A) : classOf p (p a) = classOf p a := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl p a).apply_left

@[simp] theorem classOf_symm_apply (p : Equiv.Perm A) (a : A) :
    classOf p (p.symm a) = classOf p a := by
  have h := classOf_apply p (p.symm a)
  simpa using h.symm

theorem classOf_surjective (p : Equiv.Perm A) : Function.Surjective (classOf p) :=
  Quotient.mk_surjective

theorem invariant_on_cycle [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) {a b : A} (hab : p.SameCycle a b) : f a = f b := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ n : ℕ, ∀ a, f ((p ^ n) a) = f a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ', Equiv.Perm.mul_apply, hf, ih]
  exact (hpow n a).symm

noncomputable def descendCycle [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) : CycleClass p → B :=
  Quotient.lift f (fun _ _ h => invariant_on_cycle f hf h)

@[simp] theorem descendCycle_classOf [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) (a : A) : descendCycle f hf (classOf p a) = f a := rfl

def partialPerm (p : Equiv.Perm A) (b : A → Bool) (hb : ∀ a, b (p a) = b a) : Equiv.Perm A where
  toFun a := if b a then p a else a
  invFun a := if b a then p.symm a else a
  left_inv a := by
    cases h : b a <;> simp [h, hb]
  right_inv a := by
    have hb' (a) : b (p.symm a) = b a := by simpa using (hb (p.symm a)).symm
    cases h : b a <;> simp [h, hb']

@[simp] theorem partialPerm_apply (p : Equiv.Perm A) (b : A → Bool)
    (hb : ∀ a, b (p a) = b a) (a : A) :
    partialPerm p b hb a = if b a then p a else a := rfl

end Barnette

namespace Barnette.TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

def State.ofPermutation (s : T.State X) (e : Equiv.Perm A) (c : A → Fin 3)
    (hc : ∀ t, T.vertex t (c t) = s.value (e t)) : T.State X :=
  ⟨c, by
    constructor
    · intro t u h
      exact e.injective (s.value_injective (by simpa only [hc] using h))
    · rw [← s.value_range]
      ext v
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨e t, (hc t).symm⟩
      · rintro ⟨t, rfl⟩
        exact ⟨e.symm t, (hc _).trans (congrArg s.value (e.apply_symm_apply t))⟩⟩

def Pair (X : Set V) := {rs : T.State X × T.State X // T.Partner rs.1 rs.2}

namespace Pair

def left (P : @Pair A V T X) : T.State X := P.val.1
def right (P : @Pair A V T X) : T.State X := P.val.2

theorem partner (P : @Pair A V T X) : T.Partner P.left P.right := P.property

@[ext] theorem ext {P Q : @Pair A V T X} (hl : P.left = Q.left)
    (hr : P.right = Q.right) : P = Q := Subtype.ext (Prod.ext hl hr)

instance [Finite A] : Finite (@Pair A V T X) := inferInstanceAs (Finite (Subtype _))
noncomputable instance [Fintype A] : Fintype (@Pair A V T X) := Fintype.ofFinite _

noncomputable def next (P : @Pair A V T X) : Equiv.Perm A :=
  P.right.toEquiv.trans P.left.toEquiv.symm

@[simp] theorem value_next (P : @Pair A V T X) (t : A) :
    P.left.value (P.next t) = P.right.value t := by
  change (P.left.toEquiv (P.left.toEquiv.symm (P.right.toEquiv t)) : V) = _
  rw [Equiv.apply_symm_apply, State.coe_toEquiv]

@[simp] theorem value_prev (P : @Pair A V T X) (t : A) :
    P.right.value (P.next.symm t) = P.left.value t := by
  have h := P.value_next (P.next.symm t)
  simpa using h.symm

theorem next_ne (P : @Pair A V T X) (t : A) : P.next t ≠ t := by
  intro h
  exact P.partner t (by simpa only [h] using P.value_next t)

def third (P : @Pair A V T X) : A → Fin 3 :=
  fun t => thirdIndex (P.left.val t) (P.right.val t)

def Group (P : @Pair A V T X) := {Q : @Pair A V T X // Q.third = P.third}

noncomputable instance [Fintype A] (P : @Pair A V T X) : Fintype P.Group :=
  Fintype.ofFinite {Q : @Pair A V T X // Q.third = P.third}

def flipCorners (r s : T.State X) (b : A → Bool) : A → Fin 3 :=
  fun t => if b t then s.val t else r.val t

noncomputable def flipLeft (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : T.State X :=
  P.left.ofPermutation (partialPerm P.next b hb) (flipCorners P.left P.right b) (by
    intro t
    cases h : b t
    · simp [flipCorners, h, State.value]
    · simpa only [flipCorners, h, ↓reduceIte, partialPerm_apply, State.value] using
        (P.value_next t).symm)

noncomputable def flipRight (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : T.State X :=
  P.right.ofPermutation
    (partialPerm P.next.symm b (fun t => by simpa using (hb (P.next.symm t)).symm))
    (flipCorners P.right P.left b) (by
      intro t
      cases h : b t
      · simp [flipCorners, h, State.value]
      · simpa only [flipCorners, h, ↓reduceIte, partialPerm_apply, State.value] using
          (P.value_prev t).symm)

@[simp] theorem flipLeft_val (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) :
    (P.flipLeft b hb).val = flipCorners P.left P.right b := rfl

@[simp] theorem flipRight_val (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) :
    (P.flipRight b hb).val = flipCorners P.right P.left b := rfl

@[simp] theorem flipLeft_value (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) (t : A) :
    (P.flipLeft b hb).value t = if b t then P.right.value t else P.left.value t := by
  cases h : b t <;> simp [State.value, flipLeft_val, flipCorners, h]

@[simp] theorem flipRight_value (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) (t : A) :
    (P.flipRight b hb).value t = if b t then P.left.value t else P.right.value t := by
  cases h : b t <;> simp [State.value, flipRight_val, flipCorners, h]

noncomputable def flip (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : @Pair A V T X :=
  ⟨(P.flipLeft b hb, P.flipRight b hb), by
    intro t
    change (P.flipLeft b hb).value t ≠ (P.flipRight b hb).value t
    rw [flipLeft_value, flipRight_value]
    cases h : b t
    · simpa [h] using P.partner t
    · simpa [h] using (P.partner t).symm⟩

theorem flip_third (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : (P.flip b hb).third = P.third := by
  funext t
  change thirdIndex (flipCorners P.left P.right b t) (flipCorners P.right P.left b t) = _
  cases h : b t <;> simp [flipCorners, h, third, thirdIndex, add_comm]

noncomputable def orient (P : @Pair A V T X) (b : CycleClass P.next → Bool) : P.Group :=
  ⟨P.flip (fun t => b (classOf P.next t)) (fun t => by rw [classOf_apply]),
    P.flip_third _ _⟩

theorem same_third_corners : ∀ i j k l : Fin 3, i ≠ j → k ≠ l →
    thirdIndex i j = thirdIndex k l → (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

theorem group_local (P : @Pair A V T X) (Q : P.Group) (t : A) :
    (Q.val.left.val t = P.left.val t ∧ Q.val.right.val t = P.right.val t) ∨
    (Q.val.left.val t = P.right.val t ∧ Q.val.right.val t = P.left.val t) := by
  apply same_third_corners
  · exact fun h => Q.val.partner t ((State.value_eq_iff _ _ _).mpr h)
  · exact fun h => P.partner t ((State.value_eq_iff _ _ _).mpr h)
  · exact congrFun Q.property t

noncomputable def bits (P : @Pair A V T X) (Q : P.Group) (t : A) : Bool :=
  decide (Q.val.left.val t = P.right.val t)

theorem group_values (P : @Pair A V T X) (Q : P.Group) (t : A) :
    Q.val.left.value t = (if P.bits Q t then P.right.value t else P.left.value t) ∧
    Q.val.right.value t = (if P.bits Q t then P.left.value t else P.right.value t) := by
  have hn : P.left.val t ≠ P.right.val t := fun h =>
    P.partner t ((State.value_eq_iff _ _ _).mpr h)
  rcases P.group_local Q t with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    simp [bits, hl, hr, hn, State.value]

theorem bits_invariant (P : @Pair A V T X) (Q : P.Group) (t : A) :
    P.bits Q (P.next t) = P.bits Q t := by
  have h0 := P.group_values Q t
  have h1 := P.group_values Q (P.next t)
  cases ht : P.bits Q t <;> cases hn : P.bits Q (P.next t)
  · rfl
  · simp only [ht, hn, Bool.false_eq_true, ↓reduceIte] at h0 h1
    exact False.elim (P.next_ne t (Q.val.right.value_injective
      (h1.2.trans ((P.value_next t).trans h0.2.symm))))
  · simp only [ht, hn, Bool.false_eq_true, ↓reduceIte] at h0 h1
    exact False.elim (P.next_ne t (Q.val.left.value_injective
      (h1.1.trans ((P.value_next t).trans h0.1.symm))))
  · rfl

noncomputable def orientations [Finite A] (P : @Pair A V T X) (Q : P.Group) :
    CycleClass P.next → Bool := descendCycle (P.bits Q) (P.bits_invariant Q)

@[simp] theorem orient_orientations [Finite A] (P : @Pair A V T X) (Q : P.Group) :
    P.orient (P.orientations Q) = Q := by
  apply Subtype.ext
  apply Pair.ext
  · apply State.ext
    intro t
    change (P.flipLeft (fun t => P.orientations Q (classOf P.next t))
      (fun t => by rw [classOf_apply])).value t = _
    rw [flipLeft_value]
    dsimp [orientations, descendCycle, classOf]
    exact (P.group_values Q t).1.symm
  · apply State.ext
    intro t
    change (P.flipRight (fun t => P.orientations Q (classOf P.next t))
      (fun t => by rw [classOf_apply])).value t = _
    rw [flipRight_value]
    dsimp [orientations, descendCycle, classOf]
    exact (P.group_values Q t).2.symm

@[simp] theorem orientations_orient [Finite A] (P : @Pair A V T X)
    (b : CycleClass P.next → Bool) : P.orientations (P.orient b) = b := by
  funext c
  obtain ⟨t, rfl⟩ := classOf_surjective P.next c
  change P.bits (P.orient b) t = b (classOf P.next t)
  have hn : P.left.val t ≠ P.right.val t := fun h =>
    P.partner t ((State.value_eq_iff _ _ _).mpr h)
  change decide ((if b (classOf P.next t) then P.right.val t else P.left.val t) =
    P.right.val t) = b (classOf P.next t)
  cases b (classOf P.next t) <;> simp [hn]

noncomputable def groupEquiv [Finite A] (P : @Pair A V T X) :
    (CycleClass P.next → Bool) ≃ P.Group where
  toFun := P.orient
  invFun := P.orientations
  left_inv := P.orientations_orient
  right_inv := P.orient_orientations

end Pair
end Barnette.TriangleSystem

end OAI


