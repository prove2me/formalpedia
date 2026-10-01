-- Prove2me | Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
-- name    : LocalConjugacy_Proof_Counterexamples_Heisenberg
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T13:50:20.488722+00:00
-- url     : https://prove2.me/theorems/e2f69749-2f95-4634-bc47-510964610c6b
-- title:
--   The imprimitive wreath product model
-- statement:
--   The group $C_3^3\rtimes D_6$, with the usual permutation action on three coordinates, together with the sum and sign maps and the subgroups used in the Heisenberg counterexample in §1.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

/-!
The imprimitive wreath product `C₃ wr S₃`, of order 162, acting on nine
points. Its normal Heisenberg subgroup is the kernel of the base-sum/sign
map to `C₃ × C₂`. The chosen cyclic complement translates block zero and
interchanges the other two blocks. Its Sylow subgroups have disjoint fixed
point sets. This is the second example in the manuscript.
-/

namespace LocalConjugacy.HeisenbergExample

abbrev C3 := Multiplicative (ZMod 3)
abbrev C2 := Multiplicative (ZMod 2)
abbrev B := ZMod 3 → C3
abbrev S := DihedralGroup 3

def perm : S → ZMod 3 → ZMod 3
  | .r a, i => a + i
  | .sr a, i => -(a + i)

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem perm_one : ∀ i, perm 1 i = i := by decide
theorem perm_mul : ∀ s t i, perm (s * t) i = perm s (perm t i) := by decide

def action : S →* MulAut B where
  toFun s :=
    { toFun := fun b i => b (perm s⁻¹ i)
      invFun := fun b i => b (perm s i)
      left_inv := fun b => by ext i; dsimp; rw [← perm_mul, inv_mul_cancel, perm_one]
      right_inv := fun b => by ext i; dsimp; rw [← perm_mul, mul_inv_cancel, perm_one]
      map_mul' := fun _ _ => rfl }
  map_one' := by ext b i; dsimp; rw [inv_one, perm_one]
  map_mul' s t := by ext b i; dsimp; rw [mul_inv_rev, perm_mul]

abbrev G := B ⋊[action] S
instance : Fintype G := Fintype.ofEquiv (B × S) SemidirectProduct.equivProd.symm
instance (priority := high) : DecidableEq G := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2,
     fun h => ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩⟩
instance (priority := high) : TopologicalSpace G := ⊥
instance : DiscreteTopology G := ⟨rfl⟩

def sign : S →* C2 where
  toFun s := match s with | .r _ => 1 | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by decide

def sumBase : B →* C3 where
  toFun b := b 0 * b 1 * b 2
  map_one' := rfl
  map_mul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc]

def baseMap : B →* C3 × C2 := sumBase.prod 1
def permMap : S →* C3 × C2 := (1 : S →* C3).prod sign

theorem compatibility : ∀ s : S,
    baseMap.comp (action s).toMonoidHom =
      (MulAut.conj (permMap s)).toMonoidHom.comp baseMap := by
  intro s
  apply MonoidHom.ext
  exact (by decide : ∀ s : S, ∀ b : B,
    baseMap (action s b) = permMap s * baseMap b * (permMap s)⁻¹) s

/-- Quotient by the normal Heisenberg subgroup. -/
def projection : G →* C3 × C2 := SemidirectProduct.lift baseMap permMap compatibility

/-- Kernel: base vectors of sum zero, with even block permutation. -/
def N : Subgroup G := projection.ker
instance : DecidablePred (· ∈ N) := fun _ => inferInstanceAs (Decidable (projection _ = 1))
instance : N.Normal := inferInstanceAs projection.ker.Normal

/-- A section of the quotient: change only block zero and optionally swap
blocks one and two. Thus its image is a cyclic complement of order six. -/
def sectionMap : C3 × C2 →* G where
  toFun z := ⟨fun i => if i = 0 then z.1 else 1,
    if z.2 = 1 then 1 else DihedralGroup.sr 0⟩
  map_one' := by decide
  map_mul' := by decide



def J : Subgroup G := sectionMap.range
instance : DecidablePred (· ∈ J) := fun _ =>
  inferInstanceAs (Decidable (∃ z : C3 × C2, sectionMap z = _))




theorem card_J : Fintype.card J = 6 := by decide


abbrev Ω := ZMod 3 × C3

def move (g : G) (x : Ω) : Ω :=
  (perm g.right x.1, g.left (perm g.right x.1) * x.2)

instance : MulAction G Ω where
  smul := move
  one_smul := by decide
  mul_smul g h x := by
    apply Prod.ext
    · exact perm_mul _ _ _
    · change g.left (perm (g.right * h.right) x.1) *
        h.left (perm g.right⁻¹ (perm (g.right * h.right) x.1)) * x.2 =
        g.left (perm g.right (perm h.right x.1)) * (h.left (perm h.right x.1) * x.2)
      rw [perm_mul, ← perm_mul g.right⁻¹ g.right, inv_mul_cancel, perm_one, mul_assoc]

def H : Subgroup G := MulAction.stabilizer G ((0, 1) : Ω)
instance : DecidablePred (· ∈ H) := fun g => inferInstanceAs (Decidable (move g (0, 1) = (0, 1)))



/-- Elements generating the Sylow 3- and Sylow 2-subgroups of the complement. -/
def c : G := sectionMap (Multiplicative.ofAdd 1, 1)
def t : G := sectionMap (1, Multiplicative.ofAdd 1)
def shift : G := ⟨1, .r 1⟩

















def P3 : Subgroup G := (sectionMap.comp (MonoidHom.inl C3 C2)).range
def P2 : Subgroup G := (sectionMap.comp (MonoidHom.inr C3 C2)).range
instance : DecidablePred (· ∈ P3) := fun x =>
  inferInstanceAs (Decidable (∃ z : C3, sectionMap (z, 1) = x))
instance : DecidablePred (· ∈ P2) := fun x =>
  inferInstanceAs (Decidable (∃ z : C2, sectionMap (1, z) = x))


















theorem cyclic_J : IsCyclic J := by
  let z : J := ⟨c * t, J.mul_mem ⟨_, rfl⟩ ⟨_, rfl⟩⟩
  apply isCyclic_of_orderOf_eq_card z
  rw [Nat.card_eq_fintype_card, card_J]
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  constructor
  · apply Subtype.ext; decide
  · intro m hm hm0
    interval_cases m <;> decide










end LocalConjugacy.HeisenbergExample

end LocalConjugacy.Proof

end


