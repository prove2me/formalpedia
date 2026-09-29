-- Prove2me | Definitions.Def_PDivisibleGroup_CharacterDifferential
-- name    : PDivisibleGroup_CharacterDifferential
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/9583b9bc-89de-53af-9051-6009492177ec
-- title:
--   Cotangent classes and character differentials for Cartier duality
-- statement:
--   Throughout, $R$ is a commutative ring and $G$ is a [`PDivisibleGroup R p h`](../def/PDivisibleGroup_Basic.html#L199), so $G$ consists of finite free cocommutative Hopf $R$-algebras $A_v =$ `G.level v` with surjective bialgebra transition maps and the torsion conditions recorded in that structure. For each level $v$, [`PDivisibleGroup.cotangentClass`](../def/PDivisibleGroup_CharacterDifferential.html#L20) is the $R$-linear map $A_v \to$ `G.Cotangent v` $= I_v/I_v^2$, where $I_v =$ `G.augIdeal v` is the kernel of the counit, sending $a$ to the class of $a - \varepsilon(a)\cdot 1$, which lies in $I_v$. The accompanying lemmas record that it agrees with `Ideal.toCotangent` on elements of the augmentation ideal, and that it kills $1$ and, more generally, the image of $R$ under the structure map.
--
--   In the second part, $G, G'$ are $p$-divisible groups over $R$ equipped with a duality datum $D$ : `CartierDuality G G'`, which supplies bialgebra isomorphisms $A'_v \cong$ [`CartierDual R`](../def/HopfAlgebra_CartierDual.html#L12) $A_v$ compatible with the transitions, and in particular the $R$-linear isomorphisms `D.toDualEquiv v` $: A'_v \cong A_v^\vee$; $S$ is a commutative $R$-algebra. For a point $\psi \in$ `G'.Point S v` (an element of the convolution monoid of $R$-algebra maps $A'_v \to S$), `charElem` is the element
--   $$\sum_i \psi\bigl((\mathrm{D.toDualEquiv}\ v)^{-1}(b^i)\bigr) \otimes b_i \in S \otimes_R A_v,$$
--   formed from the chosen basis $(b_i)$ of the finite free module $A_v$ given by `Module.Free.chooseBasis` and its coordinate functionals $b^i$. Its character differential `charDiff` is the image of `charElem` in $S \otimes_R$ `G.Cotangent v` under the map induced by `cotangentClass v` on the second factor; `charDiff_eq_sum` expresses it as the corresponding sum of $\psi((\cdots)^{-1}(b^i)) \otimes$ `cotangentClass v` $b_i$.
--
--   **Relation to Mathlib.** The cotangent space here is Mathlib's `Ideal.Cotangent` (with `Ideal.toCotangent`) applied to the augmentation ideal of a Hopf algebra; $p$-divisible groups, their Cartier duality data and these character constructions are the project's own notions.
--
--   **Where it is used.** These constructions provide the algebraic input for the Cartier pairing between points of $G'$ and points, respectively cotangent vectors, of $G$, and hence for the comparison of Tate modules with tangent spaces in the project's treatment of $p$-divisible groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PDivisibleGroup_CharacterDifferential.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_Dimension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra
open scoped TensorProduct

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

section CotangentClass

variable (G : PDivisibleGroup R p h)

def cotangentClass (v : ℕ) : G.level v →ₗ[R] G.Cotangent v where
  toFun a := (G.augIdeal v).toCotangent
    ⟨a - algebraMap R (G.level v) (counit (R := R) a), Hopf.sub_algebraMap_counit_mem_augIdeal R _ a⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    change a + b - algebraMap R (G.level v) (counit (R := R) (a + b)) =
      (a - algebraMap R (G.level v) (counit (R := R) a)) + (b - algebraMap R (G.level v) (counit (R := R) b))
    rw [map_add, map_add]
    abel
  map_smul' r a := by
    rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]
    congr 1
    ext
    change r • a - algebraMap R (G.level v) (counit (R := R) (r • a)) =
      r • (a - algebraMap R (G.level v) (counit (R := R) a))
    rw [map_smul, smul_sub, Algebra.smul_def r (algebraMap R (G.level v) _), ← map_mul, smul_eq_mul]

theorem cotangentClass_apply (v : ℕ) (a : G.level v) :
    G.cotangentClass v a = (G.augIdeal v).toCotangent
      ⟨a - algebraMap R (G.level v) (counit (R := R) a),
        Hopf.sub_algebraMap_counit_mem_augIdeal R _ a⟩ := rfl

theorem cotangentClass_of_mem (v : ℕ) (a : G.augIdeal v) :
    G.cotangentClass v a = (G.augIdeal v).toCotangent a := by
  rw [cotangentClass_apply]
  congr 1
  ext
  change (a : G.level v) - algebraMap R (G.level v) (counit (R := R) (a : G.level v)) = a
  rw [(G.mem_augIdeal_iff v a).mp a.2, map_zero, sub_zero]

@[simp] theorem cotangentClass_one (v : ℕ) : G.cotangentClass v 1 = 0 := by
  rw [cotangentClass_apply, ← map_zero (G.augIdeal v).toCotangent]
  congr 1
  ext
  change (1 : G.level v) - algebraMap R (G.level v) (counit (R := R) (1 : G.level v)) = 0
  rw [Bialgebra.counit_one, map_one, sub_self]

@[simp] theorem cotangentClass_algebraMap (v : ℕ) (r : R) :
    G.cotangentClass v (algebraMap R (G.level v) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, cotangentClass_one, smul_zero]

end CotangentClass

namespace CartierDuality

variable {G G' : PDivisibleGroup R p h} (D : CartierDuality G G')
variable (S : Type) [CommRing S] [Algebra R S]

def charElem (v : ℕ) (ψ : G'.Point S v) : S ⊗[R] G.level v :=
  ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R]
    Module.Free.chooseBasis R (G.level v) i

theorem charElem_def (v : ℕ) (ψ : G'.Point S v) :
    D.charElem S v ψ = ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm
      ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R] Module.Free.chooseBasis R (G.level v) i :=
  rfl

def charDiff (v : ℕ) (ψ : G'.Point S v) : S ⊗[R] G.Cotangent v :=
  (G.cotangentClass v).lTensor S (D.charElem S v ψ)

theorem charDiff_def (v : ℕ) (ψ : G'.Point S v) :
    D.charDiff S v ψ = (G.cotangentClass v).lTensor S (D.charElem S v ψ) := rfl

theorem charDiff_eq_sum (v : ℕ) (ψ : G'.Point S v) :
    D.charDiff S v ψ = ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm
      ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R]
        G.cotangentClass v (Module.Free.chooseBasis R (G.level v) i) := by
  rw [charDiff_def, charElem_def, map_sum]
  rfl

end CartierDuality

end PDivisibleGroup

end


