-- Prove2me | Definitions.Def_PDivisibleGroup_CartierDuality
-- name    : PDivisibleGroup_CartierDuality
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/2a349208-76ec-573a-bc63-687045829fa9
-- title:
--   Cartier duality data and pairings for p-divisible groups
-- statement:
--   Fix a commutative ring $R$ and natural numbers $p,h$, and let $G,G'$ be $p$-divisible groups over $R$ of height $h$ in the sense of the project's structure [`PDivisibleGroup`](../def/PDivisibleGroup_Basic.html#L199): families of commutative Hopf algebras `level v` over $R$, cocommutative, finite and free as $R$-modules, with surjective bialgebra transition maps `transition v : level (v+1) →ₐc[R] level v` whose kernels are the $p^v$-torsion ideals and with $\operatorname{rank}_R(\mathrm{level}\ v)=p^{vh}$. A term of the structure `CartierDuality G G'` is a datum consisting of bialgebra isomorphisms $e_v\colon G'.\mathrm{level}\ v \xrightarrow{\sim} \mathtt{CartierDual}\ R\ (G.\mathrm{level}\ v)$ for every $v$, together with the compatibility `equiv_transition`: for all $v$, all $x$ in $G'.\mathrm{level}(v+1)$ and all $a$ in $G.\mathrm{level}(v+1)$,
--   $$e_v(\mathrm{transition}_v\,x)(\mathrm{transition}_v\,a) = e_{v+1}(x)\big(\mathtt{nsmulAlgHom}\ R\ (G.\mathrm{level}(v+1))\ p\ (a)\big),$$
--   where `nsmulAlgHom … p` is the $p$-th convolution power of the identity, i.e. the comorphism of multiplication by $p$; elements of the Cartier dual are applied as $R$-linear functionals. Thus the transitions of $G'$ are required to be dual to multiplication by $p$ on $G$. The predicate `IsCartierDual G G'` asserts that such a datum exists.
--
--   The remaining declarations record the elementary consequences of such a datum: `toDualEquiv v` is the $R$-linear equivalence $G'.\mathrm{level}\ v \simeq \operatorname{Hom}_R(G.\mathrm{level}\ v, R)$ obtained from $e_v$ followed by the identification [`CartierDual.toDual`](../def/HopfAlgebra_CartierDual.html#L948), with its formulas for values and for the inverse; `equiv_mul_apply` expresses $e_v(xy)(a)$ as the convolution, namely `TensorProduct.dualDistrib` applied to the tensor of the two functionals and to `comul a`; `equiv_one_apply` gives $e_v(1)(a)=\varepsilon(a)$; and `counit_eq_equiv_apply_one` gives $\varepsilon(x)=e_v(x)(1)$.
--
--   Finally, for a commutative $R$-algebra $L$, `pair L v f ψ` assigns to $L$-points $f$ of $G$ and $\psi$ of $G'$ at level $v$ the element $\sum_i f(b_i)\,\psi\big(e_v^{-1}(b_i^{\vee})\big)$ of $L$, where $(b_i)$ is the basis of $G.\mathrm{level}\ v$ produced by `Module.Free.chooseBasis` and $b_i^{\vee}$ its coordinate functionals, the points being evaluated through their underlying $R$-algebra maps. The definition is tied to that particular choice of basis; independence of the choice, bimultiplicativity, perfectness and Galois equivariance are not part of the data.
--
--   **Relation to Mathlib.** Mathlib supplies bialgebras, Hopf algebras, `Module.Dual` and `TensorProduct.dualDistrib`, but no notion of $p$-divisible group or of the Cartier dual of a finite flat group scheme; [`PDivisibleGroup`](../def/PDivisibleGroup_Basic.html#L199), [`CartierDual`](../def/HopfAlgebra_CartierDual.html#L12) and the duality datum and pairing defined here are the project's own.
--
--   **Where it is used.** Together with the points and Tate module of a $p$-divisible group, these definitions provide the language in which duality statements for $p$-divisible groups are formulated in the project, the pairing on $L$-points being the level-$v$ Cartier pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PDivisibleGroup_CartierDuality.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra WithConv

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

structure CartierDuality (G G' : PDivisibleGroup R p h) : Type where

  equiv : ∀ v, G'.level v ≃ₐc[R] CartierDual R (G.level v)

  equiv_transition : ∀ (v : ℕ) (x : G'.level (v + 1)) (a : G.level (v + 1)),
    equiv v (G'.transition v x) (G.transition v a) =
      equiv (v + 1) x (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p a)

def IsCartierDual (G G' : PDivisibleGroup R p h) : Prop := Nonempty (CartierDuality G G')

namespace CartierDuality

variable {G G' : PDivisibleGroup R p h} (D : CartierDuality G G')

def toDualEquiv (v : ℕ) : G'.level v ≃ₗ[R] Module.Dual R (G.level v) :=
  (D.equiv v).toLinearEquiv.trans (CartierDual.toDual R (G.level v))

@[simp] theorem toDualEquiv_apply (v : ℕ) (x : G'.level v) (a : G.level v) :
    D.toDualEquiv v x a = D.equiv v x a := rfl

theorem toDualEquiv_symm_apply (v : ℕ) (φ : Module.Dual R (G.level v)) :
    (D.toDualEquiv v).symm φ = (D.equiv v).symm (CartierDual.ofDual R (G.level v) φ) := rfl

theorem equiv_mul_apply (v : ℕ) (x y : G'.level v) (a : G.level v) :
    D.equiv v (x * y) a =
      TensorProduct.dualDistrib R (G.level v) (G.level v)
        (CartierDual.toDual R _ (D.equiv v x) ⊗ₜ[R] CartierDual.toDual R _ (D.equiv v y)) (comul (R := R) a) := by
  rw [map_mul]
  exact CartierDual.mul_apply _ _ a

theorem equiv_one_apply (v : ℕ) (a : G.level v) : D.equiv v 1 a = counit (R := R) a := by
  rw [map_one]
  rfl

theorem counit_eq_equiv_apply_one (v : ℕ) (x : G'.level v) : counit (R := R) x = D.equiv v x 1 := by
  rw [← CartierDual.counit_apply (D.equiv v x)]
  exact (CoalgHomClass.counit_comp_apply (D.equiv v) x).symm

variable (L : Type) [CommRing L] [Algebra R L]

def pair (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) : L :=
  ∑ i, Point.toAlgHom f (Module.Free.chooseBasis R (G.level v) i) *
    Point.toAlgHom ψ ((D.toDualEquiv v).symm ((Module.Free.chooseBasis R (G.level v)).coord i))

theorem pair_def (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ = ∑ i, Point.toAlgHom f (Module.Free.chooseBasis R (G.level v) i) *
      Point.toAlgHom ψ ((D.toDualEquiv v).symm ((Module.Free.chooseBasis R (G.level v)).coord i)) := rfl

end CartierDuality

end PDivisibleGroup

end


