-- Prove2me | Definitions.Def_HopfAlgebra_HopfKer
-- name    : HopfAlgebra_HopfKer
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/21a095b0-cb8a-5d4f-8e3b-9216b35b7871
-- title:
--   Coinvariants and the Hopf–Galois condition for bialgebra maps
-- statement:
--   Throughout, $R$ is a commutative ring and $\pi\colon A\to B$ a homomorphism of commutative $R$-bialgebras. The first definition is the right coaction $\mathrm{coaction}\,\pi = (\mathrm{id}_A\otimes\pi)\circ\Delta_A \colon A\to A\otimes_R B$, an $R$-algebra homomorphism obtained by composing the comultiplication of $A$, viewed as an algebra map, with the tensor product of the identity of $A$ and the algebra map underlying $\pi$. The subalgebra $\mathrm{hopfKer}\,\pi\subseteq A$ is the equalizer of this coaction and the inclusion $a\mapsto a\otimes 1$ of $A$ into $A\otimes_R B$; thus $a$ lies in it precisely when $\mathrm{coaction}\,\pi\,(a)=a\otimes 1$, the content of `mem_hopfKer_iff` and `coaction_eq_of_mem`. Next, $\mathrm{canAlgHom}\,\pi\colon A\otimes_R A\to A\otimes_R B$ is the algebra homomorphism determined (the target being commutative) by $a\otimes 1\mapsto a\otimes 1$ on the left factor and by the coaction on the right factor, so that $a\otimes a'\mapsto (a\otimes 1)\cdot\mathrm{coaction}\,\pi\,(a')$; `canMap` is its underlying $R$-linear map. The accompanying lemmas record the values on $a\otimes 1$ and $1\otimes a$ and the balancing identity $\mathrm{can}((ah)\otimes a')=\mathrm{can}(a\otimes (ha'))$ for $h\in\mathrm{hopfKer}\,\pi$.
--
--   The set $\mathrm{balancingRelations}\,\pi\subseteq A\otimes_R A$ consists of the elements $(ah)\otimes a'-a\otimes(ha')$ with $a,a'\in A$ and $h\in\mathrm{hopfKer}\,\pi$; `canMap_eq_zero_of_mem_span` shows that `canMap` vanishes on the $R$-span of this set. Finally, the predicate $\mathrm{IsHopfGalois}\,\pi$ is the conjunction of two conditions: `canMap π` is surjective, and every element of its kernel lies in the $R$-span of the balancing relations. Together with the previous lemma this says that `canMap` induces an isomorphism $A\otimes_{\mathrm{hopfKer}\,\pi}A\xrightarrow{\ \sim\ }A\otimes_R B$, but the condition is formulated without forming the tensor product over the subalgebra: it is stated as surjectivity plus an explicit description of the kernel by generators.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — `Bialgebra`, bialgebra homomorphisms `A →ₐc[R] B`, `AlgHom.equalizer` and the algebra structure on tensor products — but has no notion of coinvariant subalgebra or Hopf–Galois extension; `hopfKer`, `canMap` and `IsHopfGalois` are the project's own.
--
--   **Where it is used.** In geometric terms $\mathrm{Spec}$ of $\pi$ is a homomorphism of affine group schemes, $\mathrm{hopfKer}\,\pi$ is the candidate coordinate ring of the quotient, and $\mathrm{IsHopfGalois}\,\pi$ expresses that $\mathrm{Spec}\,A\to\mathrm{Spec}(\mathrm{hopfKer}\,\pi)$ is a torsor under $\mathrm{Spec}\,B$. This module is imported broadly by the parts of the development that handle quotients of affine (group) schemes by subgroup schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HopfAlgebra_HopfKer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]

noncomputable def coaction (π : A →ₐc[R] B) : A →ₐ[R] A ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)).comp (Bialgebra.comulAlgHom R A)

theorem coaction_apply (π : A →ₐc[R] B) (a : A) :
    coaction π a = Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) (Coalgebra.comul (R := R) a) := rfl

noncomputable def hopfKer (π : A →ₐc[R] B) : Subalgebra R A :=
  AlgHom.equalizer (coaction π) (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)

theorem mem_hopfKer_iff (π : A →ₐc[R] B) (a : A) : a ∈ hopfKer π ↔ coaction π a = a ⊗ₜ[R] 1 := Iff.rfl

theorem coaction_eq_of_mem (π : A →ₐc[R] B) {a : A} (h : a ∈ hopfKer π) : coaction π a = a ⊗ₜ[R] 1 := h

noncomputable def canAlgHom (π : A →ₐc[R] B) : A ⊗[R] A →ₐ[R] A ⊗[R] B :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) (coaction π)
    (fun _ _ => Commute.all _ _)

@[simp] theorem canAlgHom_tmul (π : A →ₐc[R] B) (a a' : A) :
    canAlgHom π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  Algebra.TensorProduct.lift_tmul _ _ _ a a'

noncomputable def canMap (π : A →ₐc[R] B) : A ⊗[R] A →ₗ[R] A ⊗[R] B := (canAlgHom π).toLinearMap

theorem canMap_apply (π : A →ₐc[R] B) (z : A ⊗[R] A) : canMap π z = canAlgHom π z := rfl

@[simp] theorem canMap_tmul (π : A →ₐc[R] B) (a a' : A) :
    canMap π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  canAlgHom_tmul π a a'

theorem canMap_mul_tmul (π : A →ₐc[R] B) (a a' : A) {h : A} (hh : h ∈ hopfKer π) :
    canMap π ((a * h) ⊗ₜ[R] a') = canMap π (a ⊗ₜ[R] (h * a')) := by
  rw [canMap_tmul, canMap_tmul, map_mul, coaction_eq_of_mem π hh, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one]

theorem canMap_tmul_one (π : A →ₐc[R] B) (a : A) : canMap π (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 := by
  rw [canMap_tmul, map_one, mul_one]

theorem canMap_one_tmul (π : A →ₐc[R] B) (a : A) : canMap π (1 ⊗ₜ[R] a) = coaction π a := by
  rw [canMap_tmul, ← Algebra.TensorProduct.one_def, one_mul]

def balancingRelations (π : A →ₐc[R] B) : Set (A ⊗[R] A) :=
  {x | ∃ (a h a' : A), h ∈ hopfKer π ∧ x = (a * h) ⊗ₜ[R] a' - a ⊗ₜ[R] (h * a')}

theorem canMap_eq_zero_of_mem_span (π : A →ₐc[R] B) {z : A ⊗[R] A}
    (hz : z ∈ Submodule.span R (balancingRelations π)) : canMap π z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, h, a', hh, rfl⟩ := hx
    rw [map_sub, canMap_mul_tmul π a a' hh, sub_self]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

def IsHopfGalois (π : A →ₐc[R] B) : Prop :=
  Function.Surjective (canMap π) ∧ ∀ z, canMap π z = 0 → z ∈ Submodule.span R (balancingRelations π)

end HopfAlgebra


