-- Prove2me | Definitions.Def_M4aHerbrand_GenuineTensorEquiv
-- name    : M4aHerbrand_GenuineTensorEquiv
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/825f1710-f251-5f67-8a99-c68bfcb8520e
-- title:
--   Adelic base change: AK​⊗K​L≅AL​
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, and the adele ring `AdeleRing (𝓞 K) K` is Mathlib's product of the infinite and the finite adeles. The module first records a purely formal splitting: for commutative $K$-algebras $P$, $Q$, $L$, the Mathlib linear equivalence `TensorProduct.prodLeft` sends $(p,q) \otimes l$ to $(p \otimes l, q \otimes l)$ (`prodLeft_tmul_proj`), and `prodTensorAlgEquiv` packages it as a $K$-algebra isomorphism $(P \times Q) \otimes_K L \cong (P \otimes_K L) \times (Q \otimes_K L)$, with its action on elementary tensors recorded. Also recorded is `moduleFinite_ringOfIntegers`, the finiteness of $\mathcal{O}_L$ as an $\mathcal{O}_K$-module, deduced from finiteness over $\mathbb{Z}$ and installed as a local instance.
--
--   The main definition is `genuineRingEquiv`, a ring isomorphism $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$, obtained by applying the above splitting with $P$ the infinite adeles of $K$ and $Q$ the finite adeles of $K$, and then taking the product of two base-change isomorphisms: the field `baseChangeRingEquiv` of the structure `genuineInfinitePlaceData` at the archimedean places, and `finiteBaseChangeRingEquiv` for the finite adeles, the latter built from the componentwise identification of $\mathcal{O}_L \otimes_{\mathcal{O}_K} K_v$ with the product of the completions $L_w$, $w \mid v$. Two compatibilities are proved: $1 \otimes l$ goes to the principal adele of $l$, and $x \otimes 1$ goes to $\beta(x)$, where `genuineβ` is the conorm map $\mathbb{A}_K \to \mathbb{A}_L$ assembled from the local inclusions at infinite and at finite places. The second compatibility is exactly what makes the isomorphism $\mathbb{A}_K$-linear, so `genuineTensorEquiv` upgrades it to an isomorphism of $\mathbb{A}_K$-algebras, $\mathbb{A}_L$ being regarded as an $\mathbb{A}_K$-algebra via `genuineβ K L`; the two compatibility statements are restated for it.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring as the product of the infinite and finite adele rings, and the linear equivalence `TensorProduct.prodLeft`; the algebra-equivalence upgrade of the latter and the base-change isomorphism $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ over $\mathbb{A}_K$ are the project's own.
--
--   **Where it is used.** This isomorphism is the adelic base-change dictionary for a finite extension of number fields: it lets adelic objects over $L$ be read as objects over $\mathbb{A}_K$ after tensoring with $L$, and is used in the adelic setting on which the automorphic side of the argument is built.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_GenuineTensorEquiv.lean

import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_M4aHerbrand_FiniteTensorEquiv
import Mathlib.LinearAlgebra.TensorProduct.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct M4aHerbrand.ArchSemilocal

open scoped TensorProduct

section ProdSplit

variable (K P Q L : Type*) [CommRing K] [CommRing P] [CommRing Q] [CommRing L]
  [Algebra K P] [Algebra K Q] [Algebra K L]

theorem prodLeft_tmul_proj (x : P × Q) (l : L) :
    TensorProduct.prodLeft K K P Q L (x ⊗ₜ[K] l) = (x.1 ⊗ₜ[K] l, x.2 ⊗ₜ[K] l) := by
  obtain ⟨p, q⟩ := x
  rfl

def prodTensorAlgEquiv : ((P × Q) ⊗[K] L) ≃ₐ[K] ((P ⊗[K] L) × (Q ⊗[K] L)) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.prodLeft K K P Q L)
    (by
      rw [Algebra.TensorProduct.one_def, prodLeft_tmul_proj]
      exact Prod.ext rfl rfl)
    (fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul p a =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul q b =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, prodLeft_tmul_proj,
            Prod.mk_mul_mk, Prod.fst_mul, Prod.snd_mul]
        | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
      | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂])

@[simp] theorem prodTensorAlgEquiv_tmul (x : P × Q) (l : L) :
    prodTensorAlgEquiv K P Q L (x ⊗ₜ[K] l) = (x.1 ⊗ₜ[K] l, x.2 ⊗ₜ[K] l) :=
  prodLeft_tmul_proj K P Q L x l

end ProdSplit

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in

theorem moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 L) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)

attribute [local instance] moduleFinite_ringOfIntegers

def genuineRingEquiv : ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃+* AdeleRing (𝓞 L) L :=
  ((prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L).toRingEquiv).trans
    (RingEquiv.prodCongr (genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv
      (finiteBaseChangeRingEquiv (𝓞 K) K L (𝓞 L)))

theorem genuineRingEquiv_one_tmul (l : L) :
    genuineRingEquiv K L ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv_one_tmul l)
    (finiteBaseChangeRingEquiv_one_tmul (𝓞 K) K L (𝓞 L) l)

theorem genuineRingEquiv_tmul_one (x : AdeleRing (𝓞 K) K) :
    genuineRingEquiv K L (x ⊗ₜ[K] (1 : L)) = genuineβ K L x :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv_tmul_one x.1)
    (finiteBaseChangeRingEquiv_tmul_one (𝓞 K) K L (𝓞 L) x.2)

def genuineTensorEquiv :
    letI := (genuineβ K L).toAlgebra
    ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
  letI := (genuineβ K L).toAlgebra
  AlgEquiv.ofRingEquiv (f := genuineRingEquiv K L) (fun x => by
    exact genuineRingEquiv_tmul_one K L x)

theorem genuineTensorEquiv_apply (z : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    genuineTensorEquiv K L z = genuineRingEquiv K L z := rfl

theorem genuineTensorEquiv_one_tmul (l : L) :
    genuineTensorEquiv K L ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l :=
  genuineRingEquiv_one_tmul K L l

theorem genuineTensorEquiv_tmul_one (x : AdeleRing (𝓞 K) K) :
    genuineTensorEquiv K L (x ⊗ₜ[K] (1 : L)) = genuineβ K L x :=
  genuineRingEquiv_tmul_one K L x

end Genuine

end M4aHerbrand.Bridge

end


