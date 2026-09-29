-- Prove2me | Definitions.Def_QuaternionAlgebra_BaseChange
-- name    : QuaternionAlgebra_BaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/88f580d3-5e8e-515b-9b86-c1c0f0bd7fb7
-- title:
--   Base change of generalised quaternion algebras
-- statement:
--   Throughout, $R$ is a commutative ring, $S$ a commutative $R$-algebra, $c_1,c_2,c_3\in R$ and $d_1,d_2,d_3\in S$ with $\mathrm{algebraMap}\,R\,S\,c_i=d_i$ for $i=1,2,3$; these three equalities are the hypotheses $h_1,h_2,h_3$ of every declaration. Here $\mathbb{H}[R,c_1,c_2,c_3]$ is Mathlib's generalised quaternion algebra: free of rank $4$ on $1,i,j,k$ with $i^2=c_1+c_2i$, $j^2=c_3$, $ij=k$, $ji=c_2j-k$. First, `Basis.ofAlgebraMapEq` exhibits the standard elements $(0,1,0,0)$, $(0,0,1,0)$, $(0,0,0,1)$ of $\mathbb{H}[S,d_1,d_2,d_3]$ as a `QuaternionAlgebra.Basis` over $R$ with parameters $c_1,c_2,c_3$, i.e. verifies those four relations with the $c_i$ acting through $R\to S$. Lifting it gives `mapOfAlgebraMapEq`, the $R$-algebra homomorphism $\mathbb{H}[R,c_1,c_2,c_3]\to\mathbb{H}[S,d_1,d_2,d_3]$ which applies $R\to S$ to each of the four coordinates. Tensoring this with the structure map $S\to\mathbb{H}[S,d_1,d_2,d_3]$ gives `baseChangeHom`, the $S$-algebra homomorphism $S\otimes_R\mathbb{H}[R,c_1,c_2,c_3]\to\mathbb{H}[S,d_1,d_2,d_3]$ sending $s\otimes x$ to the quadruple $(s\,\overline{x_0},s\,\overline{x_1},s\,\overline{x_2},s\,\overline{x_3})$, where the bar is $R\to S$ on coordinates. The function `baseChangeInv` is the explicit candidate inverse $q\mapsto q_{\mathrm{re}}\otimes1+q_{\mathrm{imI}}\otimes i+q_{\mathrm{imJ}}\otimes j+q_{\mathrm{imK}}\otimes k$; it is additive and is shown to be a two-sided inverse of `baseChangeHom`, so `baseChange` is an $S$-algebra isomorphism $S\otimes_R\mathbb{H}[R,c_1,c_2,c_3]\simeq\mathbb{H}[S,d_1,d_2,d_3]$, with `baseChange_tmul` and `baseChange_symm_apply` recording its values and those of its inverse. Composing with the commutativity isomorphism of the tensor product yields `baseChangeRight`, an isomorphism of $R$-algebras $\mathbb{H}[R,c_1,c_2,c_3]\otimes_R S\simeq\mathbb{H}[S,d_1,d_2,d_3]$, with $x\otimes s\mapsto s\bar x$, in particular $1\otimes s\mapsto s$ and $x\otimes1\mapsto\bar x$, together with the corresponding formula for its inverse. Stating the hypotheses as equalities $\mathrm{algebraMap}\,R\,S\,c_i=d_i$, rather than writing the target with those images, lets the two-parameter algebras $\mathbb{H}[R,a,b]$ (where $c_2=0$) be base-changed as well.
--
--   **Relation to Mathlib.** Built on Mathlib's `QuaternionAlgebra` with its `QuaternionAlgebra.Basis` structure and `Basis.liftHom`, and on `Algebra.TensorProduct.lift`; the coordinatewise map and the two base-change isomorphisms are the project's own additions.
--
--   **Where it is used.** These isomorphisms let a quaternion algebra over $\mathbb{Q}$ be compared with the quaternion algebra over a completion $\mathbb{Q}_v$ defined by the same parameters, which is how local data at a place is extracted from a global definite quaternion algebra in the quaternionic automorphic forms part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_QuaternionAlgebra_BaseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion

noncomputable section

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable {c₁ c₂ c₃ : R} {d₁ d₂ d₃ : S}

def Basis.ofAlgebraMapEq (h₁ : algebraMap R S c₁ = d₁) (h₂ : algebraMap R S c₂ = d₂)
    (h₃ : algebraMap R S c₃ = d₃) :
    QuaternionAlgebra.Basis (R := R) ℍ[S,d₁,d₂,d₃] c₁ c₂ c₃ where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by
    rw [← algebraMap_smul S c₁, ← algebraMap_smul S c₂, h₁, h₂]
    ext <;> simp
  j_mul_j := by
    rw [← algebraMap_smul S c₃, h₃]
    ext <;> simp
  i_mul_j := by ext <;> simp
  j_mul_i := by
    rw [← algebraMap_smul S c₂, h₂]
    ext <;> simp

variable (h₁ : algebraMap R S c₁ = d₁) (h₂ : algebraMap R S c₂ = d₂) (h₃ : algebraMap R S c₃ = d₃)

def mapOfAlgebraMapEq : ℍ[R,c₁,c₂,c₃] →ₐ[R] ℍ[S,d₁,d₂,d₃] :=
  (Basis.ofAlgebraMapEq h₁ h₂ h₃).liftHom

@[simp] theorem mapOfAlgebraMapEq_apply (x : ℍ[R,c₁,c₂,c₃]) :
    mapOfAlgebraMapEq h₁ h₂ h₃ x =
      ⟨algebraMap R S x.re, algebraMap R S x.imI, algebraMap R S x.imJ, algebraMap R S x.imK⟩ := by
  rw [mapOfAlgebraMapEq, Basis.liftHom_apply]
  unfold Basis.lift
  rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul S x.re, ← algebraMap_smul S x.imI,
    ← algebraMap_smul S x.imJ, ← algebraMap_smul S x.imK]
  ext <;> simp [Basis.ofAlgebraMapEq] <;> simp [Algebra.smul_def]

def baseChangeHom : S ⊗[R] ℍ[R,c₁,c₂,c₃] →ₐ[S] ℍ[S,d₁,d₂,d₃] :=
  Algebra.TensorProduct.lift (Algebra.ofId S ℍ[S,d₁,d₂,d₃]) (mapOfAlgebraMapEq h₁ h₂ h₃)
    (fun s _ => Algebra.commute_algebraMap_left s _)

theorem baseChangeHom_tmul (s : S) (x : ℍ[R,c₁,c₂,c₃]) :
    baseChangeHom h₁ h₂ h₃ (s ⊗ₜ[R] x) =
      ⟨s * algebraMap R S x.re, s * algebraMap R S x.imI, s * algebraMap R S x.imJ,
        s * algebraMap R S x.imK⟩ := by
  rw [baseChangeHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, mapOfAlgebraMapEq_apply,
    ← Algebra.smul_def]
  ext <;> simp

def baseChangeInv (q : ℍ[S,d₁,d₂,d₃]) : S ⊗[R] ℍ[R,c₁,c₂,c₃] :=
  q.re ⊗ₜ[R] (1 : ℍ[R,c₁,c₂,c₃]) + q.imI ⊗ₜ[R] (⟨0, 1, 0, 0⟩ : ℍ[R,c₁,c₂,c₃]) +
    q.imJ ⊗ₜ[R] (⟨0, 0, 1, 0⟩ : ℍ[R,c₁,c₂,c₃]) + q.imK ⊗ₜ[R] (⟨0, 0, 0, 1⟩ : ℍ[R,c₁,c₂,c₃])

theorem baseChangeInv_add (q q' : ℍ[S,d₁,d₂,d₃]) :
    (baseChangeInv (q + q') : S ⊗[R] ℍ[R,c₁,c₂,c₃]) = baseChangeInv q + baseChangeInv q' := by
  simp only [baseChangeInv]
  rw [show (q + q').re = q.re + q'.re from rfl, show (q + q').imI = q.imI + q'.imI from rfl,
    show (q + q').imJ = q.imJ + q'.imJ from rfl, show (q + q').imK = q.imK + q'.imK from rfl]
  simp only [TensorProduct.add_tmul]
  abel

theorem baseChangeHom_baseChangeInv (q : ℍ[S,d₁,d₂,d₃]) :
    baseChangeHom h₁ h₂ h₃ (baseChangeInv q) = q := by
  simp only [baseChangeInv, map_add, baseChangeHom_tmul]
  ext <;> simp

theorem baseChangeInv_baseChangeHom (x : S ⊗[R] ℍ[R,c₁,c₂,c₃]) :
    baseChangeInv (baseChangeHom h₁ h₂ h₃ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      simp [baseChangeInv]
  | tmul s y =>
      have aux : ∀ (r : R) (e : ℍ[R,c₁,c₂,c₃]), (s * algebraMap R S r) ⊗ₜ[R] e = s ⊗ₜ[R] (r • e) := by
        intro r e
        rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
      rw [baseChangeHom_tmul]
      simp only [baseChangeInv, aux, ← TensorProduct.tmul_add]
      congr 1
      ext <;> simp
  | add x y hx hy => rw [map_add, baseChangeInv_add, hx, hy]

def baseChange : S ⊗[R] ℍ[R,c₁,c₂,c₃] ≃ₐ[S] ℍ[S,d₁,d₂,d₃] :=
  AlgEquiv.ofBijective (baseChangeHom h₁ h₂ h₃)
    ⟨Function.LeftInverse.injective (g := baseChangeInv) (baseChangeInv_baseChangeHom h₁ h₂ h₃),
      Function.RightInverse.surjective (g := baseChangeInv) (baseChangeHom_baseChangeInv h₁ h₂ h₃)⟩

theorem baseChange_apply (x : S ⊗[R] ℍ[R,c₁,c₂,c₃]) :
    baseChange h₁ h₂ h₃ x = baseChangeHom h₁ h₂ h₃ x := rfl

@[simp] theorem baseChange_tmul (s : S) (x : ℍ[R,c₁,c₂,c₃]) :
    baseChange h₁ h₂ h₃ (s ⊗ₜ[R] x) =
      ⟨s * algebraMap R S x.re, s * algebraMap R S x.imI, s * algebraMap R S x.imJ,
        s * algebraMap R S x.imK⟩ :=
  baseChangeHom_tmul h₁ h₂ h₃ s x

theorem baseChange_symm_apply (q : ℍ[S,d₁,d₂,d₃]) :
    (baseChange h₁ h₂ h₃).symm q = baseChangeInv q :=
  (baseChange h₁ h₂ h₃).injective (by
    rw [AlgEquiv.apply_symm_apply, baseChange_apply, baseChangeHom_baseChangeInv])

def baseChangeRight : ℍ[R,c₁,c₂,c₃] ⊗[R] S ≃ₐ[R] ℍ[S,d₁,d₂,d₃] :=
  (Algebra.TensorProduct.comm R ℍ[R,c₁,c₂,c₃] S).trans ((baseChange h₁ h₂ h₃).restrictScalars R)

@[simp] theorem baseChangeRight_tmul (x : ℍ[R,c₁,c₂,c₃]) (s : S) :
    baseChangeRight h₁ h₂ h₃ (x ⊗ₜ[R] s) =
      ⟨s * algebraMap R S x.re, s * algebraMap R S x.imI, s * algebraMap R S x.imJ,
        s * algebraMap R S x.imK⟩ := by
  rw [baseChangeRight, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    AlgEquiv.restrictScalars_apply, baseChange_tmul]

theorem baseChangeRight_one_tmul (s : S) :
    baseChangeRight h₁ h₂ h₃ ((1 : ℍ[R,c₁,c₂,c₃]) ⊗ₜ[R] s) = algebraMap S ℍ[S,d₁,d₂,d₃] s := by
  rw [baseChangeRight_tmul, Algebra.algebraMap_eq_smul_one]
  ext <;> simp

theorem baseChangeRight_tmul_one (x : ℍ[R,c₁,c₂,c₃]) :
    baseChangeRight h₁ h₂ h₃ (x ⊗ₜ[R] (1 : S)) =
      ⟨algebraMap R S x.re, algebraMap R S x.imI, algebraMap R S x.imJ, algebraMap R S x.imK⟩ := by
  rw [baseChangeRight_tmul]
  ext <;> simp

theorem baseChangeRight_symm_apply (q : ℍ[S,d₁,d₂,d₃]) :
    (baseChangeRight h₁ h₂ h₃).symm q =
      (1 : ℍ[R,c₁,c₂,c₃]) ⊗ₜ[R] q.re + (⟨0, 1, 0, 0⟩ : ℍ[R,c₁,c₂,c₃]) ⊗ₜ[R] q.imI +
        (⟨0, 0, 1, 0⟩ : ℍ[R,c₁,c₂,c₃]) ⊗ₜ[R] q.imJ + (⟨0, 0, 0, 1⟩ : ℍ[R,c₁,c₂,c₃]) ⊗ₜ[R] q.imK := by
  apply (baseChangeRight h₁ h₂ h₃).injective
  rw [AlgEquiv.apply_symm_apply]
  simp only [map_add, baseChangeRight_tmul]
  ext <;> simp

end QuaternionAlgebra

end


