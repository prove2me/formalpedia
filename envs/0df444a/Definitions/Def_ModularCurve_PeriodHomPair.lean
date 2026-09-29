-- Prove2me | Definitions.Def_ModularCurve_PeriodHomPair
-- name    : ModularCurve_PeriodHomPair
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/ff611c50-2bff-5be5-8e15-2bd3c549dc56
-- title:
--   J-conjugation, character involution, and the period pair map
-- statement:
--   Three layers of structure on $\Gamma_0(N)$ and on homomorphisms out of it are set up here. First, $J$-conjugation: for an integral $2\times 2$ matrix $A$, `jConjMat A` is $\begin{pmatrix} a & -b \\ -c & d\end{pmatrix}$, i.e. conjugation by $\mathrm{diag}(1,-1)$; the accompanying lemmas record its entries, that it preserves determinant and trace, that it is multiplicative, fixes $1$, and is an involution. Consequently `jConjSL` is an involutive monoid endomorphism of $SL(2,\mathbb{Z})$, it carries $\Gamma_0(N)$ into itself (the lower left entry only changes sign), and `jConjGamma0 N` is the induced involutive monoid endomorphism of $\Gamma_0(N)$. Second, for a semiring $R$ and an $R$-module $A$, `charInvolution N R A` is the $R$-linear endomorphism of $\mathrm{Hom}(\Gamma_0(N)^{\mathrm{add}}, A)$ given by precomposition with $J$-conjugation, $\psi\mapsto \psi\circ\mathrm{jConjGamma0}\,N$; it is an involution, and since $J$-conjugation preserves traces it maps the submodule `parabolicHoms` (homomorphisms vanishing on all $\gamma$ with $\operatorname{tr}(\gamma)^2=4$) into itself. Third, `ExistsPeriodMapLinear N` asserts the existence of a $\mathbb{C}$-linear map $S_2(\Gamma_0(N))=$ `CuspForm (Gamma0 N) 2` $\to \mathrm{Hom}(\Gamma_0(N)^{\mathrm{add}},\mathbb{C})$ agreeing pointwise with `periodMap N`, the period homomorphism $\gamma\mapsto F(\gamma\cdot i)-F(i)$ attached to a chosen equivariant primitive $F$ of the form. Granting this predicate, `periodHomPair N` is the $\mathbb{C}$-linear map on pairs of cusp forms sending $(f,g)$ to $(\mathrm{id}+\iota^{*})\Lambda(f)+(\mathrm{id}-\iota^{*})\Lambda(g)$, where $\Lambda$ is such a linear period map and $\iota^{*}=$ `charInvolution N ℂ ℂ`; when the predicate fails the definition returns the zero map. The unfolding lemma `periodHomPair_def` exhibits, from a proof of the predicate, a linear $\Lambda$ agreeing with `periodMap N` together with the resulting description of `periodHomPair N` as a coproduct of the two composites.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient objects ($SL(2,\mathbb{Z})$, the congruence subgroups `Gamma0`, `CuspForm`, `Additive`, `LinearMap.coprod`); the $J$-conjugation of $\Gamma_0(N)$, the involution on homomorphism modules and the period maps are the project's own notions.
--
--   **Where it is used.** The period homomorphisms attached to weight-two cusp forms on $\Gamma_0(N)$, together with the splitting into plus and minus parts under the involution induced by $\mathrm{diag}(1,-1)$, form the analytic side of the comparison between $S_2(\Gamma_0(N))$ and the first cohomology of the modular curve used in the modularity arguments of the proof of Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_PeriodHomPair.lean

import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodMapBundled
import Mathlib.LinearAlgebra.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve.Period

section JConj

def jConjMat (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 0 0, -A 0 1; -A 1 0, A 1 1]

@[simp] theorem jConjMat_apply_zero_zero (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 0 0 = A 0 0 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_zero_one (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 0 1 = -A 0 1 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_one_zero (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 1 0 = -A 1 0 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_one_one (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 1 1 = A 1 1 := by simp [jConjMat]

theorem jConjMat_det (A : Matrix (Fin 2) (Fin 2) ℤ) : (jConjMat A).det = A.det := by
  rw [jConjMat, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring

theorem jConjMat_trace (A : Matrix (Fin 2) (Fin 2) ℤ) : (jConjMat A).trace = A.trace := by
  rw [jConjMat, Matrix.trace_fin_two_of, Matrix.trace_fin_two]

theorem jConjMat_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat (A * B) = jConjMat A * jConjMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jConjMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem jConjMat_jConjMat (A : Matrix (Fin 2) (Fin 2) ℤ) : jConjMat (jConjMat A) = A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jConjMat]

theorem jConjMat_one : jConjMat (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jConjMat]

def jConjSL : SL(2, ℤ) →* SL(2, ℤ) where
  toFun A := ⟨jConjMat ((A : Matrix (Fin 2) (Fin 2) ℤ)), by rw [jConjMat_det]; exact A.2⟩
  map_one' := by
    apply Subtype.ext
    show jConjMat ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
    rw [Matrix.SpecialLinearGroup.coe_one, jConjMat_one]
  map_mul' A B := by
    apply Subtype.ext
    show jConjMat (((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, jConjMat_mul]; rfl

@[simp] theorem jConjSL_coe (A : SL(2, ℤ)) :
    ((jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = jConjMat ((A : Matrix (Fin 2) (Fin 2) ℤ)) := rfl

theorem jConjSL_jConjSL (A : SL(2, ℤ)) : jConjSL (jConjSL A) = A := by
  apply Subtype.ext; rw [jConjSL_coe, jConjSL_coe, jConjMat_jConjMat]

theorem jConjSL_mem_Gamma0 {N : ℕ} {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) :
    jConjSL A ∈ Gamma0 N := by
  have hA' : ((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 :=
    Gamma0_mem.mp hA
  rw [Gamma0_mem]
  show ((((jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0
  rw [jConjSL_coe, jConjMat_apply_one_zero]; push_cast; rw [hA', neg_zero]

variable (N : ℕ)

def jConjGamma0 : Gamma0 N →* Gamma0 N where
  toFun γ := ⟨jConjSL ↑γ, jConjSL_mem_Gamma0 γ.2⟩
  map_one' := by apply Subtype.ext; show jConjSL ↑(1 : Gamma0 N) = _;
                 rw [OneMemClass.coe_one, map_one]
  map_mul' γ δ := by apply Subtype.ext; show jConjSL ↑(γ * δ) = _;
                     rw [MulMemClass.coe_mul, map_mul]; rfl

@[simp] theorem jConjGamma0_coe (γ : Gamma0 N) :
    ((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) = jConjSL ↑γ := rfl

theorem jConjGamma0_jConjGamma0 (γ : Gamma0 N) :
    jConjGamma0 N (jConjGamma0 N γ) = γ := by
  apply Subtype.ext; rw [jConjGamma0_coe, jConjGamma0_coe, jConjSL_jConjSL]

end JConj

section CharInvolution

variable (N : ℕ) (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A]

def charInvolution : (Additive (Gamma0 N) →+ A) →ₗ[R] (Additive (Gamma0 N) →+ A) where
  toFun ψ := ψ.comp (MonoidHom.toAdditive (jConjGamma0 N))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem charInvolution_apply (ψ : Additive (Gamma0 N) →+ A) (γ : Additive (Gamma0 N)) :
    (charInvolution N R A ψ) γ = ψ (Additive.ofMul (jConjGamma0 N (Additive.toMul γ))) := rfl

theorem charInvolution_charInvolution (ψ : Additive (Gamma0 N) →+ A) :
    charInvolution N R A (charInvolution N R A ψ) = ψ := by
  refine AddMonoidHom.ext fun γ => ?_
  show ψ (Additive.ofMul (jConjGamma0 N (jConjGamma0 N (Additive.toMul γ)))) = ψ γ
  rw [jConjGamma0_jConjGamma0]; rfl

theorem charInvolution_mem_parabolicHoms {ψ : Additive (Gamma0 N) →+ A}
    (hψ : ψ ∈ parabolicHoms R (Gamma0 N) A) :
    charInvolution N R A ψ ∈ parabolicHoms R (Gamma0 N) A := by
  rw [mem_parabolicHoms_iff] at hψ ⊢
  intro γ hγ
  refine hψ (jConjGamma0 N γ) ?_
  have htr : (((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
    rw [jConjGamma0_coe, jConjSL_coe, jConjMat_trace]
  rw [htr]; exact hγ

end CharInvolution

end ModularCurve.Period

namespace ModularCurve

section PeriodHomPair

open ModularCurve.Period

variable (N : ℕ)

def ExistsPeriodMapLinear : Prop :=
  ∃ pml : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ), ∀ f, pml f = periodMap N f

noncomputable def periodHomPair :
    (CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ) :=
  open scoped Classical in
  if h : ExistsPeriodMapLinear N then
    LinearMap.coprod
      ((LinearMap.id + charInvolution N ℂ ℂ) ∘ₗ h.choose)
      ((LinearMap.id - charInvolution N ℂ ℂ) ∘ₗ h.choose)
  else 0

theorem periodHomPair_def (h : ExistsPeriodMapLinear N) :
    ∃ (pml : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ))
      (_ : ∀ f, pml f = periodMap N f),
      periodHomPair N = LinearMap.coprod
        ((LinearMap.id + charInvolution N ℂ ℂ) ∘ₗ pml)
        ((LinearMap.id - charInvolution N ℂ ℂ) ∘ₗ pml) := by
  refine ⟨h.choose, h.choose_spec, ?_⟩
  unfold periodHomPair
  rw [dif_pos h]

end PeriodHomPair

end ModularCurve


