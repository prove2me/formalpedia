-- Prove2me | Definitions.Def_ModularCurve_PeriodTransfer
-- name    : ModularCurve_PeriodTransfer
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/2c0ff31f-65a3-5f33-8651-e81e1bf8370e
-- title:
--   Conjugation and trace transports of equivariant primitives
-- statement:
--   Throughout, $\Gamma,\Delta$ are subgroups of $\mathrm{SL}_2(\mathbb{Z})$ and $F:\mathbb{H}\to\mathbb{C}$ a function; `IsEquivariantPrimitive Γ F` means that for every $\gamma\in\Gamma$ the difference $z\mapsto F(\gamma\cdot z)-F(z)$ is a constant, and `IsEquivariantPrimitive.period` evaluates that constant as $F(\gamma\cdot i)-F(i)$.
--
--   The first half treats conjugation. For $g\in\mathrm{GL}_2(\mathbb{R})$, the relation `conjRel g γ' γ` is the equation $g\,\iota(\gamma')=\iota(\gamma)\,g$ in $\mathrm{GL}_2(\mathbb{R})$, where $\iota$ is the map `Matrix.SpecialLinearGroup.mapGL` from $\mathrm{SL}_2(\mathbb{Z})$ to $\mathrm{GL}_2(\mathbb{R})$; thus $\gamma=g\gamma'g^{-1}$, expressed without inverses. It is shown to hold for the pair $(1,1)$, to be compatible with products and with inverses, to determine $\gamma$ uniquely from $\gamma'$, and to give $g\cdot(\gamma'\cdot z)=\gamma\cdot(g\cdot z)$ for the Möbius action on $\mathbb{H}$. `conjSubgroup g Γ` is the subgroup of those $\gamma'$ for which some $\gamma\in\Gamma$ satisfies `conjRel g γ' γ`, `conjPrimitive g F` is $z\mapsto F(g\cdot z)$, and these carry equivariant primitives to equivariant primitives.
--
--   The second half treats the trace from $\Delta$ to $\Gamma$, under the standing assumption that the coset space $\Gamma/(\Delta\cap\Gamma)$ is finite. For a coset $q$, `traceRep q` is the inverse of a chosen representative, and `transferElt γ q` is the element of $\Delta$ given by the transfer cocycle [`HeckeEis.transferAux`](../def/Gamma0HeckeOperatorHom.html#L216) at $\gamma^{-1}q$; `transferElt_spec` records the factorisation $\mathrm{traceRep}(q)\,\gamma=\mathrm{transferElt}(\gamma,q)\cdot\mathrm{traceRep}(\gamma^{-1}q)$. `traceSum Γ Δ F` is $z\mapsto\sum_q F(\mathrm{traceRep}(q)\cdot z)$, and for an equivariant primitive $F$ over $\Delta$ its difference at $\gamma\in\Gamma$ equals $\sum_q$ of the periods of $F$ at the transfer elements, so the trace sum is an equivariant primitive over $\Gamma$ whose period homomorphism is the transfer of that of $F$.
--
--   **Relation to Mathlib.** Mathlib has no notion of an equivariant primitive on $\mathbb{H}$ or of its period homomorphism; these, the conjugation relation `conjRel` and the trace sum are the project's own, built on Mathlib's Möbius action of $\mathrm{GL}_2(\mathbb{R})$ on $\mathbb{H}$ and on the map `Matrix.SpecialLinearGroup.mapGL`. The transfer cocycle used here is the project's [`HeckeEis.transferAux`](../def/Gamma0HeckeOperatorHom.html#L216).
--
--   **Where it is used.** These two transports convert a primitive over one subgroup into a primitive over a conjugate or a larger subgroup, and match the resulting period homomorphisms with the transfer and pullback maps out of which the Hecke operators on homomorphisms from $\Gamma_0(N)$ are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_PeriodTransfer.lean

import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_Gamma0HeckeOperatorHom
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix UpperHalfPlane CongruenceSubgroup Function

open scoped MatrixGroups

noncomputable section

namespace ModularCurve.Period

variable {Γ Δ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

def conjRel (g : GL (Fin 2) ℝ) (γ' γ : SL(2, ℤ)) : Prop :=
  g * Matrix.SpecialLinearGroup.mapGL ℝ γ' = Matrix.SpecialLinearGroup.mapGL ℝ γ * g

namespace conjRel

variable {g : GL (Fin 2) ℝ}

theorem one : conjRel g 1 1 := by
  simp [conjRel]

theorem mul {γ₁' γ₂' γ₁ γ₂ : SL(2, ℤ)} (h₁ : conjRel g γ₁' γ₁) (h₂ : conjRel g γ₂' γ₂) :
    conjRel g (γ₁' * γ₂') (γ₁ * γ₂) := by
  unfold conjRel at *
  rw [map_mul, map_mul, ← mul_assoc, h₁, mul_assoc, h₂, mul_assoc]

theorem inv {γ' γ : SL(2, ℤ)} (h : conjRel g γ' γ) : conjRel g γ'⁻¹ γ⁻¹ := by
  unfold conjRel at *
  rw [map_inv, map_inv]
  calc g * (Matrix.SpecialLinearGroup.mapGL ℝ γ')⁻¹
      = (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
          * ((Matrix.SpecialLinearGroup.mapGL ℝ γ * g)
            * (Matrix.SpecialLinearGroup.mapGL ℝ γ')⁻¹) := by group
    _ = (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
          * ((g * Matrix.SpecialLinearGroup.mapGL ℝ γ')
            * (Matrix.SpecialLinearGroup.mapGL ℝ γ')⁻¹) := by rw [h]
    _ = (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ * g := by group

theorem unique {γ' γ₁ γ₂ : SL(2, ℤ)} (h₁ : conjRel g γ' γ₁) (h₂ : conjRel g γ' γ₂) :
    γ₁ = γ₂ := by
  have hGL : Matrix.SpecialLinearGroup.mapGL ℝ γ₁ = Matrix.SpecialLinearGroup.mapGL ℝ γ₂ :=
    mul_right_cancel (h₁.symm.trans h₂)
  have hmat : ∀ a b : Fin 2, (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) a b
      = (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) a b := by
    intro a b
    have := congrArg (fun M : GL (Fin 2) ℝ => (M : Matrix (Fin 2) (Fin 2) ℝ) a b) hGL
    simpa [Matrix.SpecialLinearGroup.mapGL, Int.cast_injective.eq_iff] using this
  ext a b
  exact hmat a b

theorem smul_comm {γ' γ : SL(2, ℤ)} (h : conjRel g γ' γ) (z : ℍ) :
    g • (γ' • z) = γ • (g • z) := by
  rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, ← mul_smul, h, mul_smul]

end conjRel

def conjSubgroup (g : GL (Fin 2) ℝ) (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {γ' | ∃ γ ∈ Γ, conjRel g γ' γ}
  one_mem' := ⟨1, Γ.one_mem, conjRel.one⟩
  mul_mem' := by
    rintro γ₁' γ₂' ⟨γ₁, hγ₁, h₁⟩ ⟨γ₂, hγ₂, h₂⟩
    exact ⟨γ₁ * γ₂, Γ.mul_mem hγ₁ hγ₂, h₁.mul h₂⟩
  inv_mem' := by
    rintro γ' ⟨γ, hγ, h⟩
    exact ⟨γ⁻¹, Γ.inv_mem hγ, h.inv⟩

def conjPrimitive (g : GL (Fin 2) ℝ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun z => F (g • z)

theorem IsEquivariantPrimitive.conj (g : GL (Fin 2) ℝ)
    (hF : IsEquivariantPrimitive Γ F) :
    IsEquivariantPrimitive (conjSubgroup g Γ) (conjPrimitive g F) := by
  rintro ⟨γ', γ, hγ, hrel⟩
  refine ⟨hF.period ⟨γ, hγ⟩, fun z => ?_⟩
  show F (g • (γ' • z)) - F (g • z) = _
  rw [hrel.smul_comm z]
  exact hF.sub_eq_period ⟨γ, hγ⟩ (g • z)

def traceRep (q : ↥Γ ⧸ Δ.subgroupOf Γ) : ↥Γ :=
  (Quotient.out q)⁻¹

def transferElt (γ : ↥Γ) (q : ↥Γ ⧸ Δ.subgroupOf Γ) : ↥Δ :=
  ⟨((HeckeEis.transferAux (Δ.subgroupOf Γ) γ (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)),
    Subgroup.mem_subgroupOf.mp (HeckeEis.transferAux (Δ.subgroupOf Γ) γ (γ⁻¹ • q)).2⟩

theorem transferElt_spec (γ : ↥Γ) (q : ↥Γ ⧸ Δ.subgroupOf Γ) :
    ((traceRep q : ↥Γ) : SL(2, ℤ)) * (γ : SL(2, ℤ))
      = (transferElt (Δ := Δ) γ q : SL(2, ℤ))
        * ((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) := by
  have h : traceRep q * γ
      = (HeckeEis.transferAux (Δ.subgroupOf Γ) γ (γ⁻¹ • q) : ↥Γ) * traceRep (γ⁻¹ • q) := by
    rw [HeckeEis.coe_transferAux, smul_inv_smul]
    unfold traceRep
    group
  exact congrArg (fun x : ↥Γ => (x : SL(2, ℤ))) h

variable [Fintype (↥Γ ⧸ Δ.subgroupOf Γ)]

def traceSum (Γ Δ : Subgroup SL(2, ℤ)) [Fintype (↥Γ ⧸ Δ.subgroupOf Γ)] (F : ℍ → ℂ) :
    ℍ → ℂ :=
  fun z => ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z)

theorem sum_traceRep_smul_sub (hF : IsEquivariantPrimitive Δ F) (γ : ↥Γ) (z : ℍ) :
    traceSum Γ Δ F ((γ : SL(2, ℤ)) • z) - traceSum Γ Δ F z
      = ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, hF.period (transferElt γ q) := by
  have hterm : ∀ q : ↥Γ ⧸ Δ.subgroupOf Γ,
      F (((traceRep q : ↥Γ) : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z))
        = F (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z)
          + hF.period (transferElt γ q) := by
    intro q
    have h1 : ((traceRep q : ↥Γ) : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z)
        = ((transferElt (Δ := Δ) γ q : SL(2, ℤ)))
            • (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z) := by
      rw [← mul_smul, transferElt_spec γ q, mul_smul]
    rw [h1]
    have h2 := hF.sub_eq_period (transferElt γ q)
      (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z)
    linear_combination h2
  unfold traceSum
  calc
    (∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z)))
        - ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z)
      = (∑ q : ↥Γ ⧸ Δ.subgroupOf Γ,
          (F (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z) + hF.period (transferElt γ q)))
          - ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z) := by
        rw [Finset.sum_congr rfl fun q _ => hterm q]
    _ = (∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z))
          + (∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, hF.period (transferElt γ q))
          - ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, hF.period (transferElt γ q) := by
        rw [(MulAction.bijective (γ⁻¹ : ↥Γ)).sum_comp
          (fun q : ↥Γ ⧸ Δ.subgroupOf Γ => F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z))]
        ring

theorem IsEquivariantPrimitive.traceSum (hF : IsEquivariantPrimitive Δ F) :
    IsEquivariantPrimitive Γ (ModularCurve.Period.traceSum Γ Δ F) := fun γ =>
  ⟨∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, hF.period (transferElt γ q),
    fun z => sum_traceRep_smul_sub hF γ z⟩

end ModularCurve.Period

end


