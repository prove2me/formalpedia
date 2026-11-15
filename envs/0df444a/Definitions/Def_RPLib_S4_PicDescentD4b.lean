-- Prove2me | Definitions.Def_RPLib_S4_PicDescentD4b
-- name    : RPLib_S4_PicDescentD4b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:32:16.4422+00:00
-- url     : https://prove2.me/theorems/e9019c56-56d1-4268-8f3f-3261f48c384c
-- title:
--   Contraction of places for a constant field extension of a function field
-- statement:
--   For a constant field extension $F' = F \otimes_{\mathbb{F}_q} L$ of a function field $F$, the file assembles the ring pairs at the finite and infinite parts into a contraction map $P' \mapsto P$ from places of $F'/L$ to places of $F/\mathbb{F}_q$ with $\operatorname{ord}_{P'} = \operatorname{ord}_P$ on $F$, finite nonempty fibres with $$\sum_{P' \mid P} \deg_L P' = \deg P,$$ and the action of $\operatorname{Gal}(L/\mathbb{F}_q)$ on places compatible with contraction and orders, transitive on fibres.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.6 (Theorem 3.6.3); M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8

import Definitions.Def_RPLib_S4_PicDescentD4a

/-!
# S4-PicDescent, part D4b: contraction of places for a constant field extension

For `h : RR.IsConstExt Fq F L F' c`: the ring pairs `Rfin(F) → Rfin(F')`, `Rinf(F) → Rinf(F')` (`algFin`, `algInf`,
towers), `contract : Place L F' → Place Fq F`, `ord_contract` (orders agree), the finite fibres `fibre h P`
(`mem_fibre`), `sum_deg_fibre` (`Σ_{P' | P} deg_L P' = deg P`), `exists_contract_eq`,
the Galois action on places `plE h τ` with `contract_plE`, `ord_plE`, `exists_plE_of_contract_eq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places

section ConstPlaces

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

variable (Fq F) in
theorem injFin : Function.Injective (algebraMap (Rfin Fq F) F) := Subtype.val_injective

variable (Fq F) in
theorem injInf : Function.Injective (algebraMap (Rinf Fq F) F) := Subtype.val_injective

/-- `Rfin(F) → Rfin(F')`. -/
noncomputable def algFin : Algebra (Rfin Fq F) (Rfin L F') :=
  (toA' h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin).toAlgebra

/-- `Rinf(F) → Rinf(F')`. -/
noncomputable def algInf : Algebra (Rinf Fq F) (Rinf L F') :=
  (toA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf).toAlgebra

theorem towerFin : letI := algFin h; IsScalarTower (Rfin Fq F) (Rfin L F') F' := by
  letI := algFin h
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply (Rfin Fq F) F F' a]
  exact (algebraMap_toA' h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin a).symm

theorem towerInf : letI := algInf h; IsScalarTower (Rinf Fq F) (Rinf L F') F' := by
  letI := algInf h
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply (Rinf Fq F) F F' a]
  exact (algebraMap_toA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf a).symm

/-- Contraction of finite places. -/
noncomputable def contFin (w : HeightOneSpectrum (Rfin L F')) : HeightOneSpectrum (Rfin Fq F) :=
  letI := algFin h; haveI := towerFin h
  cont h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin w

/-- Contraction of places over `∞`. -/
noncomputable def contInf (w : HeightOneSpectrum (Rinf L F')) : HeightOneSpectrum (Rinf Fq F) :=
  letI := algInf h; haveI := towerInf h
  cont h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf w

/-- **Contraction** `P' ↦ P' ∩ F`. -/
noncomputable def contract : Place L F' → Place Fq F := Sum.map (contFin h) (contInf h)

/-- **Orders agree**: `ord_{P' ∩ F} f = ord_{P'} f`. -/
theorem ord_contract (P' : Place L F') (f : F) : (contract h P').ord f = P'.ord (algebraMap F F' f) := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact ord_cont h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin w f
  · letI := algInf h; haveI := towerInf h
    exact ord_cont h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf w f

theorem finite_contFin (v : HeightOneSpectrum (Rfin Fq F)) : {w | contFin h w = v}.Finite := by
  letI := algFin h; haveI := towerFin h
  exact finite_cont h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin v

theorem finite_contInf (v : HeightOneSpectrum (Rinf Fq F)) : {w | contInf h w = v}.Finite := by
  letI := algInf h; haveI := towerInf h
  exact finite_cont h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf v

/-- The places of `F'` over `P`. -/
noncomputable def fibre : Place Fq F → Finset (Place L F') :=
  Sum.elim (fun v => (finite_contFin h v).toFinset.map Function.Embedding.inl)
    (fun v => (finite_contInf h v).toFinset.map Function.Embedding.inr)

theorem mem_fibre (P : Place Fq F) (P' : Place L F') : P' ∈ fibre h P ↔ contract h P' = P := by
  rcases P with v | v <;> rcases P' with w | w <;>
    simp [fibre, contract, Set.Finite.mem_toFinset]

theorem exists_contract_eq (P : Place Fq F) : ∃ P' : Place L F', contract h P' = P := by
  rcases P with v | v
  · letI := algFin h; haveI := towerFin h
    obtain ⟨w, hw⟩ := exists_cont_eq h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin v
    exact ⟨Sum.inl w, congrArg Sum.inl hw⟩
  · letI := algInf h; haveI := towerInf h
    obtain ⟨w, hw⟩ := exists_cont_eq h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf v
    exact ⟨Sum.inr w, congrArg Sum.inr hw⟩

/-- **`Σ_{P' | P} deg_L P' = deg P`**. -/
theorem sum_deg_fibre (P : Place Fq F) : ∑ P' ∈ fibre h P, P'.deg = P.deg := by
  rcases P with v | v
  · letI := algFin h; haveI := towerFin h
    simp only [fibre, Sum.elim_inl, Finset.sum_map, Function.Embedding.inl_apply, Place.deg_inl]
    exact sum_deg_cont h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin v
  · letI := algInf h; haveI := towerInf h
    simp only [fibre, Sum.elim_inr, Finset.sum_map, Function.Embedding.inr_apply, Place.deg_inr]
    exact sum_deg_cont h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf v

/-- `Gal(L/Fq)` acting on the places of `F'`: `P' ↦ τ⁻¹ P'`. -/
noncomputable def plE (τ : L ≃ₐ[Fq] L) : Place L F' ≃ Place L F' :=
  letI := algFin h; haveI := towerFin h; letI := algInf h; haveI := towerInf h
  Equiv.sumCongr (plEquiv h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin τ)
    (plEquiv h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf τ)

theorem contract_plE (τ : L ≃ₐ[Fq] L) (P' : Place L F') : contract h (plE h τ P') = contract h P' := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact congrArg Sum.inl (cont_pullH h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin τ w)
  · letI := algInf h; haveI := towerInf h
    exact congrArg Sum.inr (cont_pullH h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf τ w)

/-- **Transport of orders**: `ord_{τ⁻¹ P'} f = ord_{P'} (gal τ f)`. -/
theorem ord_plE (τ : L ≃ₐ[Fq] L) (P' : Place L F') (f : F') :
    (plE h τ P').ord f = P'.ord (gal h.linearIndependent h.span τ f) := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact ord_pullH h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin τ w f
  · letI := algInf h; haveI := towerInf h
    exact ord_pullH h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf τ w f

/-- **Transitivity on fibres.** -/
theorem exists_plE_of_contract_eq (P1 P2 : Place L F') (h12 : contract h P1 = contract h P2) :
    ∃ τ : L ≃ₐ[Fq] L, P2 = plE h τ P1 := by
  rcases P1 with w1 | w1 <;> rcases P2 with w2 | w2
  · letI := algFin h; haveI := towerFin h
    obtain ⟨τ, hτ⟩ := exists_pullH_of_cont_eq h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin
      w1 w2 (Sum.inl_injective h12)
    exact ⟨τ, congrArg Sum.inl hτ⟩
  · exact absurd h12 Sum.inl_ne_inr
  · exact absurd h12 Sum.inr_ne_inl
  · letI := algInf h; haveI := towerInf h
    obtain ⟨τ, hτ⟩ := exists_pullH_of_cont_eq h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf
      w1 w2 (Sum.inr_injective h12)
    exact ⟨τ, congrArg Sum.inr hτ⟩

end ConstPlaces

end RamanujanPetersson.PicDescent


