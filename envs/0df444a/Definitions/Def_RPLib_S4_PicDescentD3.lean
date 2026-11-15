-- Prove2me | Definitions.Def_RPLib_S4_PicDescentD3
-- name    : RPLib_S4_PicDescentD3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:25:58.477532+00:00
-- url     : https://prove2.me/theorems/f94b7901-d480-45b3-bbd9-f10a6111cb63
-- title:
--   The ring pair $A \to L \otimes_{\mathbb{F}_q} A$ of a constant field extension
-- statement:
--   For an $\mathbb{F}_q$-algebra $A$ (a ring of functions of $F$) and the corresponding ring $A' \cong L \otimes_{\mathbb{F}_q} A$ of the constant field extension $F'$, compatible with $F \to F'$, the file proves that $A'$ is free and finite over $A$ of rank $[L : \mathbb{F}_q]$, formally unramified and torsion-free, and that $\operatorname{Gal}(L/\mathbb{F}_q)$ acts on $A'$ with fixed ring $A$ and acts transitively on the places of $A'$ over each place of $A$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8; J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9

import Definitions.Def_RPLib_S4_PicDescentD2

/-!
# S4-PicDescent, part D3: the ring pair `A → A' ≃ L ⊗ A`

Setting of D1 section `Rings` plus an algebra `A → A'` compatible with `F → F'`.
* `algebraMap_A_A'`: `algebraMap A A' = toA'`; `eAB : A ⊗[Fq] L ≃ₐ[A] A'`.
* `moduleFree`, `moduleFinite`, `finrank_A_A'` (`= [L : Fq]`), `formallyUnramified`, `isTorsionFree`.
* `galAct`: `Gal(L/Fq)` acts on `A'` by `galA'`; `smulCommClass`, `isInvariant` (fixed ring `A`),
  `exists_pullH_of_under_eq`: `Gal(L/Fq)` is transitive on the places of `A'` over a place of `A`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct Pointwise
open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section Pair

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))
  {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']
  (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)
  [Algebra A A'] [Algebra A F'] [IsScalarTower A F F'] [IsScalarTower A A' F']

theorem algebraMap_A_A' (a : A) : algebraMap A A' a = toA' hli hsp hA hA' hc a :=
  hA' (by rw [algebraMap_toA', ← IsScalarTower.algebraMap_apply A A' F',
    IsScalarTower.algebraMap_apply A F F'])

/-- `A ⊗[Fq] L ≃ₐ[A] A'`. -/
noncomputable def eAB : A ⊗[Fq] L ≃ₐ[A] A' :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm Fq A L).toRingEquiv.trans
    (tensorEquiv hA hA' hli hsp hc).toRingEquiv) (fun a => by
      rw [algebraMap_A_A' hli hsp hA hA' hc]
      show tensorEquiv hA hA' hli hsp hc (Algebra.TensorProduct.comm Fq A L (a ⊗ₜ 1)) = _
      rw [Algebra.TensorProduct.comm_tmul]
      rfl)

include hA hA' in
theorem algebraMap_A_A'_injective : Function.Injective (algebraMap A A') := by
  intro a b h
  apply hA
  apply (algebraMap F F').injective
  rw [← IsScalarTower.algebraMap_apply A F F', ← IsScalarTower.algebraMap_apply A F F',
    IsScalarTower.algebraMap_apply A A' F', IsScalarTower.algebraMap_apply A A' F' b, h]

include hli hsp hA hA' hc in
theorem moduleFree : Module.Free A A' :=
  Module.Free.of_equiv (eAB hli hsp hA hA' hc).toLinearEquiv

include hli hsp hA hA' hc in
theorem moduleFinite [Module.Finite Fq L] : Module.Finite A A' :=
  Module.Finite.equiv (eAB hli hsp hA hA' hc).toLinearEquiv

include hli hsp hA hA' hc in
theorem finrank_A_A' [Nontrivial A] : Module.finrank A A' = Module.finrank Fq L :=
  (eAB hli hsp hA hA' hc).toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange

include hli hsp hA hA' hc in
theorem formallyUnramified [Algebra.IsSeparable Fq L] : Algebra.FormallyUnramified A A' := by
  haveI := Algebra.FormallyUnramified.of_isSeparable Fq L
  exact Algebra.FormallyUnramified.of_equiv (eAB hli hsp hA hA' hc)

include hA hA' in
theorem isTorsionFree [IsDomain A] [IsDomain A'] : Module.IsTorsionFree A A' :=
  Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_A_A'_injective hA hA')

/-- `galA' τ` fixes `A`. -/
theorem galA'_algebraMap (τ : L ≃ₐ[Fq] L) (a : A) :
    galA' hli hsp hA hA' hc τ (algebraMap A A' a) = algebraMap A A' a :=
  hA' (by rw [algebraMap_galA', ← IsScalarTower.algebraMap_apply A A' F',
    IsScalarTower.algebraMap_apply A F F', AlgEquiv.commutes])

/-- `Gal(L/Fq)` acting on `A'` through `galA'`. -/
noncomputable def galAct : MulSemiringAction (L ≃ₐ[Fq] L) A' :=
  MulSemiringAction.compHom A' (galA'Hom hli hsp hA hA' hc)

theorem galAct_smul (τ : L ≃ₐ[Fq] L) (y : A') :
    (galAct hli hsp hA hA' hc).smul τ y = galA' hli hsp hA hA' hc τ y := rfl

theorem smulCommClass : letI := galAct hli hsp hA hA' hc; SMulCommClass (L ≃ₐ[Fq] L) A A' := by
  letI := galAct hli hsp hA hA' hc
  refine ⟨fun τ a y => ?_⟩
  show galA' hli hsp hA hA' hc τ (a • y) = a • galA' hli hsp hA hA' hc τ y
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, galA'_algebraMap]

theorem isInvariant [Finite L] :
    letI := galAct hli hsp hA hA' hc; Algebra.IsInvariant A A' (L ≃ₐ[Fq] L) := by
  letI := galAct hli hsp hA hA' hc
  refine ⟨fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := exists_toA'_eq hli hsp hA hA' hc y hy
  exact ⟨a, (algebraMap_A_A' hli hsp hA hA' hc a).trans ha⟩

theorem finite_gal [Finite L] : Finite (L ≃ₐ[Fq] L) :=
  Finite.of_injective (fun τ : L ≃ₐ[Fq] L => (τ : L → L)) DFunLike.coe_injective

/-- **Transitivity on fibres**: places of `A'` over the same place of `A` are `Gal(L/Fq)`-conjugate. -/
theorem exists_pullH_of_under_eq [Finite L] [IsDedekindDomain A'] (w1 w2 : HeightOneSpectrum A')
    (h : w1.asIdeal.under A = w2.asIdeal.under A) :
    ∃ τ : L ≃ₐ[Fq] L, w2 = pullH (galA' hli hsp hA hA' hc τ) w1 := by
  letI := galAct hli hsp hA hA' hc
  haveI := smulCommClass hli hsp hA hA' hc
  haveI := isInvariant hli hsp hA hA' hc
  haveI := finite_gal (Fq := Fq) (L := L)
  haveI := w1.isPrime
  haveI := w2.isPrime
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq A A' (L ≃ₐ[Fq] L) w1.asIdeal w2.asIdeal h
  refine ⟨g⁻¹, HeightOneSpectrum.ext ?_⟩
  rw [pullH_asIdeal, hg, Ideal.pointwise_smul_eq_comap]
  ext y
  exact Iff.rfl

end Pair

end RamanujanPetersson.PicDescent


