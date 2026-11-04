-- Prove2me | Definitions.Def_FreeGroupFactorProof24
-- name    : FreeGroupFactorProof24
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:27:39.028473+00:00
-- url     : https://prove2.me/theorems/8aeab8cd-9809-4303-b819-f653b2bb05e0
-- title:
--   Free group factors: supporting development, part 24
-- statement:
--   Part 24 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof23

set_option linter.all false

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

theorem hamiltonianLinear_single_one {ι : Type uι} (S : A) (U : ι → unitary A) :
    hamiltonianLinear S U (Finsupp.single 1 1) = S := by
  simp [hamiltonianLinear]

end
section

variable {A : Type uA} [CStarAlgebra A]

theorem unitary_curve_displacement (S : A) (hS : IsSelfAdjoint S)
    (W : ℝ → unitary A) (H : ℝ → A)
    (hW : ∀ t, HasDerivAt (fun s => (W s : A))
      (Complex.I • (H t * (W t : A))) t)
    (B : ℝ) (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖H t-S‖ ≤ B) :
    ‖(W 1 : A) - NormedSpace.exp (Complex.I • S) * (W 0 : A)‖ ≤ B := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  let E (t : ℝ) : A := NormedSpace.exp (t • (-Complex.I • S))
  have hEu (t : ℝ) : E t ∈ unitary A := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    change star (t • (-Complex.I • S)) = -(t • (-Complex.I • S))
    rw [star_smul, star_smul, star_trivial, star_neg, Complex.star_def,
      Complex.conj_I, neg_neg, hS.star_eq, neg_smul, smul_neg]
    rw [neg_neg]
  let D (t : ℝ) : A := Complex.I • (E t * (H t-S) * (W t : A))
  have hd (t : ℝ) : HasDerivAt (fun s => E s * (W s : A)) (D t) t := by
    have he := hasDerivAt_exp_smul_const (-Complex.I • S) t
    convert he.mul (hW t) using 1
    case e'_8 => rfl
    dsimp [E, D]
    simp only [mul_sub, sub_mul, smul_sub, mul_smul_comm, smul_mul_assoc,
      neg_smul, mul_neg, neg_mul, smul_neg, mul_assoc]
    abel
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖D t‖ ≤ B := by
    dsimp [D]
    rw [norm_smul, Complex.norm_I, one_mul,
      CStarRing.norm_mul_mem_unitary _ (W t).property,
      CStarRing.norm_mem_unitary_mul _ (hEu t)]
    exact hB t ht
  have hm := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb (by simp : (0:ℝ) ∈ Set.Icc 0 1)
    (by simp : (1:ℝ) ∈ Set.Icc 0 1)
  have hE0 : E 0 = 1 := by simp [E]
  have hE1 : E 1 * NormedSpace.exp (Complex.I • S) = 1 := by
    dsimp [E]
    rw [one_smul, neg_smul, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have heq : E 1 * ((W 1 : A) - NormedSpace.exp (Complex.I • S) * (W 0 : A)) =
      E 1 * (W 1 : A) - E 0 * (W 0 : A) := by
    rw [mul_sub, ← mul_assoc, hE1, hE0]
  rw [← heq, CStarRing.norm_mem_unitary_mul _ (hEu 1)] at hm
  simpa using hm

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem hamiltonianLinear_norm_map (Φ : A ≃⋆ₐ[ℂ] A)
    (S : A) (hS : Φ S = S) (U V : ι → unitary A)
    (hUV : ∀ g, Φ (wordHom U g) = wordHom V g) (k : FreeGroup ι →₀ ℝ) :
    ‖hamiltonianLinear S V k‖ = ‖hamiltonianLinear S U k‖ := by
  have he := FreeGroupFactorMain.hamiltonianLinear_map Φ S U V hUV k
  rw [hS] at he
  rw [← he, StarAlgEquiv.norm_map]

omit [Fintype ι] in
theorem generator_displacement (S : A) (h : ι → FreeGroup ι →₀ ℝ)
    (U : ℝ → ι → unitary A)
    (hU : ∀ t, HasDerivAt (fun t j => (U t j : A))
      (PolynomialFlow.field S h (fun j => (U t j : A))) t)
    (B : ι → ℝ) (hb : ∀ t j, ‖hamiltonianLinear S (U t) (h j)‖ ≤ B j) (j : ι) :
    ‖(U 1 j : A) - (U 0 j : A)‖ ≤ B j := by
  have hd := unitary_curve_displacement (0 : A) (by simp)
    (fun t => U t j) (fun t => hamiltonianLinear S (U t) (h j))
    (fun t => by
      simpa only [hamiltonianLinear_eq, PolynomialFlow.field] using
        (hasDerivAt_pi.mp (hU t) j))
    (B j) (fun t _ => by simpa only [sub_zero] using hb t j)
  simpa only [smul_zero, NormedSpace.exp_zero, one_mul] using hd

theorem word_displacement (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) (U : ℝ → ι → unitary A)
    (hU : ∀ t, HasDerivAt (fun t j => (U t j : A))
      (PolynomialFlow.field S h (fun j => (U t j : A))) t)
    (w : FreeGroup ι) (B : ℝ)
    (hb : ∀ t, ‖hamiltonianLinear S (U t) (freeCocycle h w - Finsupp.single 1 1)‖ ≤ B) :
    ‖wordHom (U 1) w - NormedSpace.exp (Complex.I • S) * wordHom (U 0) w‖ ≤ B := by
  apply unitary_curve_displacement S hS (fun t => FreeGroup.lift (U t) w)
    (fun t => hamiltonianLinear S (U t) (freeCocycle h w))
    (fun t => hasDerivAt_wordHom_cocycle S hS h U hU w t)
  intro t _ht
  simpa only [map_sub, FreeGroupFactorMain.hamiltonianLinear_single_one] using hb t

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem wordHom_extend_none_zpow {A : Type uA} [CStarAlgebra A]
    (U : ι → unitary A) (C : unitary A) (m : ℤ) :
    wordHom (extendUnitary U C) (FreeGroup.of none ^ m) = ((C^m : unitary A) : A) := by
  change ((FreeGroup.lift (extendUnitary U C) (FreeGroup.of none ^ m) : unitary A) : A) = _
  simp only [map_zpow, FreeGroup.lift_apply_of, extendUnitary, Option.elim_none]

omit [Fintype ι] [DecidableEq ι] in
theorem flow_iso_fix_laurent (l : ℤ →₀ ℂ)
    (U : ι → unitary (groupVonNeumann (FreeGroup (Option ι))))
    (Φ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)))
    (hΦ : ∀ g, Φ (groupUnitary g) = wordHom (extendUnitary U (generatorUnitary (none : Option ι))) g) :
    Φ (laurentValue (generatorUnitary (none : Option ι)) l) =
      laurentValue (generatorUnitary (none : Option ι)) l := by
  classical
  conv_lhs => rw [laurentValue_group]
  simp only [groupLaurent, Finsupp.sum, map_sum, map_smul, hΦ, wordHom_extend_none_zpow]
  rfl

omit [Fintype ι] in
theorem flow_iso_hamiltonian_bound (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K) (hn : ‖laurentValue (generatorUnitary (none : Option ι)) l‖ ≤ K)
    (U : ι → unitary (groupVonNeumann (FreeGroup (Option ι))))
    (Φ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)))
    (hΦ : ∀ g, Φ (groupUnitary g) = wordHom (extendUnitary U (generatorUnitary (none : Option ι))) g)
    (k : FreeGroup ι →₀ ℝ) :
    ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option ι)) l) U k‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  have hword (g : FreeGroup ι) :
      Φ (wordHom (fun j => generatorUnitary (some j)) g) = wordHom U g := by
    rw [wordHom_original, hΦ, wordHom_extend]
  rw [hamiltonianLinear_norm_map Φ
    (laurentValue (generatorUnitary (none : Option ι)) l)
    (flow_iso_fix_laurent l U Φ hΦ) (fun j => generatorUnitary (some j)) U hword k]
  exact hamiltonianLinear_original_bound l h0 hS K hK hn k

theorem laurent_bounded_flow
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K) (hn : ‖laurentValue (generatorUnitary (none : Option ι)) l‖ ≤ K) :
    ∃ U : ℝ → ι → unitary (groupVonNeumann (FreeGroup (Option ι))),
      U 0 = (fun j => generatorUnitary (some j)) ∧
      (∀ t, HasDerivAt (fun t j => (U t j : groupVonNeumann (FreeGroup (Option ι))))
        (PolynomialFlow.field (laurentValue (generatorUnitary (none : Option ι)) l) h
          (fun j => (U t j : groupVonNeumann (FreeGroup (Option ι))))) t) ∧
      (∀ t k, ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option ι)) l) (U t) k‖ ≤
        3*K*Real.sqrt (k.sum (fun _ r => r^2))) ∧
      ∃ β : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)),
        (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
          (groupUltraweakTopology (FreeGroup (Option ι))) β ∧
        ∀ g, β (groupUnitary g) = wordHom (extendUnitary (U 1) (generatorUnitary (none : Option ι))) g := by
  classical
  obtain ⟨X,hU,hX₀,hX,hiso⟩ := laurent_flow_automorphisms h l hS
  let U (t : ℝ) : ι → unitary (groupVonNeumann (FreeGroup (Option ι))) := fun j => ⟨X t j, hU t j⟩
  refine ⟨U,?_,hX,?_,hiso 1⟩
  · funext j
    exact Subtype.ext (congrFun hX₀ j)
  · intro t k
    obtain ⟨Φ,_ht,_hc,hΦ⟩ := hiso t
    exact flow_iso_hamiltonian_bound l h0 hS K hK hn (U t) Φ hΦ k

theorem flow_displacements_from_bounds
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l)) (K : ℝ)
    (U : ℝ → ι → unitary (groupVonNeumann (FreeGroup (Option ι))))
    (hU₀ : U 0 = fun j => generatorUnitary (some j))
    (hX : ∀ t, HasDerivAt (fun t j => (U t j : groupVonNeumann (FreeGroup (Option ι))))
      (PolynomialFlow.field (laurentValue (generatorUnitary (none : Option ι)) l) h
        (fun j => (U t j : groupVonNeumann (FreeGroup (Option ι))))) t)
    (hbound : ∀ t k, ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option ι)) l) (U t) k‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2))) :
    (∀ j, ‖(U 1 j : groupVonNeumann (FreeGroup (Option ι))) - groupUnitary (FreeGroup.of (some j))‖ ≤
      3*K*Real.sqrt ((h j).sum (fun _ r => r^2))) ∧
    ∀ w : FreeGroup ι, ‖wordHom (U 1) w - NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option ι)) l) *
      groupUnitary (FreeGroup.map Option.some w)‖ ≤
      3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  constructor
  · intro j
    have hd := generator_displacement (laurentValue (generatorUnitary (none : Option ι)) l) h U hX
      (fun j => 3*K*Real.sqrt ((h j).sum (fun _ r => r^2)))
      (fun t j => hbound t (h j)) j
    rw [hU₀] at hd
    exact hd
  · intro w
    have hd := word_displacement (laurentValue (generatorUnitary (none : Option ι)) l) hS h U hX w
      (3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)))
      (fun t => hbound t (freeCocycle h w - Finsupp.single 1 1))
    rwa [hU₀, wordHom_original] at hd

theorem laurent_flow_displacement
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K) (hn : ‖laurentValue (generatorUnitary (none : Option ι)) l‖ ≤ K) :
    ∃ β : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)),
      (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) β ∧
      β (groupUnitary (FreeGroup.of none)) = groupUnitary (FreeGroup.of none) ∧
      (∀ j : ι, ‖β (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ ≤
        3*K*Real.sqrt ((h j).sum (fun _ r => r^2))) ∧
      ∀ w : FreeGroup ι, ‖β (groupUnitary (FreeGroup.map Option.some w)) -
        NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option ι)) l) *
          groupUnitary (FreeGroup.map Option.some w)‖ ≤
        3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  classical
  obtain ⟨U,hU₀,hX,hbound,β,hβt,hβc,hβ⟩ := laurent_bounded_flow (ι := ι) h l h0 hS K hK hn
  obtain ⟨hgen,hword⟩ := flow_displacements_from_bounds (ι := ι) h l hS K U hU₀ hX hbound
  refine ⟨β,hβt,hβc,?_,?_,?_⟩
  · exact (hβ (FreeGroup.of (none : Option ι))).trans (wordHom_of _ _)
  · intro j
    rw [hβ]
    simpa only [wordHom_of, extendUnitary, Option.elim_some] using hgen j
  · intro w
    rw [hβ]
    simpa only [wordHom_extend] using hword w

end

theorem twoNorm_le_norm {G : Type uG} [Group G] (T : groupVonNeumann G) :
    twoNorm T ≤ ‖T‖ := by
  calc
    _ ≤ ‖(T : GroupOperator G)‖ * ‖(deltaOne : GroupHilbert G)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by simp [deltaOne, lp.norm_single]

theorem twoNorm_sq {G : Type uG} [Group G] (T : groupVonNeumann G) :
    (twoNorm T : ℂ)^2 = canonicalTrace (star T*T) := by
  classical
  rw [canonicalTrace_star_mul, ← deltaOne_eq]
  rfl

end

end FreeGroupFactorMain

end OAI
end


