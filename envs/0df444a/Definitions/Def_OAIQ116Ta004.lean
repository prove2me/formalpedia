-- Prove2me | Definitions.Def_OAIQ116Ta004
-- name    : OAIQ116Ta004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:36:55.220047+00:00
-- url     : https://prove2.me/theorems/416d4ab1-7c8f-4a93-8090-9d6bfb52b239
-- title:
--   Definitions bundle OAIQ116Ta004 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 171 declarations of OpenAI's Lean: 60 definitions, 1 inductive type or structure, 5 instances and 105 theorems. The definitions and types are `OAI.Tachikawa.CompleteHom.equiv`, `OAI.Tachikawa.CompleteHom.zeroEquiv`, `OAI.Tachikawa.CompleteNull.Step`, `OAI.Tachikawa.CompleteNull.component`, `OAI.Tachikawa.CompleteNull.down`, `OAI.Tachikawa.CompleteNull.homotopy`, `OAI.Tachikawa.CompleteNull.up`, `OAI.Tachikawa.Enveloping.freeLeftEquiv`, `OAI.Tachikawa.Enveloping.freeRightEquiv`, `OAI.Tachikawa.Enveloping.leftFunctor`, `OAI.Tachikawa.Enveloping.tensorFunctor`, `OAI.Tachikawa.NatCoker.obj`, `OAI.Tachikawa.NatCoker.stableEquiv`, `OAI.Tachikawa.NatCoker.ι`, `OAI.Tachikawa.OuterTensor.algebraTwist`, `OAI.Tachikawa.OuterTensor.freeAt`, `OAI.Tachikawa.OuterTensor.freeBasis`, `OAI.Tachikawa.OuterTensor.freeEquiv`, `OAI.Tachikawa.OuterTensor.freeTensorBasis`, `OAI.Tachikawa.OuterTensor.restrictionGround`, `OAI.Tachikawa.OuterTensor.twistBicomplexIso`, `OAI.Tachikawa.OuterTensor.twistComplex`, `OAI.Tachikawa.OuterTensor.twistObjIso`, `OAI.Tachikawa.OuterTensor.twistTotalIso`, `OAI.Tachikawa.OuterTensor.underlyingHom`, `OAI.Tachikawa.StableEquiv`, `OAI.Tachikawa.StableEquiv.down`, `OAI.Tachikawa.StableEquiv.ofExactSquares`, `OAI.Tachikawa.StableEquiv.ofLinearEquiv`, `OAI.Tachikawa.StableEquiv.post`, `OAI.Tachikawa.StableEquiv.pre`, `OAI.Tachikawa.StableEquiv.refl`, `OAI.Tachikawa.StableEquiv.symm`, `OAI.Tachikawa.StableEquiv.trans`, `OAI.Tachikawa.StableEquiv.up`, `OAI.Tachikawa.StableMap`, `OAI.Tachikawa.StableShift.kernelMap`, `OAI.Tachikawa.StableShift.liftLinear`, `OAI.Tachikawa.StableShift.map`, `OAI.Tachikawa.SymmetrizingForm.inverseTwistHom` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Bimodule`, `Tachikawa_Coinduction`, `Tachikawa_CompleteResolution`, `Tachikawa_CompleteTensor`, `Tachikawa_Coresolution`, `Tachikawa_Corner`, `Tachikawa_DerivedDescent`, `Tachikawa_FiniteCoinduction`, `Tachikawa_HomProfile`, `Tachikawa_OuterExt`, `Tachikawa_OuterTensor`, `Tachikawa_Perfect`, `Tachikawa_ReverseResolution`, `Tachikawa_StableDuality`, `Tachikawa_StableShift`, `Tachikawa_Symmetry`, `Tachikawa_Tensor`, `Tachikawa_Twisting`.
--
--   **Imports.** It imports the bundles `OAIQ116Ta000`, `OAIQ116Ta001` and `OAIQ116Ta002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta006`, `OAIQ116Ta007`, `OAIQ116Ta008` and `OAIQ116Ta009`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta000
import Definitions.Def_OAIQ116Ta001
import Definitions.Def_OAIQ116Ta002

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Symmetry
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa

namespace TrivialExtension
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

instance instFiniteDimensional [FiniteDimensional k R] : FiniteDimensional k (TrivialExtension k R) :=
  inferInstanceAs (FiniteDimensional k (R × DualBimodule k R))

lemma trace_mul (a b : TrivialExtension k R) :
    trace (a * b) = b.snd a.fst + a.snd b.fst := by
  change (a.fst • b.snd + MulOpposite.op b.fst • a.snd) 1 = _
  simp

lemma trace_comm (a b : TrivialExtension k R) : trace (a * b) = trace (b * a) := by
  rw [trace_mul, trace_mul, add_comm]

lemma trace_nondegenerate (a : TrivialExtension k R)
    (h : ∀ b : TrivialExtension k R, trace (a * b) = 0) : a = 0 := by
  have hfst : a.fst = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff k a.fst).mp
    intro φ
    have := h (TrivSqZeroExt.inr (φ : DualBimodule k R))
    rw [trace_mul] at this
    change φ a.fst + a.snd 0 = 0 at this
    simpa using this
  have hsnd : a.snd = 0 := by
    ext r
    have := h (TrivSqZeroExt.inl r)
    rw [trace_mul] at this
    change (0 : DualBimodule k R) a.fst + a.snd r = 0 at this
    simpa using this
  exact TrivSqZeroExt.ext hfst hsnd

end TrivialExtension



end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableDuality
attribute [-instance] _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instFiniteDiag _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]
  [Module k M] [Module k N] [Module k P]
  [IsScalarTower k R M] [IsScalarTower k R N] [IsScalarTower k R P]

def homPostcompose (p : P →ₗ[R] N) : (M →ₗ[R] P) →ₗ[k] (M →ₗ[R] N) where
  toFun f := p.comp f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [Module k M] [Module k P] [IsScalarTower k R M] [IsScalarTower k R P] in

lemma factors_iff_extends [Module.Injective R R]
    [Module.Finite R P] [Module.Projective R P]
    (i : M →ₗ[R] P) (hi : Function.Injective i) (f : M →ₗ[R] N) :
    f ∈ projectiveFactors (k := k) ↔ ∃ g : P →ₗ[R] N, g.comp i = f := by
  constructor
  · rintro ⟨J, hJf, hJp, a, b, rfl⟩
    let := hJf
    let := hJp
    let : Module.Injective R J := injective_of_finite_projective
    obtain ⟨a', ha'⟩ := Module.Injective.extension_property R J M P i hi a
    refine ⟨b.comp a', ?_⟩
    rw [LinearMap.comp_assoc, ha']
  · rintro ⟨g, rfl⟩
    exact ⟨ModuleCat.of R P, inferInstance, inferInstance, i, g, rfl⟩

omit [Module k M] [Module k P] [IsScalarTower k R M] [IsScalarTower k R P] in

lemma factors_iff_lifts [Module.Finite R P] [Module.Projective R P]
    (p : P →ₗ[R] N) (hp : Function.Surjective p) (f : M →ₗ[R] N) :
    f ∈ projectiveFactors (k := k) ↔ ∃ g : M →ₗ[R] P, p.comp g = f := by
  constructor
  · rintro ⟨J, hJf, hJp, a, b, rfl⟩
    let := hJp
    obtain ⟨b', hb'⟩ := Module.projective_lifting_property p b hp
    exact ⟨b'.comp a, by rw [← LinearMap.comp_assoc, hb']⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ModuleCat.of R P, inferInstance, inferInstance, g, p, rfl⟩

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {N : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R)) [FiniteDimensional k R]
variable (ι : Type) [Fintype ι] [DecidableEq ι]

lemma freeHomDual_natural {N' : Type} [AddCommGroup N'] [Module R N'] [Module k N']
    [IsScalarTower k R N'] (g : N' →ₗ[R] (ι → R))
    (a : N →ₗ[R] N') (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι (g.comp a) f = t.freeHomDual ι g (a.comp f) := by
  simp only [freeHomDual_apply, LinearMap.comp_apply]

lemma freeHomDual_cyclic_rect (κ : Type) [Fintype κ] [DecidableEq κ]
    (g : N →ₗ[R] (κ → R)) (f : (ι → R) →ₗ[R] N)
    (a : (κ → R) →ₗ[R] (ι → R)) :
    t.freeHomDual κ g (f.comp a) = t.freeHomDual ι (a.comp g) f := by
  have expand (x : ι → R) : f x = ∑ i, x i • f (Pi.single i 1) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using
      (congrArg (fun z : (ι → R) →ₗ[R] N => z x)
        ((LinearEquiv.piRing R N ι k).symm_apply_apply f)).symm
  have expand' (x : κ → R) : a x = ∑ j, x j • a (Pi.single j 1) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using
      (congrArg (fun z : (κ → R) →ₗ[R] (ι → R) => z x)
        ((LinearEquiv.piRing R (ι → R) κ k).symm_apply_apply a)).symm
  simp only [freeHomDual_apply, LinearMap.comp_apply]
  conv_lhs => arg 2; ext j; rw [expand (a (Pi.single j 1))]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_rhs => arg 2; ext j; rw [expand' (g (f (Pi.single j 1)))]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact t.comm _ _

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module k N]
  [IsScalarTower k R N]
namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))
variable {n : ℕ} (ε : (Fin n → R) →ₗ[R] M)

def syzygyPair : (N →ₗ[R] LinearMap.ker ε) →ₗ[k] Module.Dual k (M →ₗ[R] N) :=
  (homPrecompose (k := k) ε).dualMap.comp
    ((t.freeHomDual (Fin n)).toLinearMap.comp (homPostcompose (LinearMap.ker ε).subtype))

lemma syzygyPair_apply (g : N →ₗ[R] LinearMap.ker ε) (f : M →ₗ[R] N) :
    t.syzygyPair ε g f = t.freeHomDual (Fin n) ((LinearMap.ker ε).subtype.comp g)
      (f.comp ε) := rfl

lemma syzygyPair_vanish_right {p : ℕ}
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    (g : N →ₗ[R] LinearMap.ker ε) (hg : g ∈ projectiveFactors (k := k)) :
    t.syzygyPair ε g = 0 := by
  obtain ⟨a, rfl⟩ := (factors_iff_lifts d hd g).mp hg
  ext f
  rw [syzygyPair_apply, ← LinearMap.comp_assoc, ← t.freeHomDual_cyclic_rect]
  have hzero : (f.comp ε).comp ((LinearMap.ker ε).subtype.comp d) = 0 := by
    apply LinearMap.ext
    intro x
    change f (ε (d x).val) = 0
    rw [(d x).property, map_zero]
  rw [hzero, map_zero]
  rfl

omit [FiniteDimensional k R] in

lemma precompose_range_eq_ker (hε : Function.Surjective ε) {p : ℕ}
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d) :
    LinearMap.range (homPrecompose (k := k) (N := N) ε) =
      LinearMap.ker (homPrecompose (k := k) (N := N) ((LinearMap.ker ε).subtype.comp d)) := by
  ext a
  constructor
  · rintro ⟨f, rfl⟩
    apply LinearMap.ext
    intro x
    change f (ε (d x).val) = 0
    rw [(d x).property, map_zero]
  · intro ha
    have hk : LinearMap.ker ε ≤ LinearMap.ker a := by
      intro x hx
      obtain ⟨y, hy⟩ := hd ⟨x, hx⟩
      have hy' : (d y).val = x := congrArg Subtype.val hy
      have hay := LinearMap.congr_fun ha y
      change a (d y).val = 0 at hay
      simpa only [LinearMap.mem_ker, ← hy'] using hay
    refine ⟨((LinearMap.ker ε).liftQ a hk).comp
      (ε.quotKerEquivOfSurjective hε).symm.toLinearMap, ?_⟩
    apply LinearMap.ext
    intro x
    change (LinearMap.ker ε).liftQ a hk ((ε.quotKerEquivOfSurjective hε).symm (ε x)) = a x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl

lemma syzygyPair_eq_zero_iff (hε : Function.Surjective ε) {p : ℕ}
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    (g : N →ₗ[R] LinearMap.ker ε) :
    t.syzygyPair ε g = 0 ↔ g ∈ projectiveFactors (k := k) := by
  constructor
  · intro hg
    let δ := (LinearMap.ker ε).subtype.comp d
    let l := t.freeHomDual (Fin n) ((LinearMap.ker ε).subtype.comp g)
    have hl : l ∈ (LinearMap.ker (homPrecompose (k := k) (N := N) δ)).dualAnnihilator := by
      rw [← precompose_range_eq_ker ε hε d hd]
      rw [Submodule.mem_dualAnnihilator]
      rintro a ⟨f, rfl⟩
      exact LinearMap.congr_fun hg f
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hl
    obtain ⟨l', hl'⟩ := hl
    obtain ⟨a, rfl⟩ := (t.freeHomDual (Fin p) (N := N)).surjective l'
    have hga : (LinearMap.ker ε).subtype.comp g = δ.comp a := by
      apply (t.freeHomDual (Fin n)).injective
      ext f
      have hf := LinearMap.congr_fun hl' f
      change t.freeHomDual (Fin p) a (f.comp δ) = l f at hf
      rw [t.freeHomDual_cyclic_rect] at hf
      exact hf.symm
    apply (factors_iff_lifts d hd g).mpr
    refine ⟨a, ?_⟩
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (LinearMap.congr_fun hga x).symm
  · exact t.syzygyPair_vanish_right ε d hd g

end SymmetrizingForm
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteResolution
attribute [-instance] _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ)

namespace TotallyAcyclic
variable {P}

lemma factors_iff_boundary (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j))
    {N : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
    (j : ℤ) (f : P.X j →ₗ[R] N) (hf : f.comp (P.d (j+1) j).hom = 0) :
    CokerAt.descend P j f hf ∈ projectiveFactors (k := k) ↔
      ∃ g : P.X (j-1) →ₗ[R] N, g.comp (P.d j (j-1)).hom = f := by
  constructor
  · rintro ⟨J, hJf, hJp, a, b, hab⟩
    let := hJf
    let := hJp
    obtain ⟨a', ha'⟩ := hP.extend_coker j a
    refine ⟨b.comp a', ?_⟩
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun ha' (CokerAt.π P j x)
    change a' (P.d j (j-1) x) = a (CokerAt.π P j x) at hx
    change b (a' (P.d j (j-1) x)) = f x
    rw [hx]
    exact LinearMap.congr_fun hab (CokerAt.π P j x)
  · rintro ⟨g, hg⟩
    refine ⟨P.X (j-1), fin _, proj _, CokerAt.ι P j, g, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := CokerAt.π_surjective P j x
    exact LinearMap.congr_fun hg y

end TotallyAcyclic
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Tensor
attribute [-instance] _root_.OAI.Tachikawa.BalancedTensor.rightModule _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instFiniteDiag _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped TensorProduct
namespace Tachikawa.BalancedTensor
variable {k R S M N N' N'' : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

lemma mapRight_surjective (f : N →ₗ[R] N') (hf : Function.Surjective f) :
    Function.Surjective (mapRight (k := k) (S := S) (M := M) f) := by
  intro x
  induction x using induction_on with
  | h0 => exact ⟨0, map_zero _⟩
  | ht m n =>
    obtain ⟨n', rfl⟩ := hf n
    exact ⟨mk m n', rfl⟩
  | ha x y hx hy =>
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact ⟨a+b, map_add _ _ _⟩

end Tachikawa.BalancedTensor



end


noncomputable section
namespace Tachikawa.BalancedTensor
variable {k R S M M' N N' N'' : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M']
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

omit [IsScalarTower k Rᵐᵒᵖ M] in
lemma restrictEquiv_mapRight [SMulCommClass S Rᵐᵒᵖ M] (g : N →ₗ[R] N')
    (x : T (k := k) (R := R) (S := S) (M := M) (N := N)) :
    restrictEquiv (mapRight (k := k) (S := S) g x) =
      mapRight (k := k) (S := k) g (restrictEquiv x) := by
  induction x using induction_on with
  | h0 => simp
  | ht m n => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

end Tachikawa.BalancedTensor



namespace Tachikawa
open scoped TensorProduct
namespace SymmetrizingForm
variable {k R S : Type*} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))

lemma tensorTrace_comm (a b : R ⊗[k] S) :
    tensorTrace t u (a*b) = tensorTrace t u (b*a) := by
  induction a using OAI.tensorInductionOn with
  | tmul r s =>
    induction b using OAI.tensorInductionOn with
    | tmul r' s' => simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorTrace_tmul,
        t.comm r r', u.comm s s']
    | add b c hb hc => simp only [mul_add, add_mul, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, mul_add, map_add, ha, hc]

variable [FiniteDimensional k R] [FiniteDimensional k S]

def tensorDualEquiv : R ⊗[k] S ≃ₗ[k] Module.Dual k (R ⊗[k] S) :=
  (TensorProduct.congr (t.dualEquiv.restrictScalars k) (u.dualEquiv.restrictScalars k)).trans
    (TensorProduct.dualDistribEquiv k R S)

lemma tensorDualEquiv_apply (a b : R ⊗[k] S) :
    tensorDualEquiv t u a b = tensorTrace t u (b*a) := by
  induction a using OAI.tensorInductionOn with
  | tmul r s =>
    induction b using OAI.tensorInductionOn with
    | tmul r' s' =>
      dsimp only [tensorDualEquiv, DualBimodule]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorTrace_tmul]
      rfl
    | add b c hb hc => simp only [map_add, add_mul, hb, hc]
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, mul_add, ha, hc]

def tensor : SymmetrizingForm (k := k) (R := R ⊗[k] S) where
  linear := tensorTrace t u
  comm := tensorTrace_comm t u
  nondegenerate a h := by
    apply (tensorDualEquiv t u).injective
    apply LinearMap.ext
    intro b
    rw [tensorDualEquiv_apply, tensorTrace_comm, h]
    simp

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def op (t : SymmetrizingForm (k := k) (R := R)) :
    SymmetrizingForm (k := k) (R := Rᵐᵒᵖ) where
  linear := t.linear.comp (MulOpposite.opLinearEquiv k).symm.toLinearMap
  comm a b := t.comm b.unop a.unop
  nondegenerate a ha := by
    apply MulOpposite.unop_injective
    apply t.nondegenerate a.unop
    intro b
    have h := ha (MulOpposite.op b)
    change t.linear (b * a.unop) = 0 at h
    exact (t.comm _ _).trans h

end SymmetrizingForm
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

instance objFinite (M : ModuleCat (Alg k R S)) [FiniteDimensional k M] :
    FiniteDimensional k (Obj M) := inferInstanceAs (FiniteDimensional k M)

def leftFunctor : ModuleCat (Alg k R S) ⥤ ModuleCat R where
  obj M := ModuleCat.of R (Obj M)
  map f := ModuleCat.ofHom (leftMap f)

instance instAdditiveModuleCatAlgLeftFunctor : (leftFunctor (k := k) (R := R) (S := S)).Additive where
  map_add := rfl

def freeLeftEquiv (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (Fin n → Alg k R S)) ≃ₗ[R] (Fin n → (R ⊗[k] Sᵐᵒᵖ)) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    ext i
    change (r ⊗ₜ[k] (1:Sᵐᵒᵖ)) * x i = r • x i
    induction x i using OAI.tensorInductionOn with
    | tmul a b => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [mul_add, smul_add, hx, hy]

def freeRightEquiv (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (Fin n → Alg k R S)) ≃ₗ[Sᵐᵒᵖ]
      (Fin n → (Sᵐᵒᵖ ⊗[k] R)) where
  toFun x i := TensorProduct.comm k R Sᵐᵒᵖ (x i)
  invFun x i := TensorProduct.comm k Sᵐᵒᵖ R (x i)
  left_inv x := by
    apply funext
    intro i
    exact (TensorProduct.comm k R Sᵐᵒᵖ).left_inv (x i)
  right_inv x := by ext i; exact (TensorProduct.comm k R Sᵐᵒᵖ).right_inv (x i)
  map_add' _ _ := by ext i; exact map_add _ _ _
  map_smul' s x := by
    ext i
    change TensorProduct.comm k R Sᵐᵒᵖ (((1:R) ⊗ₜ[k] s) * x i) =
      s • TensorProduct.comm k R Sᵐᵒᵖ (x i)
    induction x i using OAI.tensorInductionOn with
    | tmul a b => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [mul_add, map_add, smul_add, hx, hy]

lemma freeLeftProjective (n : ℕ) :
    Module.Projective R (Obj (ModuleCat.of (Alg k R S) (Fin n → Alg k R S))) :=
  Module.Projective.of_equiv' (freeLeftEquiv (k := k) (R := R) (S := S) n).symm

lemma freeRightProjective (n : ℕ) :
    Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (Fin n → Alg k R S))) :=
  Module.Projective.of_equiv' (freeRightEquiv (k := k) (R := R) (S := S) n).symm

lemma projective_left (M : ModuleCat (Alg k R S))
    [Module.Finite (Alg k R S) M] [Module.Projective (Alg k R S) M] :
    Module.Projective R (Obj M) := by
  let c := finiteFreeCover (R := Alg k R S) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let := freeLeftProjective (k := k) (R := R) (S := S) c.rank
  apply Module.Projective.of_split
    (leftMap (ModuleCat.ofHom i)) (leftMap (ModuleCat.ofHom c.map))
  ext x
  exact LinearMap.congr_fun hi x

lemma projective_right (M : ModuleCat (Alg k R S))
    [Module.Finite (Alg k R S) M] [Module.Projective (Alg k R S) M] :
    Module.Projective Sᵐᵒᵖ (Obj M) := by
  let c := finiteFreeCover (R := Alg k R S) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let := freeRightProjective (k := k) (R := R) (S := S) c.rank
  apply Module.Projective.of_split
    (rightMap (ModuleCat.ofHom i)) (rightMap (ModuleCat.ofHom c.map))
  ext x
  exact LinearMap.congr_fun hi x

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (M : ModuleCat.{0} (Alg k S R))

abbrev tensorFunctor : ModuleCat.{0} R ⥤ ModuleCat.{0} S :=
  BalancedTensor.functor (k := k) (R := R) (S := S) (M := Obj M)

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

namespace CompleteNull

@[simp] lemma stateMap_self {i : ℤ} (a : State f i) : stateMap f a (i+1) rfl = a.val := rfl

def Step (i j : ℤ) (h : i+1=j) (a : State f i) (b : State f j) : Prop :=
  (f.f j).hom = (stateMap f a j h).comp (P.d j i).hom + (Q.d (j+1) j).hom.comp b.val

variable (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))

def up (j : ℤ) (a : State f j) : State f (j+1) :=
  let h := goodComponent_up f hq pproj j (j+1) (j+1+1) rfl rfl a.val a.property
  ⟨h.choose, h.choose_spec.2⟩

lemma up_step (j : ℤ) (a : State f j) : Step f j (j+1) rfl a (up f hq pproj j a) :=
  (goodComponent_up f hq pproj j (j+1) (j+1+1) rfl rfl a.val a.property).choose_spec.1

def down (i j : ℤ) (h : i+1=j) (b : State f j) : State f i := by
  subst j
  let h := goodComponent_down f hp qfin qproj i (i+1) (i+1+1) rfl rfl b.val b.property
  exact ⟨h.choose, h.choose_spec.2⟩

lemma down_step (i j : ℤ) (h : i+1=j) (b : State f j) :
    Step f i j h (down f hp qfin qproj i j h b) b := by
  subst j
  exact (goodComponent_down f hp qfin qproj i (i+1) (i+1+1) rfl rfl b.val b.property).choose_spec.1

variable (b₀ : State f 0)

def component (j : ℤ) : State f j :=
  j.inductionOn' 0 b₀ (fun j _ => up f hq pproj j)
    (fun j _ => down f hp qfin qproj (j-1) j (by omega))

lemma component_up (j : ℤ) (hj : 0 ≤ j) :
    component f hp hq pproj qfin qproj b₀ (j+1) =
      up f hq pproj j (component f hp hq pproj qfin qproj b₀ j) :=
  Int.inductionOn'_add_one hj

lemma component_down (j : ℤ) (hj : j ≤ 0) :
    component f hp hq pproj qfin qproj b₀ (j-1) =
      down f hp qfin qproj (j-1) j (by omega) (component f hp hq pproj qfin qproj b₀ j) :=
  Int.inductionOn'_sub_one hj

lemma hasStep_down (i j : ℤ) (h : i+1=j) (hj : j ≤ 0) :
    Step f i j h (component f hp hq pproj qfin qproj b₀ i)
      (component f hp hq pproj qfin qproj b₀ j) := by
  have hi : i=j-1 := by omega
  subst i
  rw [component_down f hp hq pproj qfin qproj b₀ j hj]
  exact down_step f hp qfin qproj (j-1) j h _

lemma hasStep (i j : ℤ) (h : i+1=j) :
    Step f i j h (component f hp hq pproj qfin qproj b₀ i)
      (component f hp hq pproj qfin qproj b₀ j) := by
  by_cases hi : 0 ≤ i
  · subst j
    rw [component_up f hp hq pproj qfin qproj b₀ i hi]
    exact up_step f hq pproj i _
  · exact hasStep_down f hp hq pproj qfin qproj b₀ i j h (by omega)

def homotopy : Homotopy f 0 where
  hom i j := if h : i+1=j then
    ModuleCat.ofHom (stateMap f (component f hp hq pproj qfin qproj b₀ i) j h) else 0
  zero i j h := by
    exact dite_eq_right h
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i-1) by change i-1+1=i; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (i+1) i from rfl)]
    simp only [dite_eq_left (show i-1+1=i by omega), zero_f, add_zero]
    apply ModuleCat.hom_ext
    exact hasStep f hp hq pproj qfin qproj b₀ (i-1) i (by omega)

end CompleteNull

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableShift
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ) (N : ModuleCat R)

namespace CompleteHom

variable (hP : TotallyAcyclic P) (fin : ∀ j, Module.Finite R (P.X j))
  (proj : ∀ j, Module.Projective R (P.X j))

include hP fin proj in
lemma boundary_iff (j : ℤ) (z : VectorSplit.Z (completeHom (k := k) P N) j) :
    z ∈ LinearMap.range (VectorSplit.boundary (completeHom (k := k) P N) j) ↔
      (cokerCycles P N j).symm z ∈ projectiveFactors (k := k) := by
  change _ ↔ CokerAt.descend P j z.val.hom (ModuleCat.hom_ext_iff.mp
    ((completeHom_memZ P N j z.val).mp z.property)) ∈ projectiveFactors (k := k)
  refine Iff.trans ?_ (hP.factors_iff_boundary (k := k) fin proj j z.val.hom
    (ModuleCat.hom_ext_iff.mp ((completeHom_memZ P N j z.val).mp z.property))).symm
  change (∃ g : P.X ((ComplexShape.up ℤ).prev j) ⟶ N,
    VectorSplit.boundary (completeHom (k := k) P N) j g = z) ↔ _
  simp only [← Subtype.val_inj]
  change (∃ g : P.X ((ComplexShape.up ℤ).prev j) ⟶ N,
    P.d j ((ComplexShape.up ℤ).prev j) ≫ g = z.val) ↔ _
  rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (j-1) j by change (j-1)+1=j; omega)]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩
  · rintro ⟨g,hg⟩
    exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩

def equiv (j : ℤ) : VectorSplit.H (completeHom (k := k) P N) j ≃ₗ[k]
    StableHom (k := k) (R := R) (M := CokerAt P j) (N := N) := by
  apply Submodule.Quotient.equiv _ _ (cokerCycles P N j).symm
  ext f
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (boundary_iff P N hP fin proj j z).mp hz
  · intro hf
    refine ⟨(cokerCycles P N j) f,?_,by simp⟩
    apply (boundary_iff P N hP fin proj j _).mpr
    simpa using hf

end CompleteHom
end Tachikawa



namespace Tachikawa
variable {k R M N P Q : Type} [Field k] [Ring R] [Algebra k R]
 [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
 [Module R M] [Module R N] [Module R P] [Module R Q]
 [Module k N] [Module k Q]
 [IsScalarTower k R N] [IsScalarTower k R Q]

namespace StableShift
variable (ε : P →ₗ[R] M) (δ : Q →ₗ[R] N) (hδ : Function.Surjective δ)
 [Module.Projective R P]

include hδ in
lemma hom_lift_surjective : Function.Surjective (homPostcompose (k := k) (M := P) δ) := by
  intro f
  exact Module.projective_lifting_property δ f hδ

def liftLinear : (M →ₗ[R] N) →ₗ[k] (P →ₗ[R] Q) :=
  (Classical.choose ((homPostcompose (k := k) (M := P) δ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (hom_lift_surjective (k := k) δ hδ)))).comp (homPrecompose ε)

lemma liftLinear_lifts (f : M →ₗ[R] N) : δ.comp (liftLinear (k := k) ε δ hδ f) = f.comp ε := by
  exact LinearMap.congr_fun (Classical.choose_spec
    ((homPostcompose (k := k) (M := P) δ).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (hom_lift_surjective (k := k) δ hδ)))) (f.comp ε)

def kernelMap : (M →ₗ[R] N) →ₗ[k] (LinearMap.ker ε →ₗ[R] LinearMap.ker δ) where
  toFun f := LinearMap.codRestrict (LinearMap.ker δ) ((liftLinear (k := k) ε δ hδ f).domRestrict (LinearMap.ker ε)) (by
    intro x
    change δ (liftLinear (k := k) ε δ hδ f x) = 0
    have hh := LinearMap.congr_fun (liftLinear_lifts (k := k) ε δ hδ f) x
    change δ (liftLinear (k := k) ε δ hδ f x) = f (ε x) at hh
    rw [show ε x = 0 from x.property, map_zero] at hh
    exact hh)
  map_add' f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (liftLinear (k := k) ε δ hδ) f g) x
  map_smul' c f := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (liftLinear (k := k) ε δ hδ) c f) x

variable [Module.Finite R P]

lemma kernelMap_class (f : M →ₗ[R] N) (g : LinearMap.ker ε →ₗ[R] LinearMap.ker δ)
    (h : P →ₗ[R] Q) (hh : δ.comp h = f.comp ε)
    (hg : h.comp (LinearMap.ker ε).subtype = (LinearMap.ker δ).subtype.comp g) :
    stableClass (k := k) (kernelMap (k := k) ε δ hδ f) = stableClass (k := k) g := by
  rw [← sub_eq_zero, ← map_sub, stableClass_eq_zero_iff]
  let t : P →ₗ[R] LinearMap.ker δ := LinearMap.codRestrict (LinearMap.ker δ)
    (liftLinear (k := k) ε δ hδ f - h) (by
      intro x
      change δ (liftLinear (k := k) ε δ hδ f x - h x) = 0
      rw [map_sub]
      have h₁ := LinearMap.congr_fun (liftLinear_lifts (k := k) ε δ hδ f) x
      have h₂ := LinearMap.congr_fun hh x
      dsimp only [LinearMap.comp_apply] at h₁ h₂
      rw [h₁,h₂,sub_self])
  refine ⟨ModuleCat.of R P, inferInstance, inferInstance, (LinearMap.ker ε).subtype, t, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx := LinearMap.congr_fun hg x
  change h x = (g x : Q) at hx
  change liftLinear (k := k) ε δ hδ f x - h x = liftLinear (k := k) ε δ hδ f x - (g x : Q)
  rw [hx]

variable [Module.Finite R Q] [Module.Projective R Q]

lemma kernelMap_factors (f : M →ₗ[R] N) (hf : f ∈ projectiveFactors (k := k)) :
    kernelMap (k := k) ε δ hδ f ∈ projectiveFactors (k := k) := by
  obtain ⟨s,hs⟩ := (factors_iff_lifts δ hδ f).mp hf
  have hc := kernelMap_class (k := k) ε δ hδ f 0 (s.comp ε)
    (by rw [← LinearMap.comp_assoc,hs]) (by
      apply LinearMap.ext
      intro x
      change s (ε x) = 0
      rw [x.property,map_zero])
  apply (stableClass_eq_zero_iff _).mp
  simpa only [map_zero] using hc

def map : StableHom (k := k) (R := R) (M := M) (N := N) →ₗ[k]
    StableHom (k := k) (R := R) (M := LinearMap.ker ε) (N := LinearMap.ker δ) :=
  (projectiveFactors (k := k)).mapQ (projectiveFactors (k := k))
    (kernelMap (k := k) ε δ hδ) (kernelMap_factors (k := k) ε δ hδ)

@[simp] lemma map_class (f : M →ₗ[R] N) :
    map (k := k) ε δ hδ (stableClass (k := k) f) =
      stableClass (k := k) (kernelMap (k := k) ε δ hδ f) := rfl

end StableShift
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]
variable {M N P Q M' N' : ModuleCat.{0} R}
variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]

theorem exact_square_factors_iff
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (f : M →ₗ[R] N) (h : P →ₗ[R] Q) (g : M' →ₗ[R] N')
    (hu : h.comp i = j.comp f) (hl : delta.comp h = g.comp pi) :
    f ∈ projectiveFactors (k := k) ↔ g ∈ projectiveFactors (k := k) := by
  have hji : delta.comp j = 0 := by
    ext x
    exact (hex' (j x)).mpr ⟨x,rfl⟩
  have hpii : pi.comp i = 0 := by
    ext x
    exact (hex (i x)).mpr ⟨x,rfl⟩
  constructor
  · intro hf
    obtain ⟨d,hd⟩ := (factors_iff_extends (k := k) i hi f).mp hf
    have hz : LinearMap.ker pi ≤ LinearMap.ker (h - j.comp d) := by
      intro x hx
      obtain ⟨y,rfl⟩ := (hex x).mp hx
      change h (i y) - j (d (i y)) = 0
      have h1 := LinearMap.congr_fun hu y
      have h2 := LinearMap.congr_fun hd y
      change h (i y) = j (f y) at h1
      change d (i y) = f y at h2
      rw [h1,h2,sub_self]
    obtain ⟨s,hs⟩ := linear_descent pi hpi (h - j.comp d) hz
    apply (factors_iff_lifts (k := k) delta hdelta g).mpr
    refine ⟨s,?_⟩
    ext x
    obtain ⟨y,rfl⟩ := hpi x
    have h1 := LinearMap.congr_fun hs y
    have h2 := LinearMap.congr_fun hl y
    change s (pi y) = h y - j (d y) at h1
    change delta (h y) = g (pi y) at h2
    change delta (s (pi y)) = g (pi y)
    rw [h1,map_sub,show delta (j (d y)) = 0 from LinearMap.congr_fun hji (d y),sub_zero,h2]
  · intro hg
    obtain ⟨s,hs⟩ := (factors_iff_lifts (k := k) delta hdelta g).mp hg
    have hr (x : P) : (h - s.comp pi) x ∈ LinearMap.range j := by
      apply (hex' _).mp
      change delta (h x - s (pi x)) = 0
      rw [map_sub]
      have h1 := LinearMap.congr_fun hl x
      have h2 := LinearMap.congr_fun hs (pi x)
      change delta (h x) = g (pi x) at h1
      change delta (s (pi x)) = g (pi x) at h2
      rw [h1,h2,sub_self]
    let d := CokerAt.factorThrough j hj (h - s.comp pi) hr
    have hd := CokerAt.factorThrough_spec j hj (h - s.comp pi) hr
    apply (factors_iff_extends (k := k) i hi f).mpr
    refine ⟨d,?_⟩
    ext x
    apply hj
    have h1 := LinearMap.congr_fun hd (i x)
    have h2 := LinearMap.congr_fun hu x
    change j (d (i x)) = h (i x) - s (pi (i x)) at h1
    change h (i x) = j (f x) at h2
    change j (d (i x)) = j (f x)
    rw [h1,show pi (i x) = 0 from LinearMap.congr_fun hpii x,map_zero,sub_zero,h2]

omit [Module.Finite R P] [Module.Projective R P] in

theorem exists_exact_square_down
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N')
    (hex' : Function.Exact j delta) (f : M →ₗ[R] N) :
    ∃ (h : P →ₗ[R] Q) (g : M' →ₗ[R] N'),
      h.comp i = j.comp f ∧ delta.comp h = g.comp pi := by
  let : Module.Injective R Q := injective_of_finite_projective
  obtain ⟨h,hh⟩ := Module.Injective.extension_property R Q M P i hi (j.comp f)
  have hz : LinearMap.ker pi ≤ LinearMap.ker (delta.comp h) := by
    intro x hx
    obtain ⟨y,rfl⟩ := (hex x).mp hx
    have he := LinearMap.congr_fun hh y
    change h (i y) = j (f y) at he
    change delta (h (i y)) = 0
    rw [he]
    exact (hex' _).mpr ⟨f y,rfl⟩
  obtain ⟨g,hg⟩ := linear_descent pi hpi (delta.comp h) hz
  exact ⟨h,g,hh,hg.symm⟩
end Tachikawa



namespace Tachikawa.VectorSplit
open CategoryTheory
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
  {K L M : HomologicalComplex (ModuleCat k) c}

@[simp] lemma Hmap_quotient (f : K ⟶ L) (i : I) (z : Z K i) :
    Hmap f i (quotient K i z) = quotient L i (cycleMap f i z) := rfl

lemma quotient_surjective (i : I) : Function.Surjective (quotient K i) :=
  Submodule.mkQ_surjective _

@[simp] lemma Hmap_comp (f : K ⟶ L) (g : L ⟶ M) (i : I) :
    Hmap (f ≫ g) i = (Hmap g i).comp (Hmap f i) := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  rfl

@[simp] lemma Hmap_id (i : I) : Hmap (𝟙 K) i = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  rfl

@[simp] lemma Hmap_zero (i : I) : Hmap (0 : K ⟶ L) i = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  exact map_zero (quotient L i)

@[simp] lemma Hmap_add (f g : K ⟶ L) (i : I) : Hmap (f+g) i = Hmap f i + Hmap g i := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  change quotient L i (cycleMap (f+g) i z) =
    quotient L i (cycleMap f i z) + quotient L i (cycleMap g i z)
  rw [← map_add]
  congr 1

@[simp] lemma Hmap_smul (r : k) (f : K ⟶ L) (i : I) : Hmap (r • f) i = r • Hmap f i := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  change quotient L i (cycleMap (r • f) i z) = r • quotient L i (cycleMap f i z)
  rw [← map_smul]
  congr 1

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) {M N L : ModuleCat.{0} R}

@[simp] lemma completeHomMap_apply (f : M ⟶ N) (a : ℤ) (g : P.X a ⟶ M) :
    (completeHomMap (k := k) P f).f a g = g ≫ f := rfl

@[simp] lemma completeHomMap_comp (f : M ⟶ N) (g : N ⟶ L) :
    completeHomMap (k := k) P (f ≫ g) = completeHomMap P f ≫ completeHomMap P g := by
  ext a x
  rfl

@[simp] lemma completeHomMap_id : completeHomMap (k := k) P (𝟙 M) = 𝟙 _ := by
  ext a x
  rfl

@[simp] lemma completeHomMap_zero : completeHomMap (k := k) P (0 : M ⟶ N) = 0 := by
  ext a x
  rfl

@[simp] lemma completeHomMap_add (f g : M ⟶ N) :
    completeHomMap (k := k) P (f+g) = completeHomMap P f + completeHomMap P g := by
  ext a x
  rfl

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ)

abbrev completeHmap {M N : ModuleCat.{0} R} (f : M ⟶ N) (a : ℤ) :=
  VectorSplit.Hmap (completeHomMap (k := k) P f) a

@[simp] lemma completeHmap_comp {M N L : ModuleCat.{0} R} (f : M ⟶ N) (g : N ⟶ L) (a : ℤ) :
    completeHmap (k := k) P (f ≫ g) a = (completeHmap P g a).comp (completeHmap P f a) := by
  simp only [completeHmap,completeHomMap_comp,VectorSplit.Hmap_comp]
@[simp] lemma completeHmap_id (M : ModuleCat.{0} R) (a : ℤ) :
    completeHmap (k := k) P (𝟙 M) a = LinearMap.id := by
  simp only [completeHmap,completeHomMap_id,VectorSplit.Hmap_id]
@[simp] lemma completeHmap_add {M N : ModuleCat.{0} R} (f g : M ⟶ N) (a : ℤ) :
    completeHmap (k := k) P (f+g) a = completeHmap P f a + completeHmap P g a := by
  simp only [completeHmap,completeHomMap_add,VectorSplit.Hmap_add]
@[simp] lemma completeHmap_zero {M N : ModuleCat.{0} R} (a : ℤ) :
    completeHmap (k := k) P (0 : M ⟶ N) a = 0 := by
  simp only [completeHmap,completeHomMap_zero,VectorSplit.Hmap_zero]

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Twisting
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))
  (σ : R ≃ₐ[k] R)

abbrev twistFunctor := AlgebraInduction.res σ.symm.toAlgHom

end SymmetrizingForm
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def inverseTwistHom {X Y : ModuleCat R} (f : X ⟶ (twistFunctor σ).obj Y) :
    (twistFunctor σ.symm).obj X ⟶ Y := ModuleCat.ofHom
  (X := (twistFunctor σ.symm).obj X) (Y := Y)
  { toFun := f
    map_add' := f.hom.map_add
    map_smul' a x := by
      change f (σ a • (show X from x)) = a • (show Y from f x)
      have h := f.hom.map_smul (σ a) (show X from x)
      change f (σ a • (show X from x)) = σ.symm (σ a) • (show Y from f x) at h
      simpa only [AlgEquiv.symm_apply_apply] using h }

end Tachikawa.SymmetrizingForm



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
variable (K : HomologicalComplex (ModuleCat k) c)

lemma d_hom (i : I) :
    K.d i (c.next i) ≫ hom K (c.next i) i = ModuleCat.ofHom (complement K i) := by
  by_cases h : c.Rel i (c.next i)
  · exact d_hom_of_rel K i (c.next i) h
  · rw [K.shape _ _ h, CategoryTheory.Limits.zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : x ∈ Z K i := by
      change K.d i (c.next i) x = 0
      rw [K.shape _ _ h]
      rfl
    exact (complement_cycle K i ⟨x,hx⟩).symm

lemma hom_d (i : I) (x : K.X i) :
    (hom K i (c.prev i) ≫ K.d (c.prev i) i) x =
      inc K i (retract K i x) - inc K i (representatives K i (quotient K i (retract K i x))) := by
  by_cases h : c.Rel (c.prev i) i
  · rw [hom_eq K i (c.prev i) h]
    exact homotopy_d K i x
  · rw [hom_eq_zero K _ _ h, CategoryTheory.Limits.zero_comp]
    have hh := homotopy_d K i x
    rw [K.shape _ _ h] at hh
    exact hh

end Tachikawa.VectorSplit



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterTensor
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instFiniteDiag _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
set_option backward.isDefEq.respectTransparency true



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma freeEquivLinear_action (m n : ℕ) (r : A ⊗[k] B) :
    (freeEquivLinear k A B m n).toLinearMap.comp
      (action k A B (freeObj A m) (freeObj B n) r) =
      (Algebra.lsmul k k (Fin m → Fin n → A ⊗[k] B) r).comp
      (freeEquivLinear k A B m n).toLinearMap := by
  induction r using OAI.tensorInductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    ext i j
    change (a * x i) ⊗ₜ[k] (b * y j) = (a ⊗ₜ[k] b) * (x i ⊗ₜ[k] y j)
    exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm
  | add r s hr hs =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hr, hs]

def freeEquiv (m n : ℕ) :
    Obj k A B (freeObj A m) (freeObj B n) ≃ₗ[A ⊗[k] B]
      (Fin m → Fin n → A ⊗[k] B) where
  __ := (freeEquivLinear k A B m n).toAddEquiv
  map_smul' r z := LinearMap.congr_fun (freeEquivLinear_action k A B m n r) z

instance freeProjective (m n : ℕ) :
    Module.Projective (A ⊗[k] B)
      (Obj k A B (freeObj A m) (freeObj B n)) :=
  Module.Projective.of_equiv' (freeEquiv k A B m n).symm

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M U : ModuleCat A} {N V : ModuleCat B}

def underlyingHom (f : ((bifunctor k A B).obj M |>.obj N) ⟶
    ((bifunctor k A B).obj U |>.obj V)) : M ⊗[k] N →ₗ[k] U ⊗[k] V where
  toFun := f.hom
  map_add' := f.hom.map_add
  map_smul' r z := by
    have h := f.hom.map_smul (algebraMap k (A ⊗[k] B) r) z
    change f.hom (action k A B M N (algebraMap k (A ⊗[k] B) r) z) =
      action k A B U V (algebraMap k (A ⊗[k] B) r) (f.hom z) at h
    rw [AlgHom.commutes, AlgHom.commutes] at h
    exact h

lemma homMap_underlying (z : (M ⟶ U) ⊗[k] (N ⟶ V)) :
    underlyingHom (homMap z) =
      TensorProduct.homTensorHomMap (RingHom.id k) M N U V
        (TensorProduct.map (restrictHom (k := k)) (restrictHom (k := k)) z) := by
  induction z using OAI.tensorInductionOn with
  | tmul f g => rfl
  | add z z' hz hz' =>
    rw [map_add]
    change underlyingHom (homMap z) + underlyingHom (homMap z') = _
    simp only [map_add, hz, hz']

lemma homMap_injective [FiniteDimensional k M] [FiniteDimensional k N] :
    Function.Injective (homMap (k := k) (M := M) (N := N) (U := U) (V := V)) := by
  intro x y h
  have h' := congrArg underlyingHom h
  rw [homMap_underlying, homMap_underlying,
    ← homTensorHomEquiv_apply, ← homTensorHomEquiv_apply] at h'
  have h'' := (homTensorHomEquiv k M N U V).injective h'
  exact TensorProduct.map_injective_of_flat_flat _ _ (restrictHom_injective (k := k))
    (restrictHom_injective (k := k)) h''

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)

lemma inductionComparison_surjective : Function.Surjective (inductionComparison φ ψ M N) := by
  intro z
  induction z using OAI.tensorInductionOn with
  | add z w hz hw =>
    obtain ⟨a,ha⟩ := hz
    obtain ⟨b,hb⟩ := hw
    exact ⟨a+b, by erw [map_add,ha,hb]; rfl⟩
  | tmul u v =>
    refine BalancedTensor.induction_on (k := k) (R := A) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := M) u ?_ ?_ ?_
    · exact ⟨0, by erw [map_zero, TensorProduct.zero_tmul]; rfl⟩
    · intro s x
      refine BalancedTensor.induction_on (k := k) (R := B) (S := T)
        (M := AlgebraInduction.Bimod ψ) (N := N) v ?_ ?_ ?_
      · exact ⟨0, by erw [map_zero, TensorProduct.tmul_zero]; rfl⟩
      · intro t y
        refine ⟨BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
          (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
            (show S from s) ⊗ₜ[k] (show T from t))
          (show Obj k A B M N from x ⊗ₜ[k] y), ?_⟩
        rw [inductionComparison_pure]
        congr 1
        · exact (AlgebraInduction.mk_one_smul φ M (show S from s) x).symm
        · exact (AlgebraInduction.mk_one_smul ψ N (show T from t) y).symm
      · intro v w hv hw
        obtain ⟨a,ha⟩ := hv
        obtain ⟨b,hb⟩ := hw
        exact ⟨a+b, by erw [map_add,ha,hb,TensorProduct.tmul_add]; rfl⟩
    · intro u w hu hw
      obtain ⟨a,ha⟩ := hu
      obtain ⟨b,hb⟩ := hw
      exact ⟨a+b, by erw [map_add,ha,hb,TensorProduct.add_tmul]; rfl⟩

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)

abbrev algebraTwist {R : Type} [Ring R] [Algebra k R] (ρ : R ≃ₐ[k] R) :=
  AlgebraInduction.res ρ.symm.toAlgHom

def restrictionGround {R : Type} [Ring R] [Algebra k R] (ρ : R ≃ₐ[k] R)
    (M : ModuleCat R) : (algebraTwist ρ).obj M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change ρ.symm (algebraMap k R c) • (show M from x) = c • (show M from x)
    rw [ρ.symm.commutes]
    rfl

def twistObjIso (M : ModuleCat A) (N : ModuleCat B) :
    ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N) ≅
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) := by
  let eq := TensorProduct.congr (restrictionGround σ M) (restrictionGround τ N)
  let e : Obj k A B ((algebraTwist σ).obj M) ((algebraTwist τ).obj N) ≃ₗ[k]
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) :=
    eq.trans ((underlyingEquiv M N).symm.trans
      (restrictionGround (Algebra.TensorProduct.congr σ τ) (((bifunctor k A B).obj M).obj N)).symm)
  let f : ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N) ⟶
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) :=
    ModuleCat.ofHom (X := ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N))
      (Y := (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N))
    { toFun := e
      map_add' := e.map_add
      map_smul' a z := by
        induction a using OAI.tensorInductionOn with
        | tmul a b =>
          induction z using OAI.tensorInductionOn with
          | tmul x y => rfl
          | add x y hx hy =>
            erw [smul_add, map_add, hx, hy, map_add, smul_add]
            rfl
        | add a b ha hb =>
          erw [add_smul, map_add, ha, hb, RingHom.id_apply, add_smul]
          rfl }
  exact (LinearEquiv.ofBijective f.hom e.bijective).toModuleIso

@[reassoc]
lemma twistObjIso_natural {M M' : ModuleCat A} {N N' : ModuleCat B}
    (f : M ⟶ M') (g : N ⟶ N') :
    morphism ((algebraTwist σ).map f) ((algebraTwist τ).map g) ≫ (twistObjIso σ τ M' N').hom =
      (twistObjIso σ τ M N).hom ≫ (algebraTwist (Algebra.TensorProduct.congr σ τ)).map (morphism f g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)
variable {I₁ I₂ : Type} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (P : HomologicalComplex (ModuleCat A) c₁) (Q : HomologicalComplex (ModuleCat B) c₂)

abbrev twistComplex {R : Type} [Ring R] [Algebra k R] {I : Type} {c : ComplexShape I}
    (ρ : R ≃ₐ[k] R) (K : HomologicalComplex (ModuleCat R) c) :=
  ((algebraTwist ρ).mapHomologicalComplex c).obj K

def twistBicomplexIso :
    outerBicomplex k A B (twistComplex σ P) (twistComplex τ Q) ≅
      TotalMap.map₂ (algebraTwist (Algebra.TensorProduct.congr σ τ)) (outerBicomplex k A B P Q) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => twistObjIso σ τ (P.X i) (Q.X j)) (by
        intro j j' _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        induction z using OAI.tensorInductionOn with
        | tmul x y => rfl
        | add x y hx hy =>
          exact (map_add _ x y).trans
            ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))) (by
      intro i i' _
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using OAI.tensorInductionOn with
      | tmul x y => rfl
      | add x y hx hy =>
        exact (map_add _ x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))

variable {J : Type} (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor P Q (bifunctor k A B) c]
  [HasMapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c]
  [(TotalMap.map₂ (algebraTwist (Algebra.TensorProduct.congr σ τ))
    (outerBicomplex k A B P Q)).HasTotal c]

def twistTotalIso :
    mapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c ≅
      twistComplex (Algebra.TensorProduct.congr σ τ) (mapBifunctor P Q (bifunctor k A B) c) :=
  HomologicalComplex₂.total.mapIso (twistBicomplexIso σ τ P Q) c ≪≫
    TotalMap.iso (algebraTwist (Algebra.TensorProduct.congr σ τ)) (outerBicomplex k A B P Q) c

@[reassoc]
lemma ι_twistTotalIso (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁,i₂) = j) :
    ιMapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c i₁ i₂ j h ≫
      (twistTotalIso σ τ P Q c).hom.f j =
    (twistObjIso σ τ (P.X i₁) (Q.X i₂)).hom ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map
        (ιMapBifunctor P Q (bifunctor k A B) c i₁ i₂ j h) := by
  change _ ≫ ((HomologicalComplex₂.total.mapIso (twistBicomplexIso σ τ P Q) c).hom.f j ≫ _) = _
  change HomologicalComplex₂.ιTotal _ c i₁ i₂ j h ≫
    ((HomologicalComplex₂.total.map (twistBicomplexIso σ τ P Q).hom c).f j ≫ _) = _
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map,Category.assoc]
  change (twistObjIso σ τ (P.X i₁) (Q.X i₂)).hom ≫ _ ≫
    TotalMap.compareX (algebraTwist (Algebra.TensorProduct.congr σ τ))
      (outerBicomplex k A B P Q) c j = _
  erw [TotalMap.ι_compareX]
  rfl

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def freeBasis {m : ℕ} (A : Type) [Ring A] (i : Fin m) : freeObj A m := Pi.single i 1

def freeTensorBasis {m n : ℕ} (i : Fin m) (j : Fin n) :
    (((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n)) := freeBasis A i ⊗ₜ[k] freeBasis B j

def freeAt {m : ℕ} (i : Fin m) (U : ModuleCat A) : U →ₗ[k] (freeObj A m ⟶ U) where
  toFun u := ModuleCat.ofHom
    { toFun := fun x => x i • u
      map_add' := fun x y => add_smul (x i) (y i) u
      map_smul' := fun r x => mul_smul r (x i) u }
  map_add' u v := ModuleCat.hom_ext (LinearMap.ext fun x => smul_add (x i) u v)
  map_smul' r u := ModuleCat.hom_ext (LinearMap.ext fun x => smul_comm (x i) r u)

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma morphism_comp {M M' M'' : ModuleCat A} {N N' N'' : ModuleCat B}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    morphism (k := k) f g ≫ morphism f' g' = morphism (f ≫ f') (g ≫ g') :=
  ModuleCat.hom_ext (map_comp f f' g g')

end Tachikawa.OuterTensor

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]

variable (M : C₁) (N : C₂)
variable [HasMapBifunctor ((ChainComplex.single₀ C₁).obj M)
  ((ChainComplex.single₀ C₂).obj N) F (.down ℕ)]

omit [HasZeroObject D] in
lemma singleBifunctor_isZero (n : ℕ) (hn : n ≠ 0) : IsZero ((singleBifunctor F M N).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j h
  rw [Category.comp_id, comp_zero]
  have hij : i + j = n := h
  by_cases hi : i = 0
  · have hj : j ≠ 0 := by omega
    exact ((F.obj _).map_isZero
      (isZero_single_obj_X (.down ℕ) 0 N j hj)).eq_of_src _ _
  · exact ((F.flip.obj _).map_isZero
      (isZero_single_obj_X (.down ℕ) 0 M i hi)).eq_of_src _ _

def bifunctorSingleIso : singleBifunctor F M N ≅
    (ChainComplex.single₀ D).obj ((F.obj M).obj N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => if hn : n = 0 then by
      subst n
      exact bifunctorZeroIso F _ _
    else (singleBifunctor_isZero F M N n hn).iso
      (isZero_single_obj_X (.down ℕ) 0 ((F.obj M).obj N) n hn)) (by
      intro i j hij
      cases i with
      | zero => simp only [ComplexShape.down_Rel] at hij; omega
      | succ i => exact (singleBifunctor_isZero F M N (i+1) (by omega)).eq_of_src _ _)

end Tachikawa



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
@[reassoc]
lemma tensorF_maps {k : Type} [Field k] {U U' V V' : ModuleCat k}
    (u : U ⟶ U') (v : V ⟶ V') :
    ((tensorF k).map u).app V ≫ ((tensorF k).obj U').map v =
      ModuleCat.ofHom (TensorProduct.map u.hom v.hom) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

end Tachikawa.OuterTensor

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Corner
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa
open scoped TensorProduct

variable {k : Type*} [Field k] (q : k)

lemma trace_left_right_pf [CharP k 2] (a : B q) :
    LinearMap.trace k (B q) ((LinearMap.mulLeft k a).comp (LinearMap.mulRight k (pf q))) = 0 := by
  induction a using OAI.tensorInductionOn with
  | tmul a b =>
    have he : (LinearMap.mulLeft k (a ⊗ₜ[k] b)).comp (LinearMap.mulRight k (pf q)) =
        TensorProduct.map
          ((LinearMap.mulLeft k a).comp (LinearMap.mulRight k (C.f q)))
          ((LinearMap.mulLeft k b).comp (LinearMap.mulRight k (C.f q))) := by
      ext x y
      simp [pf, Algebra.TensorProduct.tmul_mul_tmul]
    rw [he, LinearMap.trace_tensorProduct']
    rw [C.trace_left_right_f_eq_zero]
    simp
  | add a b ha hb =>
    have he : (LinearMap.mulLeft k (a + b)).comp (LinearMap.mulRight k (pf q)) =
        (LinearMap.mulLeft k a).comp (LinearMap.mulRight k (pf q)) +
        (LinearMap.mulLeft k b).comp (LinearMap.mulRight k (pf q)) := by
      ext x
      simp [add_mul]
    rw [he, map_add, ha, hb, add_zero]

end Tachikawa



namespace Tachikawa

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R]

lemma outer_to_dual_formula
    (β : (R →ₗ[k] R) →ₗ[k] Module.Dual k R)
    (hleft : ∀ (a : R) (F : R →ₗ[k] R),
      β (F.comp (LinearMap.mulRight k a)) = (β F).comp (LinearMap.mulRight k a))
    (hright : ∀ (a : R) (F : R →ₗ[k] R),
      β ((LinearMap.mulRight k a).comp F) = (β F).comp (LinearMap.mulLeft k a)) :
    ∃ b : R, ∀ (φ : Module.Dual k R) (c p : R),
      β (φ.smulRight c) p = φ (b * c * p) := by
  let t : Module.Dual k R →ₗ[k] (R →ₗ[k] R) := LinearMap.smulRightₗ.flip 1
  let η : Module.Dual k R →ₗ[k] Module.Dual k R := β.comp t
  let b : R := (Module.evalEquiv k R).symm ((LinearMap.applyₗ (1 : R)).comp η)
  have hb (φ : Module.Dual k R) : φ b = β (φ.smulRight 1) 1 := by
    exact Module.apply_evalEquiv_symm_apply k R φ _
  have ht (φ : Module.Dual k R) (p : R) : β (φ.smulRight 1) p = φ (b * p) := by
    have h := congrArg (fun g : Module.Dual k R => g 1) (hleft p (φ.smulRight 1))
    have he : (φ.smulRight (1 : R)).comp (LinearMap.mulRight k p) =
        (φ.comp (LinearMap.mulRight k p)).smulRight 1 := by
      ext x
      rfl
    rw [he] at h
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, one_mul] at h
    rw [← hb] at h
    exact h.symm
  refine ⟨b, ?_⟩
  intro φ c p
  have he : (LinearMap.mulRight k c).comp (φ.smulRight (1 : R)) = φ.smulRight c := by
    ext x
    simp
  have h := congrArg (fun g : Module.Dual k R => g p) (hright c (φ.smulRight 1))
  rw [he] at h
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
  rw [h, ht, mul_assoc]

omit [FiniteDimensional k R] in

lemma outer_central_is_mulLeft (F : R →ₗ[k] R)
    (hF : ∀ a : R, F.comp (LinearMap.mulRight k a) = (LinearMap.mulRight k a).comp F) :
    F = LinearMap.mulLeft k (F 1) := by
  ext x
  have h := congrArg (fun g : R →ₗ[k] R => g 1) (hF x)
  simpa using h

lemma outer_factorization_trace
    (F : R →ₗ[k] R)
    (hF : ∀ a : R, F.comp (LinearMap.mulRight k a) = (LinearMap.mulRight k a).comp F)
    (β : (R →ₗ[k] R) →ₗ[k] Module.Dual k R)
    (hleft : ∀ (a : R) (G : R →ₗ[k] R),
      β (G.comp (LinearMap.mulRight k a)) = (β G).comp (LinearMap.mulRight k a))
    (hright : ∀ (a : R) (G : R →ₗ[k] R),
      β ((LinearMap.mulRight k a).comp G) = (β G).comp (LinearMap.mulLeft k a)) :
    ∃ d : R, ∀ p : R, β F p =
      LinearMap.trace k R ((LinearMap.mulLeft k d).comp (LinearMap.mulRight k p)) := by
  classical
  obtain ⟨b, hb⟩ := outer_to_dual_formula β hleft hright
  refine ⟨b * F 1, ?_⟩
  intro p
  let e := Module.finBasis k R
  conv_lhs => rw [end_expansion e F]
  simp only [map_sum, LinearMap.sum_apply, hb]
  rw [LinearMap.trace_eq_matrix_trace k e]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  have hFi : F (e i) = F 1 * e i := by
    rw [outer_central_is_mulLeft F hF]
    simp
  simp only [Module.Basis.coord_apply, hFi, mul_assoc]

end Tachikawa



namespace Tachikawa
open scoped TensorProduct
variable {k : Type*} [Field k] (q : k)

def characterMapB : B q →ₗ[k] Module.Dual k (B q) :=
  (characterB q).toLinearMap.smulRight (characterB q).toLinearMap

lemma characterMapB_left (a b : B q) : characterMapB q (a * b) =
    (characterMapB q b).comp (LinearMap.mulRight k a) := by
  ext c
  simp [characterMapB, mul_comm, mul_left_comm]

lemma characterMapB_right (a b : B q) : characterMapB q (a * b) =
    (characterMapB q a).comp (LinearMap.mulLeft k b) := by
  ext c
  simp [characterMapB, mul_assoc]

lemma characterMapB_one_pf : characterMapB q 1 (pf q) = 1 := by
  simp [characterMapB]

variable [CharP k 2]

lemma ordinary_factorization_pf_zero
    (α : B q →ₗ[k] (B q →ₗ[k] B q))
    (hαleft : ∀ a b : B q, α (a * b) = (α b).comp (LinearMap.mulRight k a))
    (hαright : ∀ a b : B q, α (a * b) = (LinearMap.mulRight k b).comp (α a))
    (β : (B q →ₗ[k] B q) →ₗ[k] Module.Dual k (B q))
    (hβleft : ∀ (a : B q) (F : B q →ₗ[k] B q),
      β (F.comp (LinearMap.mulRight k a)) = (β F).comp (LinearMap.mulRight k a))
    (hβright : ∀ (a : B q) (F : B q →ₗ[k] B q),
      β ((LinearMap.mulRight k a).comp F) = (β F).comp (LinearMap.mulLeft k a)) :
    β (α 1) (pf q) = 0 := by
  have hα : ∀ a : B q, (α 1).comp (LinearMap.mulRight k a) =
      (LinearMap.mulRight k a).comp (α 1) := by
    intro a
    rw [← hαleft, ← hαright, mul_one, one_mul]
  obtain ⟨d, hd⟩ := outer_factorization_trace (α 1) hα β hβleft hβright
  rw [hd, trace_left_right_pf]

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma reverseCoeff_step (hq : q ≠ 0) (n : ℕ) :
    q * reverseCoeff q (n+1) = reverseCoeff q n := by
  unfold reverseCoeff
  rw [show n+1+2=(n+2)+1 by omega, pow_succ, mul_inv_rev]
  rw [← _root_.mul_assoc, mul_inv_cancel₀ hq, one_mul]

end Tachikawa.C



end



noncomputable section



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

instance objFinite (M : ModuleCat.{0} A) (N : ModuleCat.{0} B)
    [FiniteDimensional k M] [FiniteDimensional k N] :
    Module.Finite (A ⊗[k] B) (Obj k A B M N) := by
  have : FiniteDimensional k (Obj k A B M N) := inferInstanceAs (FiniteDimensional k (M ⊗[k] N))
  exact Module.Finite.of_restrictScalars_finite k _ _

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace HomBimodule
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) (Z : ModuleCat S)

lemma tmul_smul_apply (s : S) (r : Rᵐᵒᵖ) (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z from ((s ⊗ₜ[k] r) • f)) x =
      s • (show X →ₗ[k] Z from f) (r.unop • x) := rfl

lemma k_smul_apply (c : k) (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z from (c • f)) x = c • (show X →ₗ[k] Z from f) x := by
  change (show X →ₗ[k] Z from ((algebraMap k (Enveloping.Alg k S R) c) • f)) x = _
  change (show X →ₗ[k] Z from (((algebraMap k S c) ⊗ₜ[k] (1:Rᵐᵒᵖ)) • f)) x = _
  apply Eq.trans (tmul_smul_apply X Z (algebraMap k S c) 1 f x)
  exact (congrArg (fun y : X => (algebraMap k S c) • (show X →ₗ[k] Z from f) y)
    (one_smul R x)).trans (IsScalarTower.algebraMap_smul S c ((show X →ₗ[k] Z from f) x))

end HomBimodule



end Tachikawa



namespace Tachikawa
open CategoryTheory
variable {R M P N : Type} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N]

lemma projective_cokernel_of_injective [Module.Injective R M] [Module.Projective R P]
    (i : M →ₗ[R] P) (q : P →ₗ[R] N)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q) :
    Module.Projective R N := by
  let h := linearShortExact i q he hi hq
  have : CategoryTheory.Injective (linearShortComplex i q he).X₁ :=
    show CategoryTheory.Injective (ModuleCat.of R M) from Module.injective_object_of_injective_module R M
  have : Module.Projective R (linearShortComplex i q he).X₂ :=
    show Module.Projective R P from inferInstance
  let s := h.splittingOfInjective
  exact Module.Projective.of_split s.s.hom q (ModuleCat.hom_ext_iff.mp s.s_g)

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace NatCoker
variable (P : ChainComplex (ModuleCat R) ℕ) (n : ℕ)

def ι : C P n →ₗ[R] P.X n :=
  (LinearMap.range (P.d (n+2) (n+1)).hom).liftQ (P.d (n+1) n).hom (by
    rintro x ⟨y,rfl⟩
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (P.d_comp_d (n+2) (n+1) n)) y)

lemma projective_of_contraction [Module.Projective R (P.X n)]
    (a : P.X n →ₗ[R] P.X (n+1)) (b : P.X (n+1) →ₗ[R] P.X (n+2))
    (h : a.comp (P.d (n+1) n).hom + (P.d (n+2) (n+1)).hom.comp b = LinearMap.id) :
    Module.Projective R (C P n) := by
  apply Module.Projective.of_split (ι P n) ((π P n).comp a)
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n+2) (n+1)).hom) x
  change π P n (a (P.d (n+1) n y)) = π P n y
  have he := congrArg (π P n) (LinearMap.congr_fun h y)
  change π P n (a (P.d (n+1) n y) + P.d (n+2) (n+1) (b y)) = π P n y at he
  rw [map_add] at he
  have hz : π P n (P.d (n+2) (n+1) (b y)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨b y,rfl⟩
  simpa only [hz,add_zero] using he

lemma projective_of_homotopy {Q : ChainComplex (ModuleCat R) ℕ}
    (e : HomotopyEquiv P Q) [Subsingleton (Q.X (n+1))]
    [Module.Projective R (P.X n)] : Module.Projective R (C P n) := by
  let h := e.homotopyHomInvId.symm
  have he := h.comm (n+1)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at he
  have hz : (e.hom ≫ e.inv).f (n+1) = 0 := by
    apply ModuleCat.hom_ext
    ext x
    change e.inv.f (n+1) (e.hom.f (n+1) x) = 0
    rw [Subsingleton.elim (e.hom.f (n+1) x) 0, map_zero]
  rw [hz,add_zero] at he
  exact projective_of_contraction P n (h.hom n (n+1)).hom (h.hom (n+1) (n+2)).hom
    (ModuleCat.hom_ext_iff.mp he.symm)

end NatCoker
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)

def restrictionUnderlyingEquiv (X : ModuleCat.{0} S) :
    (AlgebraInduction.res φ).obj X ≃ₗ[k] X where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) • (show X from x) = (algebraMap k S c) • (show X from x)
    rw [φ.commutes]

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
lemma homBase_smul {K R : Type} [Field K] [Ring R] [Algebra K R]
    (V : ModuleCat R) (f : HomBimodule.Base (k := K) V V) (c : K) (x : V) :
    f (c • x) = c • f x := (show V →ₗ[K] V from f).map_smul c x

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev StableMap (M N : ModuleCat.{0} R) :=
  StableHom (k := k) (R := R) (M := M) (N := N)

structure StableEquiv (M N : ModuleCat.{0} R) where
  hom : M →ₗ[R] N
  inv : N →ₗ[R] M
  inv_hom : inv.comp hom - LinearMap.id ∈ projectiveFactors (k := k)
  hom_inv : hom.comp inv - LinearMap.id ∈ projectiveFactors (k := k)

variable {M N L : ModuleCat.{0} R}

lemma stableClass_eq_iff (f g : M →ₗ[R] N) :
    stableClass (k := k) f = stableClass (k := k) g ↔
      f-g ∈ projectiveFactors (k := k) := by
  rw [← sub_eq_zero, ← map_sub, stableClass_eq_zero_iff]

def stablePrecompose (g : L →ₗ[R] M) : StableMap (k := k) M N →ₗ[k] StableMap (k := k) L N :=
  (projectiveFactors (k := k)).mapQ (projectiveFactors (k := k))
    (homPrecompose g) (fun _ hf => projectiveFactors_precomp hf g)

@[simp] lemma stablePrecompose_class (g : L →ₗ[R] M) (f : M →ₗ[R] N) :
    stablePrecompose (k := k) g (stableClass (k := k) f) =
      stableClass (k := k) (f.comp g) := rfl

namespace StableEquiv

def refl (M : ModuleCat.{0} R) : StableEquiv (k := k) M M where
  hom := LinearMap.id
  inv := LinearMap.id
  inv_hom := by simp only [LinearMap.id_comp, sub_self]; exact Submodule.zero_mem _
  hom_inv := by simp only [LinearMap.id_comp, sub_self]; exact Submodule.zero_mem _

def symm (e : StableEquiv (k := k) M N) : StableEquiv (k := k) N M where
  hom := e.inv
  inv := e.hom
  inv_hom := e.hom_inv
  hom_inv := e.inv_hom

def ofLinearEquiv (e : M ≃ₗ[R] N) : StableEquiv (k := k) M N where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  inv_hom := by
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; exact e.symm_apply_apply x
    rw [h, sub_self]; exact Submodule.zero_mem _
  hom_inv := by
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; exact e.apply_symm_apply x
    rw [h, sub_self]; exact Submodule.zero_mem _

lemma post_inverse (e : StableEquiv (k := k) M N) (f : L →ₗ[R] M) :
    stableClass (k := k) (e.inv.comp (e.hom.comp f)) = stableClass (k := k) f := by
  apply (stableClass_eq_iff _ _).mpr
  have h := projectiveFactors_precomp e.inv_hom f
  simpa only [LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc] using h

lemma pre_inverse (e : StableEquiv (k := k) M N) (f : M →ₗ[R] L) :
    stableClass (k := k) ((f.comp e.inv).comp e.hom) = stableClass (k := k) f := by
  apply (stableClass_eq_iff _ _).mpr
  have h := projectiveFactors_postcomp e.inv_hom f
  simpa only [LinearMap.comp_sub, LinearMap.comp_id, LinearMap.comp_assoc] using h

def post (e : StableEquiv (k := k) M N) (L : ModuleCat.{0} R) :
    StableMap (k := k) L M ≃ₗ[k] StableMap (k := k) L N :=
  { stablePostcompose e.hom with
    invFun := stablePostcompose e.inv
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.post_inverse f
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.symm.post_inverse f }

def pre (e : StableEquiv (k := k) M N) (L : ModuleCat.{0} R) :
    StableMap (k := k) M L ≃ₗ[k] StableMap (k := k) N L :=
  { stablePrecompose e.inv with
    invFun := stablePrecompose e.hom
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.pre_inverse f
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.symm.pre_inverse f }

def trans (e : StableEquiv (k := k) M N) (d : StableEquiv (k := k) N L) :
    StableEquiv (k := k) M L where
  hom := d.hom.comp e.hom
  inv := e.inv.comp d.inv
  inv_hom := by
    have h := projectiveFactors_postcomp (projectiveFactors_precomp d.inv_hom e.hom) e.inv
    have heq : (e.inv.comp d.inv).comp (d.hom.comp e.hom) - LinearMap.id =
        (e.inv.comp ((d.inv.comp d.hom - LinearMap.id).comp e.hom)) +
        (e.inv.comp e.hom - LinearMap.id) := by
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
        LinearMap.comp_assoc]
      abel
    rw [heq]
    exact Submodule.add_mem _ h e.inv_hom
  hom_inv := by
    have h := projectiveFactors_postcomp (projectiveFactors_precomp e.hom_inv d.inv) d.hom
    have heq : (d.hom.comp e.hom).comp (e.inv.comp d.inv) - LinearMap.id =
        (d.hom.comp ((e.hom.comp e.inv - LinearMap.id).comp d.inv)) +
        (d.hom.comp d.inv - LinearMap.id) := by
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
        LinearMap.comp_assoc]
      abel
    rw [heq]
    exact Submodule.add_mem _ h d.hom_inv

end StableEquiv
end Tachikawa



namespace Tachikawa.NatCoker
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q S : ChainComplex (ModuleCat.{0} R) ℕ}

abbrev obj (P : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) := ModuleCat.of R (C P n)

@[simp] lemma map_π (f : P ⟶ Q) (n : ℕ) (x : P.X (n+1)) :
    map f n (π P n x) = π Q n (f.f (n+1) x) := rfl

@[simp] lemma map_id (n : ℕ) : map (𝟙 P) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

@[simp] lemma map_comp (f : P ⟶ Q) (g : Q ⟶ S) (n : ℕ) :
    map (f ≫ g) n = (map g n).comp (map f n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

lemma homotopy_factors (f g : P ⟶ Q) (h : Homotopy f g) (n : ℕ)
    [Module.Finite R (P.X n)] [Module.Projective R (P.X n)] :
    map f n - map g n ∈ projectiveFactors (k := k)
      (M := obj P n) (N := obj Q n) := by
  have he : map f n - map g n =
      ((π Q n).comp (h.hom n (n+1)).hom).comp (ι P n) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
    have hc := h.comm (n+1)
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl),
      prevD_eq _ (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at hc
    have hx := congrArg (fun u : P.X (n+1) ⟶ Q.X (n+1) => π Q n (u y)) hc
    change π Q n (f.f (n+1) y) = π Q n
      ((h.hom n (n+1)) (P.d (n+1) n y) +
        Q.d (n+2) (n+1) (h.hom (n+1) (n+2) y) + g.f (n+1) y) at hx
    have hz : π Q n (Q.d (n+2) (n+1) (h.hom (n+1) (n+2) y)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩
    simp only [map_add, hz, add_zero] at hx
    change π Q n (f.f (n+1) y) - π Q n (g.f (n+1) y) = _
    rw [hx, add_sub_cancel_right]
    rfl
  rw [he]
  exact ⟨P.X n,inferInstance,inferInstance,ι P n,
    (π Q n).comp (h.hom n (n+1)).hom,rfl⟩

def stableEquiv (e : HomotopyEquiv P Q) (n : ℕ)
    [Module.Finite R (P.X n)] [Module.Projective R (P.X n)]
    [Module.Finite R (Q.X n)] [Module.Projective R (Q.X n)] :
    StableEquiv (k := k) (obj P n) (obj Q n) where
  hom := map e.hom n
  inv := map e.inv n
  inv_hom := by
    simpa only [map_comp, map_id] using homotopy_factors _ _ e.homotopyHomInvId n
  hom_inv := by
    simpa only [map_comp, map_id] using homotopy_factors _ _ e.homotopyInvHomId n

end Tachikawa.NatCoker



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

lemma goodComponent_up_at
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l)
    (hq : Function.Exact (Q.d l j) (Q.d j i))
    [Module.Projective R (P.X j)]
    (a : P.X i →ₗ[R] Q.X j) (ha : GoodComponent f i j a) :
    ∃ b : P.X j →ₗ[R] Q.X l,
      (f.f j).hom = a.comp (P.d j i).hom + (Q.d l j).hom.comp b ∧
      GoodComponent f j l b := by
  let r := (f.f j).hom - a.comp (P.d j i).hom
  have hr (x : P.X j) : r x ∈ LinearMap.range (Q.d l j).hom := by
    have he := hq
    have hi : i = j-1 := by omega
    have hl : l = j+1 := by omega
    subst i
    subst l
    apply (he _).mp
    have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm j (j-1))) x
    change Q.d j (j-1) (f.f j x) = f.f (j-1) (P.d j (j-1) x) at hc
    have hh := LinearMap.congr_fun ha x
    change f.f (j-1) (P.d j (j-1) x) - Q.d j (j-1) (a (P.d j (j-1) x)) = 0 at hh
    change Q.d j (j-1) (f.f j x - a (P.d j (j-1) x)) = 0
    rw [map_sub, hc]
    exact hh
  obtain ⟨b, hb⟩ := Module.projective_lifting_property
    (Q.d l j).hom.rangeRestrict (r.codRestrict _ hr) (by rintro ⟨x, y, rfl⟩; exact ⟨y, rfl⟩)
  have hb' : (Q.d l j).hom.comp b = r := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hb x)
  refine ⟨b, ?_, ?_⟩
  · rw [hb']
    dsimp only [r]
    abel
  · unfold GoodComponent
    rw [hb']
    dsimp only [r]
    rw [sub_sub_cancel, LinearMap.comp_assoc]
    have hd : (P.d j i).hom.comp (P.d l j).hom = 0 :=
      ModuleCat.hom_ext_iff.mp (P.d_comp_d _ _ _)
    rw [hd, LinearMap.comp_zero]

section Initial
variable {k : Type} [Field k] [Algebra k R] [Module.Injective R R]

lemma tail_initial_component (n : ℤ)
    (hp : Function.Exact (P.d (n+1) n) (P.d n (n-1)))
    (hf : CokerAt.map f n ∈ projectiveFactors (k := k)) :
    ∃ a : P.X (n-1) →ₗ[R] Q.X n, GoodComponent f (n-1) n a := by
  obtain ⟨J, hJf, hJp, u, v, hvu⟩ := hf
  let := hJf
  let := hJp
  let : Module.Injective R J := injective_of_finite_projective
  obtain ⟨u', hu⟩ := Module.Injective.extension_property R J
    (CokerAt P n) (P.X (n-1)) (CokerAt.ι P n) (CokerAt.ι_injective P n hp) u
  obtain ⟨v', hv⟩ := Module.projective_lifting_property (CokerAt.π Q n) v
    (CokerAt.π_surjective Q n)
  refine ⟨v'.comp u', ?_⟩
  unfold GoodComponent
  apply LinearMap.ext
  intro x
  have h : CokerAt.π Q n (f.f n x - v' (u' (P.d n (n-1) x))) = 0 := by
    have hu' := LinearMap.congr_fun hu (CokerAt.π P n x)
    change u' (P.d n (n-1) x) = u (CokerAt.π P n x) at hu'
    rw [map_sub, hu']
    have hv' := LinearMap.congr_fun hv (u (CokerAt.π P n x))
    dsimp only [LinearMap.comp_apply] at hv'
    have hvu' := LinearMap.congr_fun hvu (CokerAt.π P n x)
    change v (u (CokerAt.π P n x)) = CokerAt.π Q n (f.f n x) at hvu'
    rw [hv', hvu', sub_self]
  have hz := congrArg (CokerAt.ι Q n) h
  rw [map_zero, CokerAt.ι_π] at hz
  change Q.d n (n-1) (f.f n x - v' (u' (P.d n (n-1) x))) = 0 at hz
  have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm n (n-1))) x
  change Q.d n (n-1) (f.f n x) = f.f (n-1) (P.d n (n-1) x) at hc
  change f.f (n-1) (P.d n (n-1) x) - Q.d n (n-1) (v' (u' (P.d n (n-1) x))) = 0
  rw [map_sub, hc] at hz
  exact hz
end Initial

namespace TailNull
variable (n : ℤ)

def State (j : ℤ) :=
  {a : P.X j →ₗ[R] Q.X (j+1) // n-1 ≤ j → GoodComponent f j (j+1) a}

variable (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
variable (pproj : ∀ j, Module.Projective R (P.X j))

def up (j : ℤ) (hj : n-1 ≤ j) (a : State f n j) : State f n (j+1) := by
  let := pproj (j+1)
  have he : Function.Exact (Q.d (j+1+1) (j+1)) (Q.d (j+1) j) := by
    exact exact_tail_at n hq j (j+1) (j+1+1) rfl rfl (by omega)
  let hh := goodComponent_up_at f j (j+1) (j+1+1) rfl rfl he a.val (a.property hj)
  exact ⟨hh.choose, fun _ => hh.choose_spec.2⟩

def stateMap {i : ℤ} (a : State f n i) (j : ℤ) (h : i+1=j) : P.X i →ₗ[R] Q.X j := by
  subst j
  exact a.val

def Step (i j : ℤ) (h : i+1=j) (a : State f n i) (b : State f n j) : Prop :=
  (f.f j).hom = (stateMap f n a j h).comp (P.d j i).hom + (Q.d (j+1) j).hom.comp b.val

lemma up_step (j : ℤ) (hj : n-1 ≤ j) (a : State f n j) :
    Step f n j (j+1) rfl a (up f n hq pproj j hj a) := by
  let := pproj (j+1)
  have he : Function.Exact (Q.d (j+1+1) (j+1)) (Q.d (j+1) j) := by
    exact exact_tail_at n hq j (j+1) (j+1+1) rfl rfl (by omega)
  exact (goodComponent_up_at f j (j+1) (j+1+1) rfl rfl he a.val (a.property hj)).choose_spec.1

variable (a₀ : State f n (n-1))

def component (j : ℤ) : State f n j :=
  j.inductionOn' (n-1) a₀ (fun j hj => up f n hq pproj j hj)
    (fun j hj _ => ⟨0, fun h => by omega⟩)

lemma component_up (j : ℤ) (hj : n-1 ≤ j) :
    component f n hq pproj a₀ (j+1) = up f n hq pproj j hj (component f n hq pproj a₀ j) :=
  Int.inductionOn'_add_one hj

lemma hasStep (i j : ℤ) (h : i+1=j) (hj : n ≤ j) :
    Step f n i j h (component f n hq pproj a₀ i) (component f n hq pproj a₀ j) := by
  subst j
  have hi : n-1 ≤ i := by omega
  rw [component_up f n hq pproj a₀ i hi]
  exact up_step f n hq pproj i hi _

def hom (i j : ℤ) : P.X i ⟶ Q.X j :=
  if h : i+1=j then ModuleCat.ofHom (stateMap f n (component f n hq pproj a₀ i) j h) else 0

lemma hom_zero (i j : ℤ) (h : ¬ (ComplexShape.down ℤ).Rel j i) :
    hom f n hq pproj a₀ i j = 0 := dite_eq_right h

lemma nullHomotopicMap_f (j : ℤ) (hj : n ≤ j) :
    (Homotopy.nullHomotopicMap (hom f n hq pproj a₀)).f j = f.f j := by
  rw [Homotopy.nullHomotopicMap_f
    (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)
    (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega)]
  simp only [hom, dite_eq_left (show j-1+1=j by omega)]
  apply ModuleCat.hom_ext
  exact (hasStep f n hq pproj a₀ (j-1) j (by omega) hj).symm

end TailNull

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt C]

lemma projective_dimension_of_bounded_resolution {X : C} (P : ProjectiveResolution X)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) :
    HasProjectiveDimensionLE X d := by
  apply HasProjectiveDimensionLT.mk
  intro n hn Y e
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let : Subsingleton (Ext X Y (m+1)) := ext_subsingleton_of_boundaries P m (by
    intro f hf
    refine ⟨0, ?_⟩
    rw [comp_zero]
    exact (h (m+1) (by omega)).eq_of_src 0 f)
  exact Subsingleton.elim _ _

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
attribute [instance] IndReplacement.quasiIso

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C]
variable {K L : CochainComplex C ℤ}

lemma raise_cochain_map (n : ℕ) (f : K ⟶ L)
    (hf : ∀ j, j < -(n+1 : ℤ) → f.f j = 0) (hb : HomColumnBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, j < -(n : ℤ) → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  classical
  have hc : K.d (-(n+2 : ℤ)) (-(n+1 : ℤ)) ≫ f.f (-(n+1 : ℤ)) = 0 := by
    rw [← f.comm, hf _ (by omega), zero_comp]
  obtain ⟨g,hg⟩ := hb n (f.f (-(n+1 : ℤ))) hc
  let h : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = -(n : ℤ) then if hj : j = -(n+1 : ℤ) then
      eqToHom (congrArg K.X hi) ≫ g ≫ eqToHom (congrArg L.X hj.symm)
      else 0 else 0
  have hh : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0 := by
    intro i j hij
    dsimp only [h]
    split_ifs with hi hj
    · subst i; subst j
      exact False.elim (hij (by change -(n+1 : ℤ)+1= -(n : ℤ); omega))
    all_goals rfl
  let z := Homotopy.nullHomotopicMap h
  have hz (j : ℤ) : z.f j = K.d j (j+1) ≫ h (j+1) j + h j (j-1) ≫ L.d (j-1) j :=
    Homotopy.nullHomotopicMap_f (by change j-1+1=j; omega) rfl h
  refine ⟨f-z, ?_, ?_⟩
  · intro j hj
    change f.f j - z.f j = 0
    rw [hz]
    have h1 : j ≠ -(n : ℤ) := by omega
    by_cases h2 : j = -(n+1 : ℤ)
    · subst j
      have hi : -(n+1 : ℤ)+1= -(n : ℤ) := by omega
      rw [hi]
      simp only [h, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id,
        dite_eq_right h1, zero_comp, add_zero, hg, sub_self]
    · have h3 : j+1 ≠ -(n : ℤ) := by omega
      simp only [h, dite_eq_right h1, dite_eq_right h3, comp_zero, zero_comp, add_zero,
        hf j (by omega), sub_self]
  · apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have he : f-(f-z)=z := by abel
    rw [he]
    exact Homotopy.nullHomotopy h hh

theorem cochain_map_supported_nonnegative (N : ℕ) (f : K ⟶ L)
    (hf : ∀ j, j < -(N : ℤ) → f.f j = 0) (hb : HomColumnBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, j < 0 → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  induction N generalizing f with
  | zero => exact ⟨f,by simpa using hf,⟨Homotopy.refl f⟩⟩
  | succ N ih =>
    obtain ⟨g,hg,⟨H⟩⟩ := raise_cochain_map N f (by simpa using hf) hb
    obtain ⟨f',hf',⟨H'⟩⟩ := ih g hg
    exact ⟨f',hf',⟨H.trans H'⟩⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable {X : C} (P : ProjectiveResolution X) {L : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem bounded_cochain_resolution_descends (N : ℕ) (f : P.cochainComplex ⟶ L)
    (hL : ∀ j, j < -(N : ℤ) → IsZero (L.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1))) :
    ∃ g : (CochainComplex.singleFunctor C 0).obj X ⟶ L,
      Nonempty (Homotopy f (P.π' ≫ g)) := by
  obtain ⟨f',hf',H⟩ := cochain_map_supported_nonnegative N f
    (fun j hj => (hL j hj).eq_of_tgt _ _)
    (resolution_HomColumnBoundaries P L hExt)
  let e0 := P.cochainComplexXIso 0 0 rfl
  let e1 := P.cochainComplexXIso (-1) 1 rfl
  have hc : P.cochainComplex.d (-1) 0 ≫ f'.f 0 = 0 := by
    rw [← f'.comm, hf' (-1) (by omega), zero_comp]
  have hc' : P.complex.d 1 0 ≫ e0.inv ≫ f'.f 0 = 0 := by
    have hs := congrArg (fun t => e1.inv ≫ t) hc
    rw [P.cochainComplex_d (-1) 0 1 0 rfl rfl] at hs
    simpa only [e0,e1,Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using hs
  let s : CokernelCofork (P.complex.d 1 0) := CokernelCofork.ofπ (e0.inv ≫ f'.f 0) hc'
  let a : X ⟶ L.X 0 := P.isColimitCokernelCofork.desc s
  have ha : P.π.f 0 ≫ a = e0.inv ≫ f'.f 0 :=
    P.isColimitCokernelCofork.fac s WalkingParallelPair.one
  have hd : P.cochainComplex.d 0 1 = 0 :=
    (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 1).eq_of_tgt _ _
  have hca : ∀ j, (ComplexShape.up ℤ).Rel 0 j → a ≫ L.d 0 j = 0 := by
    intro j hj
    have hj' : j=1 := by change 0+1=j at hj; omega
    rw [hj']
    apply (cancel_epi (P.π.f 0)).1
    erw [← Category.assoc, ha, Category.assoc, f'.comm]
    change e0.inv ≫ P.cochainComplex.d 0 1 ≫ f'.f 1 = P.π.f 0 ≫ 0
    rw [hd,zero_comp,comp_zero,comp_zero]
  let g : (CochainComplex.singleFunctor C 0).obj X ⟶ L := mkHomFromSingle a hca
  have he : P.π' ≫ g = f' := by
    apply HomologicalComplex.Hom.ext
    funext j
    by_cases hj : j=0
    · subst j
      simp only [comp_f, g, mkHomFromSingle_f, P.π'_f_zero, Category.assoc]
      erw [Iso.inv_hom_id_assoc, ha]
      simp only [e0, Iso.hom_inv_id_assoc]
    · by_cases hneg : j<0
      · rw [comp_f, hf' j hneg]
        have hp : P.π'.f j = 0 :=
          (isZero_single_obj_X (ComplexShape.up ℤ) 0 X j hj).eq_of_tgt _ _
        rw [hp,zero_comp]
      · exact (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 j (by omega)).eq_of_src _ _
  exact ⟨g, he.symm ▸ H⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C]
variable {K L : CochainComplex C ℤ}

lemma lower_cochain_map (n : ℕ) (f : K ⟶ L)
    (hf : ∀ j, (n+1 : ℤ) < j → f.f j = 0) (hb : HomRowBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, (n : ℤ) < j → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  classical
  have hc : f.f (n+1 : ℤ) ≫ L.d (n+1 : ℤ) (n+2 : ℤ) = 0 := by
    rw [f.comm, hf _ (by omega), comp_zero]
  obtain ⟨g,hg⟩ := hb n (f.f (n+1 : ℤ)) hc
  let h : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = (n+1 : ℤ) then if hj : j = (n : ℤ) then
      eqToHom (congrArg K.X hi) ≫ g ≫ eqToHom (congrArg L.X hj.symm)
      else 0 else 0
  have hh : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0 := by
    intro i j hij
    dsimp only [h]
    split_ifs with hi hj
    · subst i; subst j
      exact False.elim (hij (by rfl))
    all_goals rfl
  let z := Homotopy.nullHomotopicMap h
  have hz (j : ℤ) : z.f j = K.d j (j+1) ≫ h (j+1) j + h j (j-1) ≫ L.d (j-1) j :=
    Homotopy.nullHomotopicMap_f (by change j-1+1=j; omega) rfl h
  refine ⟨f-z, ?_, ?_⟩
  · intro j hj
    change f.f j - z.f j = 0
    rw [hz]
    have h1 : j+1 ≠ (n+1 : ℤ) := by omega
    by_cases h2 : j = (n+1 : ℤ)
    · subst j
      have hi : (n+1 : ℤ)-1= (n : ℤ) := by omega
      rw [hi]
      simp only [h, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id,
        dite_eq_right h1, comp_zero, zero_add, hg, sub_self]
    · simp only [h, dite_eq_right h1, dite_eq_right h2, comp_zero, zero_comp, add_zero,
        hf j (by omega), sub_self]
  · apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have he : f-(f-z)=z := by abel
    rw [he]
    exact Homotopy.nullHomotopy h hh

theorem cochain_map_supported_nonpositive (N : ℕ) (f : K ⟶ L)
    (hf : ∀ j, (N : ℤ) < j → f.f j = 0) (hb : HomRowBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, 0 < j → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  induction N generalizing f with
  | zero => exact ⟨f,by simpa using hf,⟨Homotopy.refl f⟩⟩
  | succ N ih =>
    obtain ⟨g,hg,⟨H⟩⟩ := lower_cochain_map N f (by simpa using hf) hb
    obtain ⟨f',hf',⟨H'⟩⟩ := ih g hg
    exact ⟨f',hf',⟨H.trans H'⟩⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable {Y : C} (R : InjectiveResolution Y) {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem bounded_cochain_coresolution_descends (N : ℕ) (f : K ⟶ R.cochainComplex)
    (hK : ∀ j, (N : ℤ) < j → IsZero (K.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1))) :
    ∃ g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y,
      Nonempty (Homotopy f (g ≫ R.ι')) := by
  obtain ⟨f',hf',H⟩ := cochain_map_supported_nonpositive N f
    (fun j hj => (hK j hj).eq_of_src _ _)
    (coresolution_HomRowBoundaries R K hExt)
  let e0 := R.cochainComplexXIso 0 0 rfl
  let e1 := R.cochainComplexXIso 1 1 rfl
  have hc : f'.f 0 ≫ R.cochainComplex.d 0 1 = 0 := by
    rw [f'.comm, hf' 1 (by omega), comp_zero]
  have hc' : (f'.f 0 ≫ e0.hom) ≫ R.cocomplex.d 0 1 = 0 := by
    have hs := congrArg (fun t => t ≫ e1.hom) hc
    rw [R.cochainComplex_d 0 1 0 1 rfl rfl] at hs
    simpa only [e0,e1,Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using hs
  let s : KernelFork (R.cocomplex.d 0 1) := KernelFork.ofι (f'.f 0 ≫ e0.hom) hc'
  let a : K.X 0 ⟶ Y := R.isLimitKernelFork.lift s
  have ha : a ≫ R.ι.f 0 = f'.f 0 ≫ e0.hom :=
    R.isLimitKernelFork.fac s WalkingParallelPair.zero
  have hd : R.cochainComplex.d (-1) 0 = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1)).eq_of_src _ _
  have hca : ∀ j, (ComplexShape.up ℤ).Rel j 0 → K.d j 0 ≫ a = 0 := by
    intro j hj
    have hj' : j = -1 := by change j+1=0 at hj; omega
    rw [hj']
    apply (cancel_mono (R.ι.f 0)).1
    erw [Category.assoc, ha, ← Category.assoc, ← f'.comm]
    change (f'.f (-1) ≫ R.cochainComplex.d (-1) 0) ≫ e0.hom = 0 ≫ R.ι.f 0
    rw [hd,comp_zero,zero_comp,zero_comp]
  let g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y := mkHomToSingle a hca
  have he : g ≫ R.ι' = f' := by
    apply HomologicalComplex.Hom.ext
    funext j
    by_cases hj : j=0
    · subst j
      simp only [comp_f, g, mkHomToSingle_f, R.ι'_f_zero, Category.assoc,
        Iso.inv_hom_id_assoc]
      erw [← Category.assoc, ha]
      simp only [Category.assoc, e0, Iso.hom_inv_id, Category.comp_id]
    · by_cases hpos : 0<j
      · rw [comp_f, hf' j hpos]
        have hp : R.ι'.f j = 0 :=
          (isZero_single_obj_X (ComplexShape.up ℤ) 0 Y j hj).eq_of_src _ _
        rw [hp,comp_zero]
      · exact (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 j (by omega)).eq_of_tgt _ _
  exact ⟨g, he.symm ▸ H⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]
variable {Y : C} (K : CochainComplex C ℤ)

theorem bounded_orthogonal_derived_descent_dual (R : InjectiveResolution Y) (N : ℕ)
    (hK : ∀ j, (N : ℤ) < j → IsZero (K.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1)))
    (a : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y)) :
    ∃ g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y,
      DerivedCategory.Q.map g = a := by
  obtain ⟨f,hf⟩ := kInjective_chain_representative K R.cochainComplex
    (a ≫ DerivedCategory.Q.map R.ι')
  obtain ⟨g,⟨H⟩⟩ := bounded_cochain_coresolution_descends R N f hK hExt
  refine ⟨g, (cancel_mono (DerivedCategory.Q.map R.ι')).1 ?_⟩
  rw [← Functor.map_comp, ← DerivedCategory.Q_map_eq_of_homotopy C H, hf]

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_FiniteCoinduction
attribute [-instance] _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace LeftDual
variable {M N : ModuleCat Rᵐᵒᵖ}
lemma exact {P : ModuleCat Rᵐᵒᵖ} (f : M ⟶ N) (g : N ⟶ P) (h : Function.Exact f g) : Function.Exact (map (k := k) g) (map (k := k) f) :=
  exact_dual (f.hom.restrictScalars k) (g.hom.restrictScalars k) h
end LeftDual

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def dualResolution {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M) :
    InjectiveResolution (leftDualObj (k := k) M) := by
  let J (n : ℕ) := leftDualObj (k := k) (P.complex.X n)
  let d (n : ℕ) : J n ⟶ J (n+1) := ModuleCat.ofHom (LeftDual.map (P.complex.d (n+1) n))
  let ε : leftDualObj (k := k) M ⟶ J 0 := ModuleCat.ofHom (LeftDual.map (P.π.f 0))
  apply coresolutionOfExact _ J d ε
  · intro n
    exact LeftDual.exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (P.exact_succ n))
  · exact LeftDual.exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 P.exact₀)
  · have hπ := (ModuleCat.epi_iff_surjective (P.π.f 0)).1 inferInstance
    exact LeftDual.map_injective _ hπ
  · intro n
    let : Projective (P.complex.X n) := P.projective n
    let : Module.Projective Rᵐᵒᵖ (P.complex.X n) := inferInstance
    exact Module.injective_object_of_injective_module R (LeftDual (k := k) (P.complex.X n))

lemma dualResolution_above {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) (n : ℕ) (hn : d < n) :
    IsZero ((dualResolution (k := k) P).cocomplex.X n) :=
  leftDualObj_isZero (h n hn)

lemma dualResolution_ext_zero {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) (X : ModuleCat R) (n : ℕ) (hn : d < n) :
    Subsingleton (Abelian.Ext X (leftDualObj (k := k) M) n) := by
  have hz (α : Abelian.Ext X (leftDualObj (k := k) M) n) : α = 0 := by
    obtain ⟨f,hf,rfl⟩ := (dualResolution (k := k) P).extMk_surjective α (n+1) rfl
    have hzero := (dualResolution_above P d h n hn).eq_of_tgt f 0
    subst f
    exact (dualResolution (k := k) P).extMk_zero _ _
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]
variable {M N P Q M' N' : ModuleCat.{0} R}
variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]

def StableEquiv.ofExactSquares
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M N)
    (h : P →ₗ[R] Q) (g : M' →ₗ[R] N')
    (h' : Q →ₗ[R] P) (g' : N' →ₗ[R] M')
    (hu : h.comp i = j.comp e.hom) (hl : delta.comp h = g.comp pi)
    (hu' : h'.comp j = i.comp e.inv) (hl' : pi.comp h' = g'.comp delta) :
    StableEquiv (k := k) M' N' where
  hom := g
  inv := g'
  inv_hom := by
    obtain ⟨a,b⟩ := exact_square_difference_inverse i pi j delta e.hom h g e.inv h' g'
      hu hl hu' hl'
    exact (exact_square_factors_iff i pi hi hex hpi i pi hi hex hpi
      _ _ _ a b).mp e.inv_hom
  hom_inv := by
    obtain ⟨a,b⟩ := exact_square_difference_inverse j delta i pi e.inv h' g' e.hom h g
      hu' hl' hu hl
    exact (exact_square_factors_iff j delta hj hex' hdelta j delta hj hex' hdelta
      _ _ _ a b).mp e.hom_inv

def StableEquiv.down
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M N) : StableEquiv (k := k) M' N' := by
  have H := exists_exact_square_down i pi hi hex hpi j delta hex' e.hom
  have H' := exists_exact_square_down j delta hj hex' hdelta i pi hex e.inv
  exact e.ofExactSquares i pi hi hex hpi j delta hj hex' hdelta
    H.choose H.choose_spec.choose H'.choose H'.choose_spec.choose
    H.choose_spec.choose_spec.1 H.choose_spec.choose_spec.2
    H'.choose_spec.choose_spec.1 H'.choose_spec.choose_spec.2

omit [Module.Injective R R] [Module.Finite R P] [Module.Finite R Q]
  [Module.Projective R Q] in

theorem exists_exact_square_up
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hex : Function.Exact i pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (g : M' →ₗ[R] N') :
    ∃ (h : P →ₗ[R] Q) (f : M →ₗ[R] N),
      h.comp i = j.comp f ∧ delta.comp h = g.comp pi := by
  obtain ⟨h,hh⟩ := Module.projective_lifting_property delta (g.comp pi) hdelta
  have hr (x : M) : (h.comp i) x ∈ LinearMap.range j := by
    apply (hex' _).mp
    have he := LinearMap.congr_fun hh (i x)
    change delta (h (i x)) = g (pi (i x)) at he
    change delta (h (i x)) = 0
    rw [he, (hex _).mpr ⟨x,rfl⟩, map_zero]
  let f := CokerAt.factorThrough j hj (h.comp i) hr
  exact ⟨h,f,(CokerAt.factorThrough_spec j hj (h.comp i) hr).symm,hh⟩

def StableEquiv.up
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M' N') : StableEquiv (k := k) M N := by
  have H := exists_exact_square_up i pi hex j delta hj hex' hdelta e.hom
  have H' := exists_exact_square_up j delta hex' i pi hi hex hpi e.inv
  let h := H.choose
  let f := H.choose_spec.choose
  let h' := H'.choose
  let f' := H'.choose_spec.choose
  have hu : h.comp i = j.comp f := H.choose_spec.choose_spec.1
  have hl : delta.comp h = e.hom.comp pi := H.choose_spec.choose_spec.2
  have hu' : h'.comp j = i.comp f' := H'.choose_spec.choose_spec.1
  have hl' : pi.comp h' = e.inv.comp delta := H'.choose_spec.choose_spec.2
  refine ⟨f,f',?_,?_⟩
  · obtain ⟨a,b⟩ := exact_square_difference_inverse i pi j delta f h e.hom f' h' e.inv
      hu hl hu' hl'
    exact (exact_square_factors_iff i pi hi hex hpi i pi hi hex hpi
      _ _ _ a b).mpr e.inv_hom
  · obtain ⟨a,b⟩ := exact_square_difference_inverse j delta i pi f' h' e.inv f h e.hom
      hu' hl' hu hl
    exact (exact_square_factors_iff j delta hj hex' hdelta j delta hj hex' hdelta
      _ _ _ a b).mpr e.hom_inv
end Tachikawa



namespace Tachikawa
variable {k R M N N' : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
  [Module R M] [Module R N] [Module R N']
  [Module k N] [Module k N'] [IsScalarTower k R N] [IsScalarTower k R N']

def stablePostEquiv (e : N ≃ₗ[R] N') :
    StableHom (k := k) (R := R) (M := M) (N := N) ≃ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := N') :=
  { stablePostcompose e.toLinearMap with
    invFun := stablePostcompose e.symm.toLinearMap
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      change stableClass (k := k) (e.symm.toLinearMap.comp (e.toLinearMap.comp f)) = stableClass (k := k) f
      congr 1
      ext z
      exact e.symm_apply_apply (f z)
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      change stableClass (k := k) (e.toLinearMap.comp (e.symm.toLinearMap.comp f)) = stableClass (k := k) f
      congr 1
      ext z
      exact e.apply_symm_apply (f z) }
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ) (N : ModuleCat R)

lemma stableCoker_subsingleton (j : ℤ) (hz : ∀ f : P.X j ⟶ N, f = 0) :
    Subsingleton (StableHom (k := k) (R := R) (M := CokerAt P j) (N := N)) := by
  have hzero (x : StableHom (k := k) (R := R) (M := CokerAt P j) (N := N)) : x = 0 := by
    obtain ⟨f,rfl⟩ := stableClass_surjective x
    have hf : f = 0 := by
      apply LinearMap.ext
      intro x
      obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
      exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
        (hz (ModuleCat.ofHom (f.comp (CokerAt.π P j))))) y
    rw [hf,map_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

def cokerHomIsolated (j : ℤ) (hz : ∀ f : P.X (j+1) ⟶ N, f = 0) :
    (P.X j ⟶ N) →ₗ[k] (CokerAt P j →ₗ[R] N) where
  toFun f := CokerAt.descend P j f.hom
    (ModuleCat.hom_ext_iff.mp (hz (P.d (j+1) j ≫ f)))
  map_add' f g := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
    rfl

def stableCokerIsolatedEquiv (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j))
    (j : ℤ) (hnext : ∀ f : P.X (j+1) ⟶ N, f = 0)
    (hprev : ∀ f : P.X (j-1) ⟶ N, f = 0) :
    (P.X j ⟶ N) ≃ₗ[k] StableHom (k := k) (R := R) (M := CokerAt P j) (N := N) := by
  let d := cokerHomIsolated (k := k) P N j hnext
  let e := (stableClass (k := k)).comp d
  refine LinearEquiv.ofBijective e ⟨?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hf' : d f ∈ projectiveFactors (k := k) := (stableClass_eq_zero_iff _).mp hf
    obtain ⟨g,hg⟩ := (hP.factors_iff_boundary (k := k) fin proj j f.hom
      (ModuleCat.hom_ext_iff.mp (hnext (P.d (j+1) j ≫ f)))).mp hf'
    have hg0 : g = 0 := ModuleCat.hom_ext_iff.mp (hprev (ModuleCat.ofHom g))
    apply ModuleCat.hom_ext
    rw [hg0, LinearMap.zero_comp] at hg
    exact hg.symm
  · intro x
    obtain ⟨f,rfl⟩ := stableClass_surjective x
    refine ⟨ModuleCat.ofHom (f.comp (CokerAt.π P j)), ?_⟩
    apply congrArg (stableClass (k := k))
    apply LinearMap.ext
    intro y
    obtain ⟨z,rfl⟩ := CokerAt.π_surjective P j y
    rfl

end Tachikawa



namespace Tachikawa.CompleteHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ)
  (hP : TotallyAcyclic P) (fin : ∀ j, Module.Finite R (P.X j))
  (proj : ∀ j, Module.Projective R (P.X j))

variable {X : ModuleCat.{0} R} (e : CokerAt P 0 ≃ₗ[R] X)

def zeroEquiv (N : ModuleCat.{0} R) :
    VectorSplit.H (completeHom (k := k) P N) 0 ≃ₗ[k] StableMap (k := k) X N :=
  (equiv P N hP fin proj 0).trans ((StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt P 0)) (N := X) e).pre N)

end Tachikawa.CompleteHom

end

end OAI
end


