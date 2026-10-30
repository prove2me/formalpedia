-- Prove2me | Definitions.Def_OAIQ116Ta000
-- name    : OAIQ116Ta000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:32:26.618267+00:00
-- url     : https://prove2.me/theorems/00c72209-6c90-47bf-a06c-db26a3c9e80d
-- title:
--   Definitions bundle OAIQ116Ta000 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 219 declarations of OpenAI's Lean: 83 definitions, 1 inductive type or structure, 49 instances and 86 theorems. The definitions and types are `OAI.Tachikawa.AlgebraInduction.Bimod`, `OAI.Tachikawa.AlgebraInduction.extend`, `OAI.Tachikawa.AlgebraInduction.functor`, `OAI.Tachikawa.AlgebraInduction.homEquiv`, `OAI.Tachikawa.AlgebraInduction.res`, `OAI.Tachikawa.AlgebraInduction.underlyingEquiv`, `OAI.Tachikawa.AlgebraInduction.unit`, `OAI.Tachikawa.AlgebraInduction.unitLinear`, `OAI.Tachikawa.BalancedTensor.T`, `OAI.Tachikawa.BalancedTensor.freeEval`, `OAI.Tachikawa.BalancedTensor.functor`, `OAI.Tachikawa.BalancedTensor.leftUnit`, `OAI.Tachikawa.BalancedTensor.lift`, `OAI.Tachikawa.BalancedTensor.liftGround`, `OAI.Tachikawa.BalancedTensor.mapLeft`, `OAI.Tachikawa.BalancedTensor.mapRight`, `OAI.Tachikawa.BalancedTensor.mapRightBilinear`, `OAI.Tachikawa.BalancedTensor.mk`, `OAI.Tachikawa.BalancedTensor.relations`, `OAI.Tachikawa.BalancedTensor.restrictEquiv`, `OAI.Tachikawa.BalancedTensor.rightAction`, `OAI.Tachikawa.BalancedTensor.rightFreeEval`, `OAI.Tachikawa.BalancedTensor.rightUnit`, `OAI.Tachikawa.BimoduleTensorHom.uncurryLinear`, `OAI.Tachikawa.C.reverseCoeff`, `OAI.Tachikawa.DualBimodule`, `OAI.Tachikawa.DualBimodule.coinduce`, `OAI.Tachikawa.Enveloping.Alg`, `OAI.Tachikawa.Enveloping.Obj`, `OAI.Tachikawa.Enveloping.action`, `OAI.Tachikawa.Enveloping.evalMap`, `OAI.Tachikawa.Enveloping.evalObj`, `OAI.Tachikawa.Enveloping.evalType`, `OAI.Tachikawa.Enveloping.leftMap`, `OAI.Tachikawa.Enveloping.ofBimodule`, `OAI.Tachikawa.Enveloping.rightMap`, `OAI.Tachikawa.HomBimodule.Base`, `OAI.Tachikawa.HomBimodule.obj`, `OAI.Tachikawa.HomBimodule.rightAction`, `OAI.Tachikawa.Nakayama` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: [`Tachikawa_Bimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Bimodule.lean), [`Tachikawa_CompleteTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/CompleteTensor.lean), [`Tachikawa_Nakayama`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Nakayama.lean), [`Tachikawa_OuterTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/OuterTensor.lean), [`Tachikawa_ReverseResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/ReverseResolution.lean), [`Tachikawa_StableDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/StableDuality.lean), [`Tachikawa_Symmetry`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Symmetry.lean), [`Tachikawa_Tensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Tensor.lean), [`Tachikawa_Twisting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Twisting.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta003`, `OAIQ116Ta004` and `OAIQ116Ta005`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ116_Tach.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
namespace Tachikawa

def DualBimodule (k R : Type*) [Field k] [Ring R] [Algebra k R] := Module.Dual k R

namespace DualBimodule
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

instance instFunLike : FunLike (DualBimodule k R) R k := inferInstanceAs (FunLike (Module.Dual k R) R k)
instance instLinearMapClass : LinearMapClass (DualBimodule k R) k R k :=
  inferInstanceAs (LinearMapClass (Module.Dual k R) k R k)

instance instAddCommGroup : AddCommGroup (DualBimodule k R) := inferInstanceAs (AddCommGroup (Module.Dual k R))
instance instModule : Module k (DualBimodule k R) := inferInstanceAs (Module k (Module.Dual k R))

@[ext] lemma ext {φ ψ : DualBimodule k R} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h

@[simp] lemma add_apply (φ ψ : DualBimodule k R) (x : R) : (φ + ψ) x = φ x + ψ x := rfl
@[simp] lemma zero_apply (x : R) : (0 : DualBimodule k R) x = 0 := rfl
@[simp] lemma smul_apply (c : k) (φ : DualBimodule k R) (x : R) : (c • φ) x = c * φ x := rfl

instance leftModule : Module R (DualBimodule k R) where
  smul a φ := φ.comp (LinearMap.mulRight k a)
  one_smul φ := by ext x; change φ (x * 1) = φ x; simp
  mul_smul a b φ := by ext x; change φ (x * (a * b)) = φ ((x * a) * b); simp [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by ext x; change φ (x * (a + b)) = φ (x * a) + φ (x * b); simp [mul_add]
  zero_smul φ := by ext x; change φ (x * 0) = 0; simp

@[simp] lemma left_apply (a : R) (φ : DualBimodule k R) (x : R) : (a • φ) x = φ (x * a) := rfl

instance rightModule : Module Rᵐᵒᵖ (DualBimodule k R) where
  smul a φ := φ.comp (LinearMap.mulLeft k a.unop)
  one_smul φ := by ext x; change φ (1 * x) = φ x; simp
  mul_smul a b φ := by
    ext x
    change φ ((b.unop * a.unop) * x) = φ (b.unop * (a.unop * x))
    simp [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by
    ext x
    change φ ((a.unop + b.unop) * x) = φ (a.unop * x) + φ (b.unop * x)
    simp [add_mul]
  zero_smul φ := by ext x; change φ (0 * x) = 0; simp

@[simp] lemma right_apply (a : Rᵐᵒᵖ) (φ : DualBimodule k R) (x : R) :
    (a • φ) x = φ (a.unop * x) := rfl

instance instIsScalarTower : IsScalarTower k R (DualBimodule k R) where
  smul_assoc a b φ := by
    ext x
    simp [Algebra.mul_smul_comm]

instance instFiniteDimensional [FiniteDimensional k R] : FiniteDimensional k (DualBimodule k R) :=
  inferInstanceAs (FiniteDimensional k (Module.Dual k R))

end DualBimodule
end Tachikawa



namespace Tachikawa.DualBimodule
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

def coinduce {Y : Type*} [AddCommGroup Y] [Module R Y] [Module k Y]
    [IsScalarTower k R Y] (g : Y →ₗ[k] k) : Y →ₗ[R] DualBimodule k R where
  toFun y :=
    { toFun := fun r => g (r • y)
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun c r => by simp [smul_assoc] }
  map_add' a b := by
    ext r
    change g (r • (a + b)) = g (r • a) + g (r • b)
    simp [smul_add]
  map_smul' a y := by
    ext r
    change g (r • (a • y)) = g ((r * a) • y)
    rw [mul_smul]

@[simp] lemma coinduce_apply {Y : Type*} [AddCommGroup Y] [Module R Y] [Module k Y]
    [IsScalarTower k R Y] (g : Y →ₗ[k] k) (y : Y) (r : R) :
    coinduce g y r = g (r • y) := rfl

end Tachikawa.DualBimodule



namespace Tachikawa

abbrev TrivialExtension (k R : Type*) [Field k] [Ring R] [Algebra k R] :=
  TrivSqZeroExt R (DualBimodule k R)

namespace TrivialExtension
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

def trace : TrivialExtension k R →ₗ[k] k where
  toFun a := a.snd 1
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] lemma trace_apply (a : TrivialExtension k R) : trace a = a.snd 1 := rfl

end TrivialExtension



variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

structure SymmetrizingForm where
  linear : R →ₗ[k] k
  comm : ∀ a b, linear (a * b) = linear (b * a)
  nondegenerate : ∀ a, (∀ b, linear (a * b) = 0) → a = 0

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))

def toDual : R →ₗ[R] DualBimodule k R := DualBimodule.coinduce t.linear

@[simp] lemma toDual_apply (a x : R) : t.toDual a x = t.linear (x * a) := rfl

lemma toDual_injective : Function.Injective t.toDual := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  apply t.nondegenerate a
  intro b
  rw [t.comm]
  exact congrArg (fun f : DualBimodule k R => f b) ha

def dualEquiv [FiniteDimensional k R] : R ≃ₗ[R] DualBimodule k R :=
  LinearEquiv.ofBijective t.toDual ⟨t.toDual_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (show Module.finrank k R = Module.finrank k (DualBimodule k R) from
        (Subspace.dual_finrank_eq).symm) (f := t.toDual.restrictScalars k)).mp
          t.toDual_injective⟩

end SymmetrizingForm

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N L : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module R M] [Module R N] [Module R L]
  [Module k M] [Module k N] [Module k L]
  [IsScalarTower k R M] [IsScalarTower k R N] [IsScalarTower k R L]

def projectiveFactors : Submodule k (M →ₗ[R] N) where
  carrier f := ∃ P : ModuleCat.{0} R, Module.Finite R P ∧ Module.Projective R P ∧
    ∃ i : M →ₗ[R] P, ∃ p : P →ₗ[R] N, p.comp i = f
  zero_mem' := ⟨ModuleCat.of R R, inferInstance, inferInstance, 0, 0, by simp⟩
  add_mem' {f g} hf hg := by
    obtain ⟨P, hPf, hPp, i, p, rfl⟩ := hf
    obtain ⟨Q, hQf, hQp, j, q, rfl⟩ := hg
    let := hPf
    let := hPp
    let := hQf
    let := hQp
    refine ⟨ModuleCat.of R (P × Q), inferInstance, inferInstance,
      i.prod j, p.coprod q, ?_⟩
    ext x
    rfl
  smul_mem' c f hf := by
    obtain ⟨P, hPf, hPp, i, p, rfl⟩ := hf
    exact ⟨P, hPf, hPp, i, c • p, by ext x; rfl⟩

omit [Module k M] [Module k L] [IsScalarTower k R M] [IsScalarTower k R L] in
lemma projectiveFactors_precomp {f : M →ₗ[R] N}
    (hf : f ∈ projectiveFactors (k := k)) (g : L →ₗ[R] M) :
    f.comp g ∈ projectiveFactors (k := k) := by
  obtain ⟨P, hPf, hPp, i, p, rfl⟩ := hf
  exact ⟨P, hPf, hPp, i.comp g, p, rfl⟩

omit [Module k M] [IsScalarTower k R M] in
lemma projectiveFactors_postcomp {f : M →ₗ[R] N}
    (hf : f ∈ projectiveFactors (k := k)) (g : N →ₗ[R] L) :
    g.comp f ∈ projectiveFactors (k := k) := by
  obtain ⟨P, hPf, hPp, i, p, rfl⟩ := hf
  exact ⟨P, hPf, hPp, i, g.comp p, rfl⟩

def StableHom := (M →ₗ[R] N) ⧸ projectiveFactors (k := k)

instance instAddCommGroupStableHom : AddCommGroup (StableHom (k := k) (R := R) (M := M) (N := N)) :=
  inferInstanceAs (AddCommGroup ((M →ₗ[R] N) ⧸ projectiveFactors (k := k)))
instance instModuleStableHom : Module k (StableHom (k := k) (R := R) (M := M) (N := N)) :=
  inferInstanceAs (Module k ((M →ₗ[R] N) ⧸ projectiveFactors (k := k)))

def stableClass : (M →ₗ[R] N) →ₗ[k] StableHom (k := k) (R := R) (M := M) (N := N) :=
  (projectiveFactors (k := k)).mkQ

omit [Module k M] [IsScalarTower k R M] in
lemma stableClass_eq_zero_iff (f : M →ₗ[R] N) :
    stableClass (k := k) f = 0 ↔ f ∈ projectiveFactors (k := k) :=
  Submodule.Quotient.mk_eq_zero _

def stablePostcompose (g : N →ₗ[R] L) :
    StableHom (k := k) (R := R) (M := M) (N := N) →ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := L) :=
  (projectiveFactors (k := k)).mapQ (projectiveFactors (k := k))
    { toFun := fun f => g.comp f
      map_add' := fun f f' => by ext x; simp
      map_smul' := fun c f => by ext x; simp }
    (fun _ hf => projectiveFactors_postcomp hf g)

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma stablePostcompose_class (g : N →ₗ[R] L) (f : M →ₗ[R] N) :
    stablePostcompose (k := k) g (stableClass (k := k) f) =
      stableClass (k := k) (g.comp f) := rfl

omit [Module k M] [IsScalarTower k R M] in
lemma stableClass_surjective : Function.Surjective
    (stableClass (k := k) (R := R) (M := M) (N := N)) :=
  Submodule.mkQ_surjective _

def stablePostcomposeLinear : (N →ₗ[R] L) →ₗ[k]
    (StableHom (k := k) (R := R) (M := M) (N := N) →ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := L)) where
  toFun := stablePostcompose
  map_add' g g' := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change stableClass (k := k) ((g+g').comp f) =
      stableClass (k := k) (g.comp f) + stableClass (k := k) (g'.comp f)
    rw [LinearMap.add_comp, map_add]
  map_smul' c g := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change stableClass (k := k) ((c • g).comp f) = c • stableClass (k := k) (g.comp f)
    rw [LinearMap.smul_comp, map_smul]

def stableComp : StableHom (k := k) (R := R) (M := N) (N := L) →ₗ[k]
    (StableHom (k := k) (R := R) (M := M) (N := N) →ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := L)) :=
  (projectiveFactors (k := k)).liftQ stablePostcomposeLinear (by
    intro g hg
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change stableClass (k := k) (g.comp f) = 0
    exact (stableClass_eq_zero_iff _).mpr (projectiveFactors_precomp hg f))

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma stableComp_class (g : N →ₗ[R] L) (f : M →ₗ[R] N) :
    stableComp (k := k) (stableClass (k := k) g) (stableClass (k := k) f) =
      stableClass (k := k) (g.comp f) := rfl

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {N : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R)) [FiniteDimensional k R]

def homDual : (N →ₗ[R] R) →ₗ[k] Module.Dual k N where
  toFun f := t.linear.comp (f.restrictScalars k)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [FiniteDimensional k R] in
@[simp] lemma homDual_apply (f : N →ₗ[R] R) (x : N) :
    t.homDual f x = t.linear (f x) := rfl

lemma homDual_bijective : Function.Bijective (t.homDual (N := N)) := by
  constructor
  · intro f g h
    ext x
    apply t.toDual_injective
    ext r
    change t.linear (r * f x) = t.linear (r * g x)
    have hr := LinearMap.congr_fun h (r • x)
    simpa only [homDual_apply, map_smul, smul_eq_mul] using hr
  · intro l
    refine ⟨t.dualEquiv.symm.toLinearMap.comp (DualBimodule.coinduce l), ?_⟩
    ext x
    have h := congrArg (fun z : DualBimodule k R => z 1)
      (t.dualEquiv.apply_symm_apply (DualBimodule.coinduce l x))
    change t.linear (1 * t.dualEquiv.symm (DualBimodule.coinduce l x)) = l (1 • x) at h
    simpa only [one_mul, one_smul, homDual_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe] using h

def homDualEquiv : (N →ₗ[R] R) ≃ₗ[k] Module.Dual k N :=
  LinearEquiv.ofBijective t.homDual t.homDual_bijective

@[simp] lemma homDualEquiv_apply (f : N →ₗ[R] R) (x : N) :
    t.homDualEquiv f x = t.linear (f x) := rfl

end SymmetrizingForm

def homPiEquiv (ι : Type) : (N →ₗ[R] (ι → R)) ≃ₗ[k] (ι → N →ₗ[R] R) where
  toFun f i := (LinearMap.proj i).comp f
  invFun := LinearMap.pi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R)) [FiniteDimensional k R]
variable (ι : Type) [Fintype ι] [DecidableEq ι]

def freeHomDual : (N →ₗ[R] (ι → R)) ≃ₗ[k]
    Module.Dual k ((ι → R) →ₗ[R] N) :=
  (homPiEquiv ι).trans ((LinearEquiv.piCongrRight (fun _ : ι => t.homDualEquiv)).trans
    ((LinearMap.lsum k (fun _ : ι => N) k).trans
      (LinearEquiv.piRing R N ι k).dualMap))

@[simp] lemma freeHomDual_apply (g : N →ₗ[R] (ι → R)) (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι g f = ∑ i, t.linear (g (f (Pi.single i 1)) i) := by
  simp [freeHomDual, homPiEquiv, LinearMap.lsum_apply]
  rfl

end SymmetrizingForm
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped TensorProduct
open TensorProduct
namespace Tachikawa

namespace BalancedTensor
variable {k R S M N P : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N]

def relations : Submodule S (M ⊗[k] N) :=
  Submodule.span S {x | ∃ r : R, ∃ m : M, ∃ n : N,
    x = (MulOpposite.op r • m) ⊗ₜ[k] n - m ⊗ₜ[k] (r • n)}

abbrev T := (M ⊗[k] N) ⧸ relations (k := k) (R := R) (S := S)

def mk : M →ₗ[S] N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N) :=
  TensorProduct.AlgebraTensorModule.curry
    (relations (k := k) (R := R) (S := S) (M := M) (N := N)).mkQ

lemma balance (r : R) (m : M) (n : N) :
    mk (k := k) (R := R) (S := S) (MulOpposite.op r • m) n = mk m (r • n) := by
  apply sub_eq_zero.mp
  change (relations (k := k) (R := R) (S := S)).mkQ _ -
    (relations (k := k) (R := R) (S := S)).mkQ _ = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨r,m,n,rfl⟩)

variable [AddCommGroup P] [Module k P] [Module S P] [IsScalarTower k S P]

def lift (f : M →ₗ[S] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n)) :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[S] P :=
  (relations (k := k) (R := R) (S := S)).liftQ
    (TensorProduct.AlgebraTensorModule.lift f) (by
      apply Submodule.span_le.mpr
      rintro x ⟨r,m,n,rfl⟩
      change TensorProduct.AlgebraTensorModule.lift f _ = 0
      simp only [map_sub, TensorProduct.AlgebraTensorModule.lift_tmul]
      exact sub_eq_zero.mpr (hf r m n))

@[simp] lemma lift_mk (f : M →ₗ[S] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n)) (m : M) (n : N) :
    lift f hf (mk m n) = f m n := rfl

@[elab_as_elim] theorem induction_on
    {p : T (k := k) (R := R) (S := S) (M := M) (N := N) → Prop}
    (x : T (k := k) (R := R) (S := S) (M := M) (N := N))
    (h0 : p 0) (ht : ∀ m n, p (mk m n))
    (ha : ∀ x y, p x → p y → p (x+y)) : p x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact h0
  clear hx
  obtain ⟨z, rfl⟩ := (relations (k := k) (R := R) (S := S)).mkQ_surjective x
  induction z using OAI.tensorInductionOn with
  | tmul m n => exact ht m n
  | add z z' hz hz' => exact ha _ _ hz hz'

omit [Module k P] [IsScalarTower k S P] in
@[ext] theorem hom_ext {f g : T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[S] P}
    (h : ∀ m n, f (mk m n) = g (mk m n)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using induction_on with
  | h0 => simp
  | ht m n => exact h m n
  | ha x y hx hy => simp only [map_add, hx, hy]

end BalancedTensor
end Tachikawa

end


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

def mapRightBilinear (f : N →ₗ[R] N') :
    M →ₗ[S] N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N') :=
  (mk (k := k) (R := R) (S := S)).compl₂ (f.restrictScalars k)

lemma mapRightBilinear_balanced (f : N →ₗ[R] N') (r : R) (m : M) (n : N) :
    mapRightBilinear (k := k) (S := S) f (MulOpposite.op r • m) n = mapRightBilinear (k := k) (S := S) f m (r • n) := by
  change mk (MulOpposite.op r • m) (f n) = mk m (f (r • n))
  rw [f.map_smul]
  exact balance r m (f n)

def mapRight (f : N →ₗ[R] N') :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[S]
      T (k := k) (R := R) (S := S) (M := M) (N := N') :=
  lift (mapRightBilinear (k := k) (S := S) f) (mapRightBilinear_balanced f)

@[simp] lemma mapRight_mk (f : N →ₗ[R] N') (m : M) (n : N) :
    mapRight (k := k) (S := S) (M := M) f (mk m n) = mk (k := k) (R := R) (S := S) m (f n) := rfl

lemma mapRight_id : mapRight (k := k) (S := S) (M := M) (LinearMap.id : N →ₗ[R] N) =
    LinearMap.id := by
  apply hom_ext
  intro m n
  rfl

lemma mapRight_comp (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') :
    mapRight (k := k) (S := S) (M := M) (g.comp f) =
      (mapRight (k := k) (S := S) g).comp (mapRight (k := k) (S := S) f) := by
  apply hom_ext
  intro m n
  rfl

lemma mapRight_add (f g : N →ₗ[R] N') :
    mapRight (k := k) (S := S) (M := M) (f+g) = mapRight (k := k) (S := S) f + mapRight (k := k) (S := S) g := by
  apply hom_ext
  intro m n
  simp

lemma mapRight_zero : mapRight (k := k) (S := S) (M := M) (0 : N →ₗ[R] N') = 0 := by
  apply hom_ext
  intro m n
  simp

variable [SMulCommClass S Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]

def rightUnit : T (k := k) (R := R) (S := S) (M := M) (N := R) →ₗ[S] M :=
  lift
    { toFun := fun m =>
        { toFun := fun r => MulOpposite.op r • m
          map_add' := by intro a b; rw [MulOpposite.op_add, add_smul]
          map_smul' := by
            intro c r
            rw [MulOpposite.op_smul, smul_assoc]
            rfl }
      map_add' := by intro m n; ext r; exact smul_add _ _ _
      map_smul' := by intro s m; ext r; exact (smul_comm s (MulOpposite.op r) m).symm }
    (fun r m a => by
      change MulOpposite.op a • MulOpposite.op r • m = MulOpposite.op (r*a) • m
      rw [← mul_smul, ← MulOpposite.op_mul])

@[simp] lemma rightUnit_mk (m : M) (r : R) : rightUnit (k := k) (S := S) (mk m r) =
    MulOpposite.op r • m := rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M M' M'' N : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M] [IsScalarTower k S M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M'] [IsScalarTower k S M']
  [AddCommGroup M''] [Module k M''] [Module S M''] [Module Rᵐᵒᵖ M''] [IsScalarTower k S M'']
  [AddCommGroup N] [Module k N] [Module R N]

def mapLeft (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[S]
      T (k := k) (R := R) (S := S) (M := M') (N := N) :=
  lift ((mk (k := k) (R := R) (S := S)).comp f) (fun r m n => by
    change mk (f (MulOpposite.op r • m)) n = mk (f m) (r • n)
    rw [hf]
    exact balance r (f m) n)

@[simp] lemma mapLeft_mk (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) (m : M) (n : N) :
    mapLeft (k := k) (N := N) f hf (mk m n) = mk (f m) n := rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M N : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module R N]

lemma fieldRelations_smul_mem (s : S) {x : M ⊗[k] N}
    (hx : x ∈ relations (k := k) (R := R) (S := k)) :
    s • x ∈ relations (k := k) (R := R) (S := k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r,m,n,rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨r,s • m,n,?_⟩
    simp only [smul_sub, TensorProduct.smul_tmul', smul_comm s (MulOpposite.op r)]
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [smul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [smul_comm s c]
    exact Submodule.smul_mem _ c ih

lemma relations_restrictScalars :
    (relations (k := k) (R := R) (S := S) (M := M) (N := N)).restrictScalars k =
      relations (k := k) (R := R) (S := k) := by
  apply le_antisymm
  · let V : Submodule S (M ⊗[k] N) :=
      { (relations (k := k) (R := R) (S := k)).toAddSubmonoid with
        smul_mem' := fun s x hx => fieldRelations_smul_mem s hx }
    have h : relations (k := k) (R := R) (S := S) ≤ V := by
      apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span hx
    exact h
  · apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span hx

def restrictEquiv :
    T (k := k) (R := R) (S := S) (M := M) (N := N) ≃ₗ[k]
      T (k := k) (R := R) (S := k) (M := M) (N := N) :=
  (Submodule.Quotient.restrictScalarsEquiv k (relations (k := k) (R := R)
    (S := S) (M := M) (N := N))).symm.trans
      (Submodule.quotEquivOfEq _ _ relations_restrictScalars)

@[simp] lemma restrictEquiv_mk (m : M) (n : N) :
    restrictEquiv (mk (k := k) (R := R) (S := S) m n) =
      mk (k := k) (R := R) (S := k) m n := rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R N N' : Type*} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']

def leftUnit : T (k := k) (R := R) (S := k) (M := R) (N := N) →ₗ[k] N :=
  lift (Algebra.lsmul k k N).toLinearMap
    (fun r m n => by
      change (m*r) • n = m • r • n
      exact mul_smul m r n)

@[simp] lemma leftUnit_mk (r : R) (n : N) : leftUnit (k := k) (mk (k := k) (R := R) (S := k) r n) = r • n := rfl

variable (ι : Type*) [Fintype ι]

def freeEval : T (k := k) (R := R) (S := k) (M := ι → R) (N := N) →ₗ[k] (ι → N) :=
  lift
    { toFun m :=
        { toFun n i := m i • n
          map_add' n n' := by ext i; exact smul_add _ _ _
          map_smul' a n := by ext i; exact smul_comm _ _ _ }
      map_add' m m' := by ext n i; exact add_smul _ _ _
      map_smul' a m := by ext n i; exact smul_assoc a (m i) n }
    (fun r m n => by ext i; exact mul_smul (m i) r n)

omit [Fintype ι] in
@[simp] lemma freeEval_mk (m : ι → R) (n : N) (i : ι) :
    freeEval (k := k) (R := R) ι (mk (k := k) (R := R) (S := k) m n) i = m i • n := rfl

end Tachikawa.BalancedTensor

end


noncomputable section



namespace Tachikawa.BalancedTensor
variable {k R S M : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  (ι : Type) [Fintype ι]

def rightFreeEval : T (k := k) (R := R) (S := S) (M := M) (N := ι → R) →ₗ[S] (ι → M) :=
  LinearMap.pi fun i => (rightUnit (k := k) (R := R) (S := S)).comp
    (mapRight (k := k) (S := S) (LinearMap.proj i))

omit [Fintype ι] in
@[simp] lemma rightFreeEval_mk (m : M) (x : ι → R) (i : ι) :
    rightFreeEval ι (mk (k := k) (R := R) (S := S) m x) i = MulOpposite.op (x i) • m := rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S M : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M] [IsScalarTower k S M]

def functor : ModuleCat R ⥤ ModuleCat S where
  obj N := ModuleCat.of S (T (k := k) (R := R) (S := S) (M := M) (N := N))
  map f := ModuleCat.ofHom (mapRight f.hom)
  map_id _ := ModuleCat.hom_ext mapRight_id
  map_comp _ _ := ModuleCat.hom_ext (mapRight_comp _ _)

end Tachikawa.BalancedTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def Obj (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) := M ⊗[k] N

instance instAddCommGroupObj (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) : AddCommGroup (Obj k A B M N) :=
  inferInstanceAs (AddCommGroup (M ⊗[k] N))
instance instModuleObj (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) : Module k (Obj k A B M N) :=
  inferInstanceAs (Module k (M ⊗[k] N))

def action (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    A ⊗[k] B →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift
    ((Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M))
    ((Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N)) (by
      intro a b
      change ((Algebra.lsmul k k M a).rTensor N).comp ((Algebra.lsmul k k N b).lTensor M) =
        ((Algebra.lsmul k k N b).lTensor M).comp ((Algebra.lsmul k k M a).rTensor N)
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])

instance instModuleTensorProductObj (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) : Module (A ⊗[k] B) (Obj k A B M N) :=
  show Module (A ⊗[k] B) (M ⊗[k] N) from
  Module.compHom _ (action k A B M N).toRingHom
instance instIsScalarTowerTensorProductObj (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    IsScalarTower k (A ⊗[k] B) (Obj k A B M N) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change (action k A B M N (algebraMap k (A ⊗[k] B) r)) x = r • x
    rw [AlgHom.commutes]
    rfl

@[simp] lemma tmul_smul_tmul (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    (a : A) (b : B) (x : M) (y : N) :
    (a ⊗ₜ[k] b) • (show Obj k A B M N from x ⊗ₜ[k] y) = (a • x) ⊗ₜ[k] (b • y) := rfl

variable {k A B}
lemma map_action {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') (r : A ⊗[k] B) :
    (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)).comp
      (action k A B M N r) =
    (action k A B M' N' r).comp
      (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)) := by
  induction r using OAI.tensorInductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    change (f.hom (a • x)) ⊗ₜ[k] (g.hom (b • y)) = (a • f.hom x) ⊗ₜ[k] (b • g.hom y)
    rw [map_smul, map_smul]
  | add r s hr hs =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hr, hs]

def map {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B} (f : M ⟶ M') (g : N ⟶ N') :
    Obj k A B M N →ₗ[A ⊗[k] B] Obj k A B M' N' where
  toFun := TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)
  map_add' := map_add _
  map_smul' r z := LinearMap.congr_fun (map_action f g r) z

@[simp] lemma map_tmul {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') (x : M) (y : N) :
    map (k := k) f g (x ⊗ₜ[k] y) = f x ⊗ₜ[k] g y := rfl

lemma map_comp {M M' M'' : ModuleCat.{u} A} {N N' N'' : ModuleCat.{u} B}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    (map (k := k) f' g').comp (map f g) = map (f ≫ f') (g ≫ g') := by
  apply LinearMap.restrictScalars_injective k
  change (TensorProduct.map (f'.hom.restrictScalars k) (g'.hom.restrictScalars k)).comp
    (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)) = _
  exact (TensorProduct.map_comp _ _ _ _).symm

lemma map_id (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    map (k := k) (𝟙 M) (𝟙 N) = LinearMap.id := by
  apply LinearMap.restrictScalars_injective k
  change TensorProduct.map (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N) = LinearMap.id
  exact TensorProduct.map_id

variable (k A B)
def bifunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} B ⥤ ModuleCat.{u} (A ⊗[k] B) where
  obj M :=
    { obj := fun N => ModuleCat.of _ (Obj k A B M N)
      map := fun g => ModuleCat.ofHom (map (𝟙 M) g)
      map_id := fun N => ModuleCat.hom_ext (map_id M N)
      map_comp := fun g g' => by
        apply ModuleCat.hom_ext
        simpa only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, Category.id_comp] using
          (map_comp (k := k) (𝟙 M) (𝟙 M) g g').symm }
  map {M M'} f :=
    { app := fun N => ModuleCat.ofHom (map f (𝟙 N))
      naturality := fun N N' g => by
        apply ModuleCat.hom_ext
        simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, map_comp,
          Category.id_comp, Category.comp_id] }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact ModuleCat.hom_ext (map_id (k := k) M N)
  map_comp f f' := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    change map (f ≫ f') (𝟙 N) = (map f' (𝟙 N)).comp (map f (𝟙 N))
    simpa only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, Category.id_comp] using
      (map_comp (k := k) f f' (𝟙 N) (𝟙 N)).symm

end Tachikawa.OuterTensor



namespace Tachikawa
open scoped TensorProduct
namespace SymmetrizingForm
variable {k R S : Type*} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))

def tensorTrace : R ⊗[k] S →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp (TensorProduct.map t.linear u.linear)

@[simp] lemma tensorTrace_tmul (r : R) (s : S) :
    tensorTrace t u (r ⊗ₜ[k] s) = t.linear r * u.linear s := rfl

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace Enveloping
variable (k R S : Type) [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
abbrev Alg := R ⊗[k] Sᵐᵒᵖ

variable {k R S}

def Obj (M : ModuleCat (Alg k R S)) : Type := M
instance instAddCommGroupObj (M : ModuleCat (Alg k R S)) : AddCommGroup (Obj M) :=
  inferInstanceAs (AddCommGroup M)
instance instModuleAlgObj (M : ModuleCat (Alg k R S)) : Module (Alg k R S) (Obj M) :=
  inferInstanceAs (Module (Alg k R S) M)
instance instModuleObj (M : ModuleCat (Alg k R S)) : Module k (Obj M) :=
  inferInstanceAs (Module k M)
instance instIsScalarTowerAlgObj (M : ModuleCat (Alg k R S)) : IsScalarTower k (Alg k R S) (Obj M) :=
  inferInstanceAs (IsScalarTower k (Alg k R S) M)
instance instModuleObj_1 (M : ModuleCat (Alg k R S)) : Module R (Obj M) :=
  Module.compHom (Obj M) (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] Sᵐᵒᵖ).toRingHom
instance instModuleMulOppositeObj (M : ModuleCat (Alg k R S)) : Module Sᵐᵒᵖ (Obj M) :=
  Module.compHom (Obj M) (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] R ⊗[k] Sᵐᵒᵖ).toRingHom
instance instIsScalarTowerObj (M : ModuleCat (Alg k R S)) : IsScalarTower k R (Obj M) :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := R) (M := Obj M) fun r x => by
    change ((Algebra.TensorProduct.includeLeft : R →ₐ[k] Alg k R S) (algebraMap k R r)) • (show M from x) = r • x
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_smul (Alg k R S) r x
instance instIsScalarTowerMulOppositeObj (M : ModuleCat (Alg k R S)) : IsScalarTower k Sᵐᵒᵖ (Obj M) :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := Sᵐᵒᵖ) (M := Obj M) fun r x => by
    change ((Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] Alg k R S) (algebraMap k Sᵐᵒᵖ r)) • (show M from x) = r • x
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_smul (Alg k R S) r x
instance instSMulCommClassMulOppositeObj (M : ModuleCat (Alg k R S)) : SMulCommClass R Sᵐᵒᵖ (Obj M) where
  smul_comm r s m := by
    change ((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) : Alg k R S) • (((1:R) ⊗ₜ[k] s) • m) =
      ((1:R) ⊗ₜ[k] s) • ((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) • m)
    rw [← mul_smul, ← mul_smul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def leftMap {M N : ModuleCat (Alg k R S)} (f : M ⟶ N) : Obj M →ₗ[R] Obj N where
  toFun := f
  map_add' := f.hom.map_add
  map_smul' r x := f.hom.map_smul ((Algebra.TensorProduct.includeLeft : R →ₐ[k] Alg k R S) r) x

def rightMap {M N : ModuleCat (Alg k R S)} (f : M ⟶ N) : Obj M →ₗ[Sᵐᵒᵖ] Obj N where
  toFun := f
  map_add' := f.hom.map_add
  map_smul' s x := f.hom.map_smul ((Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] Alg k R S) s) x

@[simp] lemma leftMap_apply {M N : ModuleCat (Alg k R S)} (f : M ⟶ N) (x : Obj M) :
    leftMap f x = f x := rfl
@[simp] lemma rightMap_apply {M N : ModuleCat (Alg k R S)} (f : M ⟶ N) (x : Obj M) :
    rightMap f x = f x := rfl

end Enveloping

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (M : Type) [AddCommGroup M] [Module k M] [Module R M] [Module Sᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]

def action : Alg k R S →ₐ[k] Module.End k M :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k M) (Algebra.lsmul k k M)
    (fun r s => by
      ext x
      exact smul_comm r s x)

def ofBimodule : ModuleCat (Alg k R S) :=
  letI := Module.compHom M (action (k := k) (R := R) (S := S) M).toRingHom
  ModuleCat.of (Alg k R S) M

end Enveloping

namespace BalancedTensor
variable {k R S U M N : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [Module Uᵐᵒᵖ N]
  [IsScalarTower k R N] [IsScalarTower k Uᵐᵒᵖ N] [SMulCommClass R Uᵐᵒᵖ N]

local instance instSMulCommClassMulOpposite_solutions : SMulCommClass Uᵐᵒᵖ R N := SMulCommClass.symm R Uᵐᵒᵖ N

def rightAction : Uᵐᵒᵖ →+* Module.End S (T (k := k) (R := R) (S := S) (M := M) (N := N)) where
  toFun u := mapRight ((Algebra.lsmul k R N) u)
  map_one' := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) 1) = LinearMap.id
    rw [map_one]
    exact mapRight_id
  map_mul' u v := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) (u*v)) = _
    rw [map_mul]
    exact mapRight_comp _ _
  map_zero' := by rw [map_zero]; exact mapRight_zero
  map_add' u v := by rw [map_add]; exact mapRight_add _ _

instance rightModule : Module Uᵐᵒᵖ (T (k := k) (R := R) (S := S) (M := M) (N := N)) :=
  Module.compHom _ (rightAction (k := k) (R := R) (S := S) (M := M) (N := N))

@[simp] lemma right_smul_mk (u : Uᵐᵒᵖ) (m : M) (n : N) :
    u • (mk (k := k) (R := R) (S := S) m n) = mk m (u • n) := rfl

end BalancedTensor
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

abbrev evalType (M : ModuleCat (Alg k S R)) :=
  BalancedTensor.T (k := k) (R := R) (S := S) (M := Obj M) (N := X)

def evalObj (M : ModuleCat (Alg k S R)) : ModuleCat S := ModuleCat.of S (evalType X M)

def evalMap {M N : ModuleCat (Alg k S R)} (f : M ⟶ N) : evalObj X M ⟶ evalObj X N :=
  ModuleCat.ofHom (BalancedTensor.mapLeft (k := k) (R := R) (S := S) (N := X)
    (leftMap f) (fun r m => (rightMap f).map_smul r m))

@[simp] lemma evalMap_mk {M N : ModuleCat (Alg k S R)} (f : M ⟶ N) (m : Obj M) (x : X) :
    evalMap X f (BalancedTensor.mk m x) = BalancedTensor.mk (k := k) (R := R) (S := S) (N := X) (leftMap f m) x := rfl

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Twisting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def Bimod (_φ : R →ₐ[k] S) := S
instance instAddCommGroupBimod (φ : R →ₐ[k] S) : AddCommGroup (Bimod φ) := inferInstanceAs (AddCommGroup S)
instance instModuleBimod (φ : R →ₐ[k] S) : Module S (Bimod φ) := inferInstanceAs (Module S S)
instance instModuleBimod_1 (φ : R →ₐ[k] S) : Module k (Bimod φ) := inferInstanceAs (Module k S)
instance instIsScalarTowerBimod (φ : R →ₐ[k] S) : IsScalarTower k S (Bimod φ) := inferInstanceAs (IsScalarTower k S S)
instance instModuleMulOppositeBimod (φ : R →ₐ[k] S) : Module Rᵐᵒᵖ (Bimod φ) :=
  Module.compHom S φ.op.toRingHom
instance instSMulCommClassMulOppositeBimod (φ : R →ₐ[k] S) : SMulCommClass S Rᵐᵒᵖ (Bimod φ) where
  smul_comm s r x := (mul_assoc s x (φ r.unop)).symm

variable (φ : R →ₐ[k] S)
abbrev functor : ModuleCat.{0} R ⥤ ModuleCat.{0} S :=
  BalancedTensor.functor (k := k) (R := R) (S := S) (M := Bimod φ)
abbrev res : ModuleCat.{0} S ⥤ ModuleCat.{0} R := ModuleCat.restrictScalars φ.toRingHom

lemma mk_one_smul (N : ModuleCat.{0} R) (s : S) (n : N) :
    BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from s) n =
      s • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n := by
  have h := LinearMap.congr_fun ((BalancedTensor.mk (k := k) (R := R) (S := S) (N := N)).map_smul s (show Bimod φ from (1 : S))) n
  have hs : s • (show Bimod φ from (1 : S)) = (show Bimod φ from s) := mul_one s
  rw [hs] at h
  exact h

def unit (N : ModuleCat.{0} R) : N ⟶ (res φ).obj ((functor φ).obj N) := ModuleCat.ofHom (Y := (res φ).obj ((functor φ).obj N))
  { toFun := fun n => BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n
    map_add' := by intro x y; exact (BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S))).map_add x y
    map_smul' := by
      intro r n
      change BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) (r • n) =
        φ r • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n
      rw [← BalancedTensor.balance]
      change BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 * φ r : S)) n = _
      rw [one_mul]
      exact mk_one_smul φ N (φ r) n }

def extend {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P) :
    (functor φ).obj N ⟶ P := ModuleCat.ofHom (BalancedTensor.lift
  { toFun := fun s =>
      { toFun := fun n => (show S from s) • (show P from f n)
        map_add' := by
          intro x y
          exact (congrArg (fun z : P => (show S from s) • z) (f.hom.map_add x y)).trans
            (smul_add (show S from s) (show P from f x) (show P from f y))
        map_smul' := by
          intro c n
          have hc := f.hom.map_smul (algebraMap k R c) n
          change (show P from f ((algebraMap k R c) • n)) = φ (algebraMap k R c) • (show P from f n) at hc
          rw [IsScalarTower.algebraMap_smul, φ.commutes, IsScalarTower.algebraMap_smul] at hc
          change (show S from s) • (show P from f (c • n)) = c • ((show S from s) • (show P from f n))
          rw [hc, smul_comm] }
    map_add' := by intro s t; ext n; exact add_smul (show S from s) (show S from t) (show P from f n)
    map_smul' := by intro s t; ext n; exact mul_smul s (show S from t) (show P from f n) }
  (by
    intro r s n
    change ((show S from s) * φ r) • f n = (show S from s) • (show P from f (r • n))
    rw [mul_smul, f.hom.map_smul]
    rfl))

@[simp] lemma extend_mk {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P)
    (s : Bimod φ) (n : N) : extend φ f (BalancedTensor.mk s n) = (show S from s) • (show P from f n) := rfl

lemma unit_extend {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P) :
    unit φ N ≫ (res φ).map (extend φ f) = f := by
  ext n
  change (1:S) • f n = f n
  exact one_smul S (f n)

lemma extend_unit {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : (functor φ).obj N ⟶ P) :
    extend φ (unit φ N ≫ (res φ).map f) = f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro s n
  change (show S from s) • f.hom (BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n) =
    f.hom (BalancedTensor.mk s n)
  trans f.hom ((show S from s) • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n)
  · exact (f.hom.map_smul _ _).symm
  exact congrArg f.hom (mk_one_smul φ N (show S from s) n).symm

def homEquiv (N : ModuleCat.{0} R) (P : ModuleCat.{0} S) :
    ((functor φ).obj N ⟶ P) ≃ (N ⟶ (res φ).obj P) where
  toFun f := unit φ N ≫ (res φ).map f
  invFun := extend φ
  left_inv := extend_unit φ
  right_inv := unit_extend φ

def underlyingEquiv (N : ModuleCat.{0} R) :
    ((functor φ).obj N) ≃ₗ[k]
      BalancedTensor.T (k := k) (R := R) (S := S) (M := Bimod φ) (N := N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := IsScalarTower.algebraMap_smul S c
    (show BalancedTensor.T (k := k) (R := R) (S := S) (M := Bimod φ) (N := N) from x)

end Tachikawa.AlgebraInduction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k A B : Type u} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma map_add_left {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f f' : M ⟶ M') (g : N ⟶ N') : map (k := k) (f+f') g = map f g + map f' g := by
  apply LinearMap.restrictScalars_injective k
  change TensorProduct.map ((f.hom.restrictScalars k)+(f'.hom.restrictScalars k))
    (g.hom.restrictScalars k) = _
  exact TensorProduct.map_add_left _ _ _

lemma map_add_right {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g g' : N ⟶ N') : map (k := k) f (g+g') = map f g + map f g' := by
  apply LinearMap.restrictScalars_injective k
  change TensorProduct.map (f.hom.restrictScalars k)
    ((g.hom.restrictScalars k)+(g'.hom.restrictScalars k)) = _
  exact TensorProduct.map_add_right _ _ _

instance instAdditiveModuleCatTensorProductObjFunctorBifunctor (M : ModuleCat.{u} A) : ((bifunctor k A B).obj M).Additive where
  map_add {_X _Y} g g' := ModuleCat.hom_ext (map_add_right (k := k) (𝟙 M) g g')

instance instAdditiveModuleCatFunctorTensorProductBifunctor : (bifunctor k A B).Additive where
  map_add {_X _Y} f f' := by
    apply NatTrans.ext
    funext N
    exact ModuleCat.hom_ext (map_add_left f f' (𝟙 N))

end Tachikawa.OuterTensor



namespace Tachikawa.TotalMap
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
universe u
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable {I₁ I₂ J : Type u} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (F : C ⥤ D) [F.Additive] (K : HomologicalComplex₂ C c₁ c₂)
variable (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]

abbrev map₂ : HomologicalComplex₂ D c₁ c₂ :=
  ((F.mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj K

variable [K.HasTotal c] [(map₂ F K).HasTotal c]

instance targetHasCoproduct (j : J) : HasCoproduct
    (fun t => F.obj (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j t)) :=
  (inferInstance : (map₂ F K).HasTotal c) j

abbrev compareX (j : J) : ((map₂ F K).total c).X j ⟶ F.obj ((K.total c).X j) :=
  sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)

@[reassoc (attr := simp)]
lemma ι_compareX (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    (map₂ F K).ιTotal c i₁ i₂ j h ≫ compareX F K c j =
      F.map (K.ιTotal c i₁ i₂ j h) := by
  exact ι_comp_sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) ⟨(i₁,i₂), h⟩

@[reassoc]
lemma ιOrZero_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).ιTotalOrZero c i₁ i₂ j ≫ compareX F K c j =
      F.map (K.ιTotalOrZero c i₁ i₂ j) := by
  by_cases h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j
  · simp only [ιTotalOrZero_eq _ _ _ _ _ h, ι_compareX]
  · simp only [ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp, F.map_zero]

lemma d₁_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).d₁ c i₁ i₂ j ≫ compareX F K c j = F.map (K.d₁ c i₁ i₂ j) := by
  change (ComplexShape.ε₁ c₁ c₂ c (i₁,i₂) •
    (F.map ((K.d i₁ (c₁.next i₁)).f i₂) ≫ (map₂ F K).ιTotalOrZero c _ _ j)) ≫
      compareX F K c j = F.map (ComplexShape.ε₁ c₁ c₂ c (i₁,i₂) •
        ((K.d i₁ (c₁.next i₁)).f i₂ ≫ K.ιTotalOrZero c _ _ j))
  rw [Linear.units_smul_comp, Category.assoc, ιOrZero_compareX,
    F.map_units_smul, F.map_comp]

lemma d₂_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).d₂ c i₁ i₂ j ≫ compareX F K c j = F.map (K.d₂ c i₁ i₂ j) := by
  change (ComplexShape.ε₂ c₁ c₂ c (i₁,i₂) •
    (F.map ((K.X i₁).d i₂ (c₂.next i₂)) ≫ (map₂ F K).ιTotalOrZero c _ _ j)) ≫
      compareX F K c j = F.map (ComplexShape.ε₂ c₁ c₂ c (i₁,i₂) •
        ((K.X i₁).d i₂ (c₂.next i₂) ≫ K.ιTotalOrZero c _ _ j))
  rw [Linear.units_smul_comp, Category.assoc, ιOrZero_compareX,
    F.map_units_smul, F.map_comp]

def comparison : (map₂ F K).total c ⟶ (F.mapHomologicalComplex c).obj (K.total c) where
  f := compareX F K c
  comm' j j' _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ h
    simp only [ι_compareX_assoc, Functor.mapHomologicalComplex_obj_d,
      ← F.map_comp, total_d, Preadditive.comp_add, ι_D₁, ι_D₂, F.map_add,
      Preadditive.add_comp, ι_D₁_assoc, ι_D₂_assoc, d₁_compareX, d₂_compareX]

variable [∀ j, PreservesColimit
  (Discrete.functor (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F]

instance instIsIsoCompareX (j : J) : IsIso (compareX F K c j) := by
  have : PreservesColimit (Discrete.functor
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F := inferInstance
  change IsIso (sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j))
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

instance instIsIsoHomologicalComplexComparison : IsIso (comparison F K c) := by
  have (j : J) : IsIso ((comparison F K c).f j) :=
    inferInstanceAs (IsIso (compareX F K c j))
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : (map₂ F K).total c ≅ (F.mapHomologicalComplex c).obj (K.total c) :=
  asIso (comparison F K c)

end Tachikawa.TotalMap



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

abbrev forgetA := ModuleCat.restrictScalars (algebraMap k A)
abbrev forgetB := ModuleCat.restrictScalars (algebraMap k B)
abbrev forgetE := ModuleCat.restrictScalars (algebraMap k (A ⊗[k] B))
abbrev tensorF := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} k)

def forgetObjIso (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    (forgetE k A B).obj ((bifunctor k A B).obj M |>.obj N) ≅
      ((tensorF k).obj ((forgetA k A).obj M)).obj ((forgetB k B).obj N) :=
  LinearEquiv.toModuleIso
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (algebraMap k (A ⊗[k] B) r) • (show Obj k A B M N from x) = r • (show M ⊗[k] N from x)
        change action k A B M N (algebraMap k (A ⊗[k] B) r) x = r • (show M ⊗[k] N from x)
        rw [AlgHom.commutes]
        rfl }

@[reassoc]
lemma forgetObjIso_natural {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (forgetE k A B).map (ModuleCat.ofHom (map (k := k) f g)) ≫ (forgetObjIso k A B M' N').hom =
      (forgetObjIso k A B M N).hom ≫
        ((tensorF k).map ((forgetA k A).map f)).app ((forgetB k B).obj N) ≫
          ((tensorF k).obj ((forgetA k A).obj M')).map ((forgetB k B).map g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

@[reassoc]
lemma forgetBifunctor_natural {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (forgetE k A B).map ((bifunctor k A B).map f |>.app N) ≫
      (forgetE k A B).map (((bifunctor k A B).obj M').map g) ≫
      (forgetObjIso k A B M' N').hom =
    (forgetObjIso k A B M N).hom ≫
      ((tensorF k).map ((forgetA k A).map f)).app ((forgetB k B).obj N) ≫
        ((tensorF k).obj ((forgetA k A).obj M')).map ((forgetB k B).map g) := by
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
universe u
variable (k A B : Type u) [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable {I₁ I₂ : Type u} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K : HomologicalComplex (ModuleCat.{u} A) c₁) (L : HomologicalComplex (ModuleCat.{u} B) c₂)

abbrev outerBicomplex := ((bifunctor k A B).mapBifunctorHomologicalComplex c₁ c₂).obj K |>.obj L
abbrev vectorBicomplex := ((tensorF k).mapBifunctorHomologicalComplex c₁ c₂).obj
  (((forgetA k A).mapHomologicalComplex c₁).obj K) |>.obj
    (((forgetB k B).mapHomologicalComplex c₂).obj L)

def forgetBicomplexIso :
    TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L) ≅ vectorBicomplex k A B K L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => forgetObjIso k A B (K.X i) (L.X j)) (by
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

variable {J : Type u} (c : ComplexShape J) [DecidableEq J]
  [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K L (bifunctor k A B) c]
  [HasMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
    (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c]
  [(TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L)).HasTotal c]

def forgetTotalIso :
    ((forgetE k A B).mapHomologicalComplex c).obj
      (mapBifunctor K L (bifunctor k A B) c) ≅
    mapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
      (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c :=
  (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).symm ≪≫
    HomologicalComplex₂.total.mapIso (forgetBicomplexIso k A B K L) c

@[reassoc]
lemma ι_forgetTotalIso (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁,i₂) = j) :
    (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
      (forgetTotalIso k A B K L c).hom.f j =
    (forgetObjIso k A B (K.X i₁) (L.X i₂)).hom ≫
      ιMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
        (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c i₁ i₂ j h := by
  erw [← TotalMap.ι_compareX (forgetE k A B) (outerBicomplex k A B K L) c i₁ i₂ j h]
  change (_ ≫ (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j) ≫
    ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).inv ≫
      (HomologicalComplex₂.total.mapIso (forgetBicomplexIso k A B K L) c).hom).f j = _
  erw [HomologicalComplex.comp_f, Category.assoc, ← Category.assoc
    ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j)
      ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).inv.f j)]
  have hh := HomologicalComplex.congr_hom
    (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom_inv_id j
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hh
  erw [hh, Category.id_comp]
  exact HomologicalComplex₂.ιTotal_map _ _ (forgetBicomplexIso k A B K L).hom c i₁ i₂ j h

variable (K' : HomologicalComplex (ModuleCat.{u} A) c₁)
  (L' : HomologicalComplex (ModuleCat.{u} B) c₂)
  [HasMapBifunctor K' L' (bifunctor k A B) c]
  [HasMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K')
    (((forgetB k B).mapHomologicalComplex c₂).obj L') (tensorF k) c]
  [(TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K' L')).HasTotal c]

@[reassoc]
lemma forgetTotalIso_natural (f : K ⟶ K') (g : L ⟶ L') :
    ((forgetE k A B).mapHomologicalComplex c).map
      (mapBifunctorMap f g (bifunctor k A B) c) ≫ (forgetTotalIso k A B K' L' c).hom =
    (forgetTotalIso k A B K L c).hom ≫
      mapBifunctorMap (((forgetA k A).mapHomologicalComplex c₁).map f)
        (((forgetB k B).mapHomologicalComplex c₂).map g) (tensorF k) c := by
  apply HomologicalComplex.Hom.ext
  funext j
  rw [← cancel_epi ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j)]
  apply HomologicalComplex₂.total.hom_ext
  intro i₁ i₂ h
  have hh : (TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L)).ιTotal c i₁ i₂ j h ≫
      (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j =
      (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) :=
    TotalMap.ι_compareX (forgetE k A B) (outerBicomplex k A B K L) c i₁ i₂ j h
  rw [← Category.assoc, ← Category.assoc, hh]
  change (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
    ((forgetE k A B).map ((mapBifunctorMap f g (bifunctor k A B) c).f j) ≫ _) =
      (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
        ((forgetTotalIso k A B K L c).hom.f j ≫ _)
  rw [← Category.assoc, ← Functor.map_comp, ι_mapBifunctorMap,
    Functor.map_comp, Functor.map_comp]
  rw [Category.assoc, Category.assoc, ι_forgetTotalIso,
    ι_forgetTotalIso_assoc, ι_mapBifunctorMap]
  exact forgetBifunctor_natural_assoc k A B (f.f i₁) (g.f i₂)
    (ιMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K')
      (((forgetB k B).mapHomologicalComplex c₂).obj L') (tensorF k) c i₁ i₂ j h)

end Tachikawa.OuterTensor
set_option backward.isDefEq.respectTransparency true



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M U : ModuleCat A} {N V : ModuleCat B}

def morphism (f : M ⟶ U) (g : N ⟶ V) :
    (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  ModuleCat.ofHom (map (k := k) f g)

lemma map_smul_left (r : k) (f : M ⟶ U) (g : N ⟶ V) :
    morphism (k := k) (r • f) g = r • morphism (k := k) f g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change map (k := k) _ _ z = (algebraMap k (A ⊗[k] B) r) • (map (k := k) f g z)
  induction z using OAI.tensorInductionOn with
  | tmul x y =>
    change (r • f x) ⊗ₜ[k] g y = (algebraMap k (A ⊗[k] B) r) • (show Obj k A B U V from f x ⊗ₜ[k] g y)
    change (r • f x) ⊗ₜ[k] g y = action k A B U V (algebraMap k (A ⊗[k] B) r) _
    rw [AlgHom.commutes]
    exact TensorProduct.smul_tmul' _ _ _
  | add z z' hz hz' =>
    exact ((map (k := k) _ _).map_add z z').trans
      ((congrArg₂ (· + ·) hz hz').trans ((smul_add _ _ _).symm.trans
      (congrArg (fun w : Obj k A B U V => (algebraMap k (A ⊗[k] B) r) • w)
        ((map (k := k) f g).map_add z z').symm)))

lemma map_smul_right (r : k) (f : M ⟶ U) (g : N ⟶ V) :
    morphism (k := k) f (r • g) = r • morphism (k := k) f g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change map (k := k) _ _ z = (algebraMap k (A ⊗[k] B) r) • (map (k := k) f g z)
  induction z using OAI.tensorInductionOn with
  | tmul x y =>
    change f x ⊗ₜ[k] (r • g y) = (algebraMap k (A ⊗[k] B) r) • (show Obj k A B U V from f x ⊗ₜ[k] g y)
    change f x ⊗ₜ[k] (r • g y) = action k A B U V (algebraMap k (A ⊗[k] B) r) _
    rw [AlgHom.commutes]
    exact TensorProduct.tmul_smul _ _ _
  | add z z' hz hz' =>
    exact ((map (k := k) _ _).map_add z z').trans
      ((congrArg₂ (· + ·) hz hz').trans ((smul_add _ _ _).symm.trans
      (congrArg (fun w : Obj k A B U V => (algebraMap k (A ⊗[k] B) r) • w)
        ((map (k := k) f g).map_add z z').symm)))

def homMap : (M ⟶ U) ⊗[k] (N ⟶ V) →ₗ[k]
    (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun g => morphism (k := k) f g
          map_add' := fun g g' => ModuleCat.hom_ext (map_add_right f g g')
          map_smul' := fun r g => map_smul_right r f g }
      map_add' := fun f f' => LinearMap.ext fun g => ModuleCat.hom_ext (map_add_left f f' g)
      map_smul' := fun r f => LinearMap.ext fun g => map_smul_left r f g }

@[simp] lemma homMap_tmul (f : M ⟶ U) (g : N ⟶ V) :
    homMap (f ⊗ₜ[k] g) = morphism (k := k) f g := rfl

end Tachikawa.OuterTensor



namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def unitLinear (φ : R →ₐ[k] S) (M : ModuleCat R) : M →ₗ[k] (functor φ).obj M where
  toFun := unit φ M
  map_add' := (unit φ M).hom.map_add
  map_smul' c x := by
    have h := (unit φ M).hom.map_smul (algebraMap k R c) x
    change (show (functor φ).obj M from unit φ M ((algebraMap k R c) • x)) =
      φ (algebraMap k R c) • (show (functor φ).obj M from unit φ M x) at h
    rw [IsScalarTower.algebraMap_smul, φ.commutes, IsScalarTower.algebraMap_smul] at h
    exact h

lemma unitLinear_smul (φ : R →ₐ[k] S) (M : ModuleCat R) (r : R) (m : M) :
    unitLinear φ M (r • m) = φ r • unitLinear φ M m := (unit φ M).hom.map_smul r m

end Tachikawa.AlgebraInduction

namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)

abbrev inductionTarget := (bifunctor k S T).obj ((AlgebraInduction.functor φ).obj M) |>.obj
  ((AlgebraInduction.functor ψ).obj N)

def inductionUnit : ((bifunctor k A B).obj M).obj N ⟶
    (AlgebraInduction.res (Algebra.TensorProduct.map φ ψ)).obj (inductionTarget φ ψ M N) :=
  ModuleCat.ofHom
    (X := ((bifunctor k A B).obj M).obj N)
    (Y := (AlgebraInduction.res (Algebra.TensorProduct.map φ ψ)).obj (inductionTarget φ ψ M N))
    { toFun := TensorProduct.map (AlgebraInduction.unitLinear φ M) (AlgebraInduction.unitLinear ψ N)
      map_add' := map_add _
      map_smul' := by
        intro r z
        induction r using OAI.tensorInductionOn with
        | add a b ha hb =>
          erw [add_smul, map_add, ha, hb, RingHom.id_apply, add_smul]
          rfl
        | tmul a b =>
          induction z using OAI.tensorInductionOn with
          | add x y hx hy =>
            erw [smul_add, map_add, hx, hy, map_add, smul_add]
            rfl
          | tmul x y =>
            change AlgebraInduction.unitLinear φ M (a • x) ⊗ₜ[k]
                AlgebraInduction.unitLinear ψ N (b • y) =
              (φ a • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
                (ψ b • AlgebraInduction.unitLinear ψ N y)
            rw [AlgebraInduction.unitLinear_smul, AlgebraInduction.unitLinear_smul] }

def inductionComparison :
    (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).obj
      (((bifunctor k A B).obj M).obj N) ⟶ inductionTarget φ ψ M N :=
  AlgebraInduction.extend (Algebra.TensorProduct.map φ ψ) (inductionUnit φ ψ M N)

@[simp] lemma inductionComparison_pure (s : S) (t : T) (x : M) (y : N) :
    inductionComparison φ ψ M N
      (BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
        (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from s ⊗ₜ[k] t)
        (show Obj k A B M N from x ⊗ₜ[k] y)) =
      (s • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
        (t • AlgebraInduction.unitLinear ψ N y) := rfl

@[reassoc] lemma inductionComparison_natural {M' : ModuleCat A} {N' : ModuleCat B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).map (ModuleCat.ofHom (map f g)) ≫
        inductionComparison φ ψ M' N' =
      inductionComparison φ ψ M N ≫ ModuleCat.ofHom
        (map ((AlgebraInduction.functor φ).map f) ((AlgebraInduction.functor ψ).map g)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
  intro s z
  change (show S ⊗[k] T from s) •
      (show inductionTarget φ ψ M' N' from inductionUnit φ ψ M' N' (map f g z)) =
    (map ((AlgebraInduction.functor φ).map f) ((AlgebraInduction.functor ψ).map g))
      ((show S ⊗[k] T from s) • (show inductionTarget φ ψ M N from inductionUnit φ ψ M N z))
  erw [map_smul]
  congr 1
  induction z using OAI.tensorInductionOn with
  | add x y hx hy =>
    exact ((congrArg (inductionUnit φ ψ M' N') (map_add (map f g) x y)).trans
      (map_add (inductionUnit φ ψ M' N').hom _ _)).trans
        ((congrArg₂ (· + ·) hx hy).trans
          ((map_add (map ((AlgebraInduction.functor φ).map f)
            ((AlgebraInduction.functor ψ).map g)) _ _).symm.trans
              (congrArg (map ((AlgebraInduction.functor φ).map f)
                ((AlgebraInduction.functor ψ).map g))
                  (map_add (inductionUnit φ ψ M N).hom x y).symm)))
  | tmul x y => rfl

end Tachikawa.OuterTensor



namespace Tachikawa.BalancedTensor
variable {k R S M N P : Type*} [Field k] [Ring R] [Ring S] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module R N]
  [AddCommGroup P] [Module k P]

def liftGround (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n)) :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[k] P :=
  (lift (S := k) f hf).comp restrictEquiv.toLinearMap

@[simp] lemma liftGround_mk (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (m : M) (n : N) :
    liftGround (S := S) f hf (mk (k := k) (R := R) (S := S) m n) = f m n := rfl

omit [SMulCommClass S Rᵐᵒᵖ M] in
@[ext] theorem hom_ext_ground
    {f g : T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[k] P}
    (h : ∀ m n, f (mk m n) = g (mk m n)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | h0 => simp only [map_zero]
  | ht m n => exact h m n
  | ha x y hx hy => simp only [map_add, hx, hy]

lemma liftGround_add (f g : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (hg : ∀ (r : R) (m : M) (n : N), g (MulOpposite.op r • m) n = g m (r • n))
    (hfg : ∀ (r : R) (m : M) (n : N), (f+g) (MulOpposite.op r • m) n = (f+g) m (r • n)) :
    liftGround (S := S) (f+g) hfg = liftGround f hf + liftGround g hg := by
  apply hom_ext_ground
  intro m n
  rfl

lemma liftGround_smul (c : k) (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (hcf : ∀ (r : R) (m : M) (n : N), (c • f) (MulOpposite.op r • m) n = (c • f) m (r • n)) :
    liftGround (S := S) (c • f) hcf = c • liftGround f hf := by
  apply hom_ext_ground
  intro m n
  rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)

abbrev inductionSource := (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).obj
  (((bifunctor k A B).obj M).obj N)

def underlyingEquiv (M : ModuleCat A) (N : ModuleCat B) :
    (((bifunctor k A B).obj M).obj N) ≃ₗ[k] (M ⊗[k] N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := IsScalarTower.algebraMap_smul (A ⊗[k] B) c
    (show Obj k A B M N from x)

def inductionSourceMk : (S ⊗[k] T) →ₗ[k] (M ⊗[k] N) →ₗ[k] inductionSource φ ψ M N :=
  (((BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
      (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
      (N := ((bifunctor k A B).obj M).obj N)).restrictScalars k).compl₂
        (underlyingEquiv M N).symm.toLinearMap).compr₂
          (AlgebraInduction.underlyingEquiv (Algebra.TensorProduct.map φ ψ)
            (((bifunctor k A B).obj M).obj N)).symm.toLinearMap

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

def rightMultiply (r : R) : R →ₗ[R] R where
  toFun x := x*r
  map_add' x y := add_mul x y r
  map_smul' a x := mul_assoc a x r

@[simp] lemma rightMultiply_apply (r x : R) : rightMultiply r x = x*r := rfl

def Nakayama (k R M : Type) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] := Module.Dual k (M →ₗ[R] R)

namespace Nakayama
instance instAddCommGroup : AddCommGroup (Nakayama k R M) := inferInstanceAs (AddCommGroup (Module.Dual k (M →ₗ[R] R)))
instance instModule : Module k (Nakayama k R M) := inferInstanceAs (Module k (Module.Dual k (M →ₗ[R] R)))
instance instFunLikeLinearMapId : FunLike (Nakayama k R M) (M →ₗ[R] R) k := inferInstanceAs (FunLike (Module.Dual k (M →ₗ[R] R)) _ _)
instance instLinearMapClassLinearMapId : LinearMapClass (Nakayama k R M) k (M →ₗ[R] R) k := inferInstanceAs (LinearMapClass (Module.Dual k (M →ₗ[R] R)) _ _ _)
@[ext] lemma ext {x y : Nakayama k R M} (h : ∀ f, x f = y f) : x=y := LinearMap.ext h

def homRight (r : R) : (M →ₗ[R] R) →ₗ[k] (M →ₗ[R] R) where
  toFun f := (rightMultiply r).comp f
  map_add' f g := by ext; simp [add_mul]
  map_smul' c f := by ext; simp

@[simp] lemma homRight_apply (r : R) (f : M →ₗ[R] R) (x : M) : homRight (k := k) r f x = f x*r := rfl

instance instModule_1 : Module R (Nakayama k R M) where
  smul r ψ := ψ.comp (homRight r)
  one_smul ψ := by ext f; change ψ (homRight 1 f) = ψ f; congr 1; ext; simp
  mul_smul r s ψ := by
    ext f
    change ψ (homRight (r*s) f) = ψ (homRight s (homRight r f))
    congr 1
    ext
    simp [mul_assoc]
  smul_zero r := by ext; rfl
  smul_add r ψ φ := by ext; rfl
  zero_smul ψ := by
    ext f
    change ψ (homRight 0 f) = 0
    have he : homRight (k := k) 0 f = 0 := by ext; simp
    rw [he]
    exact LinearMap.map_zero ψ
  add_smul r s ψ := by
    ext f
    change ψ (homRight (r+s) f) = ψ (homRight r f) + ψ (homRight s f)
    rw [← map_add]
    congr 1
    ext
    simp [mul_add]

@[simp] lemma action_apply (r : R) (ψ : Nakayama k R M) (f : M →ₗ[R] R) :
    (r • ψ) f = ψ (homRight (k := k) r f) := rfl
@[simp] lemma add_apply (ψ φ : Nakayama k R M) (f : M →ₗ[R] R) : (ψ+φ) f = ψ f+φ f := rfl
@[simp] lemma zero_apply (f : M →ₗ[R] R) : (0 : Nakayama k R M) f = 0 := rfl
@[simp] lemma smul_apply (c : k) (ψ : Nakayama k R M) (f : M →ₗ[R] R) : (c • ψ) f = c*ψ f := rfl

instance instIsScalarTower : IsScalarTower k R (Nakayama k R M) where
  smul_assoc c r ψ := by
    ext f
    change ψ (homRight (c • r) f) = c • ψ (homRight r f)
    calc
      ψ (homRight (c • r) f) = ψ (c • homRight r f) := by
        congr 1
        ext
        simp
      _ = _ := (ψ : Module.Dual k (M →ₗ[R] R)).map_smul c _

variable [Module k M] [IsScalarTower k R M]

def evaluationBilinear : DualBimodule k R →ₗ[R] M →ₗ[k] Nakayama k R M where
  toFun φ :=
    { toFun := fun m =>
        { toFun := fun f => φ (f m)
          map_add' := by intro f g; simp
          map_smul' := by intro c f; simp }
      map_add' := by
        intro m n
        ext f
        change φ (f (m+n)) = φ (f m) + φ (f n)
        simp
      map_smul' := by
        intro c m
        ext f
        change (φ : R →ₗ[k] k) ((f.restrictScalars k) (c • m)) = c * φ (f m)
        exact ((φ : R →ₗ[k] k).comp (f.restrictScalars k)).map_smul c m }
  map_add' := by intro x y; ext m f; rfl
  map_smul' := by intro r φ; ext m f; rfl

@[simp] lemma evaluationBilinear_apply (φ : DualBimodule k R) (m : M) (f : M →ₗ[R] R) :
    evaluationBilinear (k := k) (R := R) φ m f = φ (f m) := rfl

lemma evaluation_balanced (r : R) (φ : DualBimodule k R) (m : M) :
    evaluationBilinear (MulOpposite.op r • φ) m = evaluationBilinear (k := k) (R := R) φ (r • m) := by
  ext f
  simp

end Nakayama
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

def reverseCoeff (n : ℕ) : k := (q^(n+2))⁻¹

end Tachikawa.C



end


end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
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

def Base : Type := X →ₗ[k] Z
instance instCoeFunBaseForallCarrier : CoeFun (Base (k := k) X Z) (fun _ => X → Z) := ⟨fun f => (show X →ₗ[k] Z from f)⟩
instance instAddCommGroupBase : AddCommGroup (Base (k := k) X Z) := inferInstanceAs (AddCommGroup (X →ₗ[k] Z))
instance instModuleBase : Module k (Base (k := k) X Z) := inferInstanceAs (Module k (X →ₗ[k] Z))
instance instModuleBase_1 : Module S (Base (k := k) X Z) := inferInstanceAs (Module S (X →ₗ[k] Z))
instance instIsScalarTowerBase : IsScalarTower k S (Base (k := k) X Z) :=
  inferInstanceAs (IsScalarTower k S (X →ₗ[k] Z))

def rightAction : Rᵐᵒᵖ →+* Module.End S (Base (k := k) X Z) where
  toFun r :=
    { toFun := fun f => (show X →ₗ[k] Z from f).comp ((Algebra.lsmul k k X) r.unop)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact congrArg f (one_smul R x)
  map_mul' r s := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact congrArg f (mul_smul s.unop r.unop x)
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    change f ((0:R) • x) = 0
    exact (congrArg f (zero_smul R x)).trans (show X →ₗ[k] Z from f).map_zero
  map_add' r s := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact (congrArg f (add_smul r.unop s.unop x)).trans (f.map_add _ _)

instance instModuleMulOppositeBase : Module Rᵐᵒᵖ (Base (k := k) X Z) := Module.compHom _ (rightAction (k := k) X Z)
instance instSMulCommClassMulOppositeBase : SMulCommClass S Rᵐᵒᵖ (Base (k := k) X Z) where
  smul_comm _ _ _ := rfl
instance instIsScalarTowerMulOppositeBase : IsScalarTower k Rᵐᵒᵖ (Base (k := k) X Z) :=
  IsScalarTower.of_algebraMap_smul fun c f => by
    apply LinearMap.ext
    intro x
    change f ((algebraMap k R c) • x) = c • f x
    rw [IsScalarTower.algebraMap_smul]
    exact f.map_smul c x

def obj : ModuleCat (Enveloping.Alg k S R) :=
  Enveloping.ofBimodule (k := k) (R := S) (S := R) (Base (k := k) X Z)

lemma left_smul_apply (s : S) (f : Enveloping.Obj (obj (k := k) X Z)) (x : X) :
    (show X →ₗ[k] Z from (s • f)) x = s • (show X →ₗ[k] Z from f) x := by
  change s • (show X →ₗ[k] Z from f) ((1:R) • x) = _
  rw [one_smul]

lemma right_smul_apply (r : Rᵐᵒᵖ) (f : Enveloping.Obj (obj (k := k) X Z)) (x : X) :
    (show X →ₗ[k] Z from (r • f)) x = (show X →ₗ[k] Z from f) (r.unop • x) := by
  change (1:S) • (show X →ₗ[k] Z from f) (r.unop • x) = _
  rw [one_smul]

end HomBimodule



namespace BimoduleTensorHom
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M : ModuleCat (Enveloping.Alg k S R)} {X : ModuleCat R} {Z : ModuleCat S}

def uncurryLinear (f : M ⟶ HomBimodule.obj (k := k) X Z) :
    Enveloping.Obj M →ₗ[S] (X →ₗ[k] Z) where
  toFun := fun m => f m
  map_add' a b := f.hom.map_add a b
  map_smul' s m := by
    apply LinearMap.ext
    intro x
    exact (congrArg (fun h : Enveloping.Obj (HomBimodule.obj (k := k) X Z) =>
      (show X →ₗ[k] Z from h) x) ((Enveloping.leftMap f).map_smul s m)).trans
        (HomBimodule.left_smul_apply X Z s (f m) x)

lemma uncurryLinear_balanced (f : M ⟶ HomBimodule.obj (k := k) X Z)
    (r : R) (m : Enveloping.Obj M) (x : X) :
    uncurryLinear f (MulOpposite.op r • m) x = uncurryLinear f m (r • x) :=
  (congrArg (fun h : Enveloping.Obj (HomBimodule.obj (k := k) X Z) =>
      (show X →ₗ[k] Z from h) x) ((Enveloping.rightMap f).map_smul (MulOpposite.op r) m)).trans
    (HomBimodule.right_smul_apply X Z (MulOpposite.op r) (f m) x)

end BimoduleTensorHom
end Tachikawa



end

end OAI
end


