-- Prove2me | Definitions.Def_OAIQ031A004
-- name    : OAIQ031A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:05.432981+00:00
-- url     : https://prove2.me/theorems/80b93179-f3e8-47b7-9d0a-2815db3d07d4
-- title:
--   Definitions bundle OAIQ031A004 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 9 definitions, 4 inductive types or structures and 17 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.Enveloping`, `OAI.ArExplicit.CompleteComparison.DownHomPair`, `OAI.ArExplicit.CompleteComparison.UpHomPair`, `OAI.ArExplicit.CompleteComparison.UpPair`, `OAI.ArExplicit.ConeQuotientMap.Cone`, `OAI.ArExplicit.ConeQuotientMap.Source`, `OAI.ArExplicit.ConeQuotientMap.Target`, `OAI.ArExplicit.ConeQuotientMap.kernelInclusion`, `OAI.ArExplicit.ConeQuotientMap.quotientMap`, `OAI.ArExplicit.ExactProjectiveCochain`, `OAI.ArExplicit.ModuleBar.object`, `OAI.ArExplicit.cokernelLinearCongr`, `OAI.ArExplicit.coneBlock`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBimodule.lean), [`AuslanderReiten_Bar_ModuleBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBar.lean), [`AuslanderReiten_Complete_CompleteComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteComparison.lean), [`AuslanderReiten_Complete_CompleteNullhomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteNullhomotopy.lean), [`AuslanderReiten_Complete_CompleteResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteResolution.lean), [`AuslanderReiten_Complete_CompleteShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShift.lean), [`AuslanderReiten_Cones_CokernelLinearCongr`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CokernelLinearCongr.lean), [`AuslanderReiten_Cones_ConeExactness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeExactness.lean), [`AuslanderReiten_Cones_ConeQuotientMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeQuotientMap.lean), [`AuslanderReiten_Cones_MappingConeTotal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeTotal.lean), [`AuslanderReiten_Homology_LinearHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/LinearHomotopy.lean), [`AuslanderReiten_Modules_SplitModules`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/SplitModules.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A027`, `OAIQ031A028`, `OAIQ031A029`, `OAIQ031A030`, `OAIQ031A031`, `OAIQ031A034` and `OAIQ031A038`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBimodule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

abbrev Enveloping := R ⊗[k] Rᵐᵒᵖ

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

abbrev object : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k M
  | n + 1 => ModuleCat.of k (R ⊗[k] object n)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u v w x y z

variable {R : Type u} [Ring R]
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {L : Type w} [AddCommGroup L] [Module R L]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable {Q : Type y} [AddCommGroup Q] [Module R Q]

section ProjectiveLifting

theorem lift_through_exact [Module.Projective R Q]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M)
    (hex : LinearMap.range e = LinearMap.ker d)
    (f : Q →ₗ[R] L) (hf : d.comp f = 0) :
    ∃ g : Q →ₗ[R] K, e.comp g = f := by
  let f' : Q →ₗ[R] LinearMap.range e := f.codRestrict _ (by
    intro q
    rw [hex]
    exact DFunLike.congr_fun hf q)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property e.rangeRestrict f'
    e.surjective_rangeRestrict
  refine ⟨g, ?_⟩
  ext q
  exact congrArg Subtype.val (DFunLike.congr_fun hg q)

theorem lift_cokernel_map [Module.Projective R K] [Module.Projective R L]
    (e : K →ₗ[R] L) (d : M →ₗ[R] Q)
    (u : (L ⧸ LinearMap.range e) →ₗ[R] (Q ⧸ LinearMap.range d)) :
    ∃ (f₀ : L →ₗ[R] Q) (f₁ : K →ₗ[R] M),
      (LinearMap.range d).mkQ.comp f₀ = u.comp (LinearMap.range e).mkQ ∧
      d.comp f₁ = f₀.comp e := by
  obtain ⟨f₀, hf₀⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ
    (u.comp (LinearMap.range e).mkQ) (Submodule.mkQ_surjective _)
  have hz : (LinearMap.range d).mkQ.comp (f₀.comp e) = 0 := by
    ext q
    change (LinearMap.range d).mkQ (f₀ (e q)) = 0
    calc
      (LinearMap.range d).mkQ (f₀ (e q)) =
          u ((LinearMap.range e).mkQ (e q)) := DFunLike.congr_fun hf₀ (e q)
      _ = 0 := by
        rw [show (LinearMap.range e).mkQ (e q) = 0 by
          exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨q, rfl⟩, map_zero]
  obtain ⟨f₁, hf₁⟩ := lift_through_exact d (LinearMap.range d).mkQ
    (Submodule.ker_mkQ _).symm (f₀.comp e) hz
  exact ⟨f₀, f₁, hf₀, hf₁⟩

end ProjectiveLifting

section ComparisonSteps

universe a b c

variable {U : Type a} [AddCommGroup U] [Module R U]
variable {V : Type b} [AddCommGroup V] [Module R V]
variable {W : Type c} [AddCommGroup W] [Module R W]

theorem extend_comparison_up [Module.Projective R K]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M) (hde : d.comp e = 0)
    (e' : U →ₗ[R] V) (d' : V →ₗ[R] W)
    (hex : LinearMap.range e' = LinearMap.ker d')
    (f : L →ₗ[R] V) (g : M →ₗ[R] W) (hfg : d'.comp f = g.comp d) :
    ∃ h : K →ₗ[R] U, e'.comp h = f.comp e := by
  apply lift_through_exact e' d' hex (f.comp e)
  ext t
  change d' (f (e t)) = 0
  calc
    d' (f (e t)) = g (d (e t)) := DFunLike.congr_fun hfg (e t)
    _ = 0 := by rw [show d (e t) = 0 from DFunLike.congr_fun hde t, map_zero]

end ComparisonSteps

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace CompleteComparison

variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

structure UpPair (P Q : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) where
  lo : P.X (n : ℤ) →ₗ[R] Q.X (n : ℤ)
  hi : P.X ((n + 1 : ℕ) : ℤ) →ₗ[R] Q.X ((n + 1 : ℕ) : ℤ)
  comm : (Q.d (n + 1) n).hom.comp hi = lo.comp (P.d (n + 1) n).hom

end CompleteComparison

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_LinearHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]
variable {P₂ P₁ P₀ Q₃ Q₂ Q₁ : Type u}
variable [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup Q₃] [Module R Q₃]
variable [AddCommGroup Q₂] [Module R Q₂] [AddCommGroup Q₁] [Module R Q₁]

theorem extend_homotopy_up [Module.Projective R P₂]
    (p₂ : P₂ →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] P₀) (hp : p₁.comp p₂ = 0)
    (q₃ : Q₃ →ₗ[R] Q₂) (q₂ : Q₂ →ₗ[R] Q₁)
    (hq : LinearMap.range q₃ = LinearMap.ker q₂)
    (f₂ : P₂ →ₗ[R] Q₂) (f₁ : P₁ →ₗ[R] Q₁)
    (hc : q₂.comp f₂ = f₁.comp p₂)
    (h₁ : P₁ →ₗ[R] Q₂) (h₀ : P₀ →ₗ[R] Q₁)
    (hh : f₁ = q₂.comp h₁ + h₀.comp p₁) :
    ∃ h₂ : P₂ →ₗ[R] Q₃, f₂ = q₃.comp h₂ + h₁.comp p₂ := by
  have hz : q₂.comp (f₂ - h₁.comp p₂) = 0 := by
    ext x
    have hc' : q₂ (f₂ x) = f₁ (p₂ x) := DFunLike.congr_fun hc x
    have hh' : f₁ (p₂ x) = q₂ (h₁ (p₂ x)) + h₀ (p₁ (p₂ x)) :=
      DFunLike.congr_fun hh (p₂ x)
    have hp' : p₁ (p₂ x) = 0 := DFunLike.congr_fun hp x
    change q₂ (f₂ x - h₁ (p₂ x)) = 0
    rw [map_sub, hc', hh', hp', map_zero, add_zero, sub_self]
  obtain ⟨h₂, hh₂⟩ := lift_through_exact q₃ q₂ hq (f₂ - h₁.comp p₂) hz
  exact ⟨h₂, by rw [hh₂, sub_add_cancel]⟩

theorem factorization_of_initial_homotopy
    (e : P₂ →ₗ[R] P₁) (d : P₁ →ₗ[R] P₀) (hd : d.comp e = 0)
    (e' : Q₃ →ₗ[R] Q₂) (f : P₁ →ₗ[R] Q₂)
    (u : (P₁ ⧸ LinearMap.range e) →ₗ[R] (Q₂ ⧸ LinearMap.range e'))
    (hu : (LinearMap.range e').mkQ.comp f = u.comp (LinearMap.range e).mkQ)
    (h₀ : P₀ →ₗ[R] Q₂) (h₁ : P₁ →ₗ[R] Q₃)
    (hh : f = e'.comp h₁ + h₀.comp d) :
    ∃ (a : (P₁ ⧸ LinearMap.range e) →ₗ[R] P₀)
      (b : P₀ →ₗ[R] (Q₂ ⧸ LinearMap.range e')), b.comp a = u := by
  have he : LinearMap.range e ≤ LinearMap.ker d := by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun hd x
  let a : (P₁ ⧸ LinearMap.range e) →ₗ[R] P₀ := (LinearMap.range e).liftQ d he
  refine ⟨a, (LinearMap.range e').mkQ.comp h₀, ?_⟩
  apply LinearMap.ext
  intro t
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) t
  change (LinearMap.range e').mkQ (h₀ (d x)) = u ((LinearMap.range e).mkQ x)
  have hz : (LinearMap.range e').mkQ (e' (h₁ x)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨h₁ x, rfl⟩
  calc
    (LinearMap.range e').mkQ (h₀ (d x)) =
        (LinearMap.range e').mkQ (e' (h₁ x) + h₀ (d x)) := by
      rw [map_add, hz, zero_add]
    _ = (LinearMap.range e').mkQ (f x) :=
      congrArg (LinearMap.range e').mkQ (DFunLike.congr_fun hh x).symm
    _ = u ((LinearMap.range e).mkQ x) := DFunLike.congr_fun hu x

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteNullhomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

theorem comm_linear (F : P ⟶ Q) (i j : ℤ) :
    (Q.d i j).hom.comp (F.f i).hom = (F.f j).hom.comp (P.d i j).hom :=
  congrArg (fun f : P.X i ⟶ Q.X j => f.hom) (F.comm i j)

structure UpHomPair (F : P ⟶ Q) (n : ℕ) where
  lo : P.X (n : ℤ) →ₗ[R] Q.X ((n + 1 : ℕ) : ℤ)
  hi : P.X ((n + 1 : ℕ) : ℤ) →ₗ[R] Q.X ((n + 2 : ℕ) : ℤ)
  eqn : (F.f ((n + 1 : ℕ) : ℤ)).hom = (Q.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom.comp hi +
    lo.comp (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom

structure DownHomPair (F : P ⟶ Q) (n : ℕ) where
  hi : P.X (Int.negSucc n) →ₗ[R] Q.X (-(n : ℤ))
  lo : P.X (Int.negSucc (n + 1)) →ₗ[R] Q.X (Int.negSucc n)
  eqn : (F.f (Int.negSucc n)).hom =
    (Q.d (-(n : ℤ)) (Int.negSucc n)).hom.comp hi +
      lo.comp (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

structure ExactProjectiveCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  finite : ∀ i, Module.Finite R (K.X i)
  projective : ∀ i, Module.Projective R (K.X i)
  exactAt : ∀ i, K.ExactAt i

theorem chain_exactAt_iff (P : ChainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    P.ExactAt i ↔ LinearMap.range (P.d (i + 1) i).hom =
      LinearMap.ker (P.d i (i - 1)).hom := by
  rw [P.exactAt_iff' (i := i + 1) (j := i) (k := i - 1)
      (ChainComplex.prev ℤ i) (ChainComplex.next ℤ i),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  rfl

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CokernelLinearCongr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable {R M N M' N' : Type u} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

def cokernelLinearCongr (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (a : M ≃ₗ[R] M') (b : N ≃ₗ[R] N') (h : b.toLinearMap.comp f = g.comp a.toLinearMap) :
    (N ⧸ LinearMap.range f) ≃ₗ[R] (N' ⧸ LinearMap.range g) :=
  Submodule.Quotient.equiv _ _ b (by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨a z, (DFunLike.congr_fun h z).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨f (a.symm z), ⟨a.symm z, rfl⟩, ?_⟩
      change b.toLinearMap.comp f (a.symm z) = g z
      rw [h]
      simp)

@[simp]
theorem cokernelLinearCongr_mk (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (a : M ≃ₗ[R] M') (b : N ≃ₗ[R] N') (h : b.toLinearMap.comp f = g.comp a.toLinearMap)
    (x : N) :
    cokernelLinearCongr f g a b h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (b x) := rfl

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeExactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable {R Q₁ Q₀ Q₂ P₁ P₀ P₂ : Type*} [Ring R]
variable [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₀] [Module R Q₀]
variable [AddCommGroup Q₂] [Module R Q₂] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₂] [Module R P₂]

def coneBlock (dQ : Q₀ →ₗ[R] Q₂) (dP : P₀ →ₗ[R] P₂) (f : P₀ →ₗ[R] Q₂) :
    (Q₀ × P₀) →ₗ[R] (Q₂ × P₂) :=
  (dQ.coprod f).prod ((-dP).comp (LinearMap.snd R Q₀ P₀))

@[simp] theorem coneBlock_apply (dQ : Q₀ →ₗ[R] Q₂) (dP : P₀ →ₗ[R] P₂)
    (f : P₀ →ₗ[R] Q₂) (x : Q₀) (y : P₀) :
    coneBlock dQ dP f (x, y) = (dQ x + f y, -dP y) := rfl

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_SplitModules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

universe u

variable {R M N : Type u} [Ring R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

theorem finiteProjective_injective [Module.Injective R R]
    [Module.Finite R M] [Module.Projective R M] : Module.Injective R M where
  out := by
    intro X Y _ _ _ _ f hf g
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
    obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
    obtain ⟨g', hg'⟩ := Module.Injective.extension_property R (Fin n → R) X Y f hf (s.comp g)
    refine ⟨p.comp g', ?_⟩
    intro x
    change p (g' (f x)) = g x
    rw [show g' (f x) = s (g x) from DFunLike.congr_fun hg' x]
    exact DFunLike.congr_fun hs (g x)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeQuotientMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.ConeQuotientMap

universe u

variable {R P₁ P₀ I Q₁ Q₀ L : Type u} [Ring R]
variable [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₀] [Module R P₀]
variable [AddCommGroup I] [Module R I] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup L] [Module R L]

variable (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] I) (b : Q₁ →ₗ[R] Q₀) (f : P₀ →ₗ[R] Q₀)

abbrev Source := P₀ ⧸ LinearMap.range e
abbrev Target := Q₀ ⧸ LinearMap.range b
abbrev Cone := (Q₀ × I) ⧸ LinearMap.range (coneBlock b d f)

variable (i : Source e →ₗ[R] Target b)
variable (p : Target b →ₗ[R] L)
variable (hf : (LinearMap.range b).mkQ.comp f = i.comp (LinearMap.range e).mkQ)
variable (hex : Function.Exact i p)

def kernelInclusion : I →ₗ[R] Cone d b f :=
  (LinearMap.range (coneBlock b d f)).mkQ.comp (LinearMap.inr R Q₀ I)

def quotientMap : Cone d b f →ₗ[R] L :=
  (LinearMap.range (coneBlock b d f)).liftQ
    ((p.comp (LinearMap.range b).mkQ).comp (LinearMap.fst R Q₀ I)) (by
      rintro _ ⟨⟨q, x⟩, rfl⟩
      change p ((LinearMap.range b).mkQ (b q + f x)) = 0
      rw [map_add, show (LinearMap.range b).mkQ (b q) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨q, rfl⟩, zero_add]
      rw [show (LinearMap.range b).mkQ (f x) = i ((LinearMap.range e).mkQ x) from
        DFunLike.congr_fun hf x]
      exact (hex _).mpr ⟨_, rfl⟩)

@[simp]
theorem quotientMap_mk (x : Q₀) (y : I) :
    quotientMap e d b f i p hf hex (Submodule.Quotient.mk (x, y)) =
      p (Submodule.Quotient.mk x) := rfl

@[simp]
theorem kernelInclusion_apply (y : I) :
    kernelInclusion d b f y = Submodule.Quotient.mk (0, y) := rfl

include hf in

theorem kernelInclusion_injective (hi : Function.Injective i)
    (hed : d.comp e = 0) : Function.Injective (kernelInclusion d b f) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro y hy
  obtain ⟨⟨q, x⟩, hqx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
  have hx : i ((LinearMap.range e).mkQ x) = 0 := by
    have h := congrArg ((LinearMap.range b).mkQ) (congrArg Prod.fst hqx)
    change (LinearMap.range b).mkQ (b q + f x) = (LinearMap.range b).mkQ 0 at h
    rw [map_add, show (LinearMap.range b).mkQ (b q) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨q, rfl⟩, zero_add, map_zero] at h
    rw [show (LinearMap.range b).mkQ (f x) = i ((LinearMap.range e).mkQ x) from
      DFunLike.congr_fun hf x] at h
    exact h
  have hx0 : (LinearMap.range e).mkQ x = 0 := hi (by simpa only [map_zero] using hx)
  obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
  have hy' := congrArg Prod.snd hqx
  change -d x = y at hy'
  rw [← hz, show d (e z) = 0 from DFunLike.congr_fun hed z, neg_zero] at hy'
  exact hy'.symm

theorem quotientMap_surjective (hp : Function.Surjective p) :
    Function.Surjective (quotientMap e d b f i p hf hex) := by
  intro z
  obtain ⟨x, rfl⟩ := hp z
  obtain ⟨x, rfl⟩ := (LinearMap.range b).mkQ_surjective x
  exact ⟨Submodule.Quotient.mk (x, 0), rfl⟩

theorem exact : Function.Exact (kernelInclusion d b f) (quotientMap e d b f i p hf hex) := by
  intro z
  obtain ⟨⟨q, y⟩, rfl⟩ := (LinearMap.range (coneBlock b d f)).mkQ_surjective z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (hex ((LinearMap.range b).mkQ q)).mp hz
    obtain ⟨x, rfl⟩ := (LinearMap.range e).mkQ_surjective x
    have hb : q - f x ∈ LinearMap.range b := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (LinearMap.range b).mkQ (q - f x) = 0
      rw [map_sub, show (LinearMap.range b).mkQ (f x) = i ((LinearMap.range e).mkQ x) from
        DFunLike.congr_fun hf x, hx, sub_self]
    obtain ⟨q', hq'⟩ := hb
    refine ⟨y + d x, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨(-q', -x), ?_⟩
    apply Prod.ext
    · change b (-q') + f (-x) = 0 - q
      rw [map_neg, map_neg, hq']
      abel
    · change -d (-x) = (y + d x) - y
      rw [map_neg, neg_neg]
      abel
  · rintro ⟨y', hy'⟩
    rw [← hy']
    change p ((LinearMap.range b).mkQ 0) = 0
    simp

end ArExplicit.ConeQuotientMap

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

theorem cochain_adjacent_exact {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveCochain K) (i : ℤ) :
    Function.Exact (K.d i (i + 1)).hom (K.d (i + 1) ((i + 1) + 1)).hom := by
  have h := hK.exactAt (i + 1)
  rw [K.exactAt_iff' (i := i) (j := i + 1) (k := (i + 1) + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact LinearMap.exact_iff.mpr h.symm

end ArExplicit

end

end OAI
end


