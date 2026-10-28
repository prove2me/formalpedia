-- Prove2me | Definitions.Def_OAIQ031A027
-- name    : OAIQ031A027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:58:07.770125+00:00
-- url     : https://prove2.me/theorems/6d34c856-f029-4b4b-85b1-fbcbd1f59b03
-- title:
--   Definitions bundle OAIQ031A027 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 71 declarations of OpenAI's Lean: 28 definitions, 1 inductive type or structure and 42 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.components`, `OAI.ArExplicit.CompleteComparison.downHomSequence`, `OAI.ArExplicit.CompleteComparison.downSequence`, `OAI.ArExplicit.CompleteComparison.fromPairs`, `OAI.ArExplicit.CompleteComparison.homComponents`, `OAI.ArExplicit.CompleteComparison.upHomSequence`, `OAI.ArExplicit.CompleteComparison.upSequence`, `OAI.ArExplicit.DualExactCochain`, `OAI.ArExplicit.ExternalTensor.scalarSummands`, `OAI.ArExplicit.FiniteLeftModule.FreeCover`, `OAI.ArExplicit.FiniteLeftModule.completeCochain`, `OAI.ArExplicit.FiniteLeftModule.completeCokernelEquiv`, `OAI.ArExplicit.FiniteLeftModule.completeComplex`, `OAI.ArExplicit.FiniteLeftModule.cosyzygies`, `OAI.ArExplicit.FiniteLeftModule.cosyzygy`, `OAI.ArExplicit.FiniteLeftModule.cover`, `OAI.ArExplicit.FiniteLeftModule.differential`, `OAI.ArExplicit.FiniteLeftModule.envelopeMap`, `OAI.ArExplicit.FiniteLeftModule.envelopeRank`, `OAI.ArExplicit.FiniteLeftModule.negativeDifferential`, `OAI.ArExplicit.FiniteLeftModule.negativeTerm`, `OAI.ArExplicit.FiniteLeftModule.positiveDifferential`, `OAI.ArExplicit.FiniteLeftModule.positiveTerm`, `OAI.ArExplicit.FiniteLeftModule.seam`, `OAI.ArExplicit.FiniteLeftModule.syzygies`, `OAI.ArExplicit.FiniteLeftModule.syzygy`, `OAI.ArExplicit.FiniteLeftModule.term`, `OAI.ArExplicit.StableHom.postcomp`, `OAI.ArExplicit.StableHom.precomp`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_CompleteComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteComparison.lean), [`AuslanderReiten_Complete_CompleteNullhomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteNullhomotopy.lean), [`AuslanderReiten_Complete_CompleteResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteResolution.lean), [`AuslanderReiten_Complete_CompleteShiftDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShiftDual.lean), [`AuslanderReiten_Complete_FiniteCompleteResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/FiniteCompleteResolution.lean), [`AuslanderReiten_Homology_LinearHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/LinearHomotopy.lean), [`AuslanderReiten_Resolutions_FiniteCochainResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteCochainResolution.lean), [`AuslanderReiten_Stable_StableHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHom.lean), [`AuslanderReiten_Tensor_ExternalTensorForget`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorForget.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A002`, `OAIQ031A003`, `OAIQ031A004`, `OAIQ031A005` and `OAIQ031A006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A044`, `OAIQ031A045`, `OAIQ031A047`, `OAIQ031A048` and `OAIQ031A056`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A002
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A004
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A006

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

namespace HomExactAt

variable {e : K →ₗ[R] L} {d : L →ₗ[R] M}

theorem projective [Module.Finite R Q] [Module.Projective R Q]
    (h : HomExactAt e d) (f : L →ₗ[R] Q) (hf : f.comp e = 0) :
    ∃ g : M →ₗ[R] Q, g.comp d = f := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R Q
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π (LinearMap.id : Q →ₗ[R] Q) hπ
  have coordinate_exists (i : Fin n) :
      ∃ g : M →ₗ[R] R, g.comp d = (LinearMap.proj i).comp (s.comp f) := by
    apply h
    ext z
    change (s (f (e z))) i = 0
    rw [show f (e z) = 0 from DFunLike.congr_fun hf z, map_zero]
    rfl
  choose g hg using coordinate_exists
  let G : M →ₗ[R] (Fin n → R) := LinearMap.pi g
  refine ⟨π.comp G, ?_⟩
  ext z
  have hz : G (d z) = s (f z) := by
    funext i
    exact DFunLike.congr_fun (hg i) z
  change π (G (d z)) = f z
  rw [hz]
  exact DFunLike.congr_fun hs (f z)

end HomExactAt

section ComparisonSteps

universe a b c

variable {U : Type a} [AddCommGroup U] [Module R U]
variable {V : Type b} [AddCommGroup V] [Module R V]
variable {W : Type c} [AddCommGroup W] [Module R W]

theorem extend_comparison_down [Module.Finite R W] [Module.Projective R W]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M) (hdual : HomExactAt e d)
    (e' : U →ₗ[R] V) (d' : V →ₗ[R] W) (hde' : d'.comp e' = 0)
    (f : K →ₗ[R] U) (g : L →ₗ[R] V) (hfg : e'.comp f = g.comp e) :
    ∃ h : M →ₗ[R] W, h.comp d = d'.comp g := by
  apply hdual.projective (d'.comp g)
  ext t
  change d' (g (e t)) = 0
  calc
    d' (g (e t)) = d' (e' (f t)) := congrArg d' (DFunLike.congr_fun hfg t).symm
    _ = 0 := DFunLike.congr_fun hde' (f t)

end ComparisonSteps

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

theorem ExactProjectiveComplex.exactAt_of_indices
    {P : ChainComplex (ModuleCat.{u} R) ℤ} (h : ExactProjectiveComplex P)
    {i j k : ℤ} (hi : i = j + 1) (hk : k = j - 1) :
    LinearMap.range (P.d i j).hom = LinearMap.ker (P.d j k).hom := by
  subst i
  subst k
  exact h.exactAt j

theorem TotallyAcyclicComplex.dualExact_of_indices
    {P : ChainComplex (ModuleCat.{u} R) ℤ} (h : TotallyAcyclicComplex P)
    {i j k : ℤ} (hi : i = j + 1) (hk : k = j - 1) :
    HomExactAt (P.d i j).hom (P.d j k).hom := by
  subst i
  subst k
  exact h.dualExact j

namespace CompleteComparison

variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

theorem exists_upStep (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (n : ℕ) (c : UpPair P Q n) :
    ∃ c' : UpPair P Q (n + 1), c'.lo = c.hi := by
  let := hP.projective (n + 2)
  have hex : LinearMap.range (Q.d (n + 2) (n + 1)).hom =
      LinearMap.ker (Q.d (n + 1) n).hom := by
    exact hQ.exactAt_of_indices (by omega) (by omega)
  obtain ⟨f, hf⟩ := extend_comparison_up
    (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom
    (differential_comp P _ _ _)
    (Q.d (n + 2) (n + 1)).hom (Q.d (n + 1) n).hom hex c.hi c.lo c.comm
  exact ⟨⟨c.hi, f, hf⟩, rfl⟩

noncomputable def upSequence (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) : (n : ℕ) → UpPair P Q n
  | 0 => c
  | n + 1 => Classical.choose (exists_upStep hP hQ n (upSequence hP hQ c n))

theorem upSequence_succ_lo (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) (n : ℕ) :
    (upSequence hP hQ c (n + 1)).lo = (upSequence hP hQ c n).hi :=
  Classical.choose_spec (exists_upStep hP hQ n (upSequence hP hQ c n))

theorem exists_downStep (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (n : ℕ) (c : DownPair P Q n) :
    ∃ c' : DownPair P Q (n + 1), c'.hi = c.lo := by
  let := hQ.finite (Int.negSucc (n + 1))
  let := hQ.projective (Int.negSucc (n + 1))
  have hd : HomExactAt (P.d (-(n : ℤ)) (Int.negSucc n)).hom
      (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom := by
    exact hP.dualExact_of_indices (by omega) (by omega)
  obtain ⟨f, hf⟩ := extend_comparison_down
    (P.d (-(n : ℤ)) (Int.negSucc n)).hom
    (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom hd
    (Q.d (-(n : ℤ)) (Int.negSucc n)).hom
    (Q.d (Int.negSucc n) (Int.negSucc (n + 1))).hom
    (differential_comp Q _ _ _) c.hi c.lo c.comm
  exact ⟨⟨c.lo, f, hf.symm⟩, rfl⟩

noncomputable def downSequence (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : DownPair P Q 0) : (n : ℕ) → DownPair P Q n
  | 0 => c
  | n + 1 => Classical.choose (exists_downStep hP hQ n (downSequence hP hQ c n))

theorem downSequence_succ_hi (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : DownPair P Q 0) (n : ℕ) :
    (downSequence hP hQ c (n + 1)).hi = (downSequence hP hQ c n).lo :=
  Classical.choose_spec (exists_downStep hP hQ n (downSequence hP hQ c n))

theorem exists_downStart (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) :
    ∃ d : DownPair P Q 0, d.hi = c.lo := by
  let := hQ.finite (-1)
  let := hQ.projective (-1)
  obtain ⟨f, hf⟩ := extend_comparison_down
    (P.d 1 0).hom (P.d 0 (-1)).hom
    (hP.dualExact_of_indices (by omega) (by omega))
    (Q.d 1 0).hom (Q.d 0 (-1)).hom
    (differential_comp Q _ _ _) c.hi c.lo c.comm
  exact ⟨⟨c.lo, f, hf.symm⟩, rfl⟩

noncomputable def components (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) (d : DownPair P Q 0) :
    (n : ℤ) → P.X n →ₗ[R] Q.X n
  | Int.ofNat n => (upSequence hP.toExactProjectiveComplex hQ c n).lo
  | Int.negSucc n => (downSequence hP hQ d n).lo

noncomputable def fromPairs (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (c : UpPair P Q 0) (d : DownPair P Q 0)
    (hd : d.hi = c.lo) : P ⟶ Q where
  f n := ModuleCat.ofHom (components hP hQ c d n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    cases j with
    | ofNat n =>
      change (Q.d (n + 1) n).hom.comp
          (upSequence hP.toExactProjectiveComplex hQ c (n + 1)).lo =
        (upSequence hP.toExactProjectiveComplex hQ c n).lo.comp (P.d (n + 1) n).hom
      rw [upSequence_succ_lo]
      exact (upSequence hP.toExactProjectiveComplex hQ c n).comm
    | negSucc n =>
      cases n with
      | zero =>
        change (Q.d 0 (-1)).hom.comp c.lo = d.lo.comp (P.d 0 (-1)).hom
        rw [← hd]
        exact d.comm
      | succ n =>
        change (Q.d (Int.negSucc n) (Int.negSucc (n + 1))).hom.comp
            (downSequence hP hQ d n).lo =
          (downSequence hP hQ d (n + 1)).lo.comp
            (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom
        rw [← downSequence_succ_hi]
        exact (downSequence hP hQ d (n + 1)).comm

theorem lift_cokernels (hP : TotallyAcyclicComplex P) (hQ : ExactProjectiveComplex Q)
    (u : Cokernel P 0 →ₗ[R] Cokernel Q 0) :
    ∃ F : P ⟶ Q,
      (LinearMap.range (Q.d 1 0).hom).mkQ.comp (F.f 0).hom =
        u.comp (LinearMap.range (P.d 1 0).hom).mkQ := by
  let := hP.projective 0
  let := hP.projective 1
  obtain ⟨f₀, f₁, hf₀, hf₁⟩ := lift_cokernel_map (P.d 1 0).hom (Q.d 1 0).hom u
  let c : UpPair P Q 0 := ⟨f₀, f₁, hf₁⟩
  obtain ⟨d, hd⟩ := exists_downStart hP hQ c
  exact ⟨fromPairs hP hQ c d hd, hf₀⟩

theorem cokernelMap_surjective (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) : Function.Surjective (fun F : P ⟶ Q => cokernelMap F 0) := by
  intro u
  obtain ⟨F, hF⟩ := lift_cokernels hP hQ u
  refine ⟨F, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d 1 0).hom) x
  exact DFunLike.congr_fun hF y

end CompleteComparison

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_LinearHomotopy
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem extend_homotopy_down [Module.Finite R Q₁] [Module.Projective R Q₁]
    (p₂ : P₂ →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] P₀) (hp : HomExactAt p₂ p₁)
    (q₃ : Q₃ →ₗ[R] Q₂) (q₂ : Q₂ →ₗ[R] Q₁) (hq : q₂.comp q₃ = 0)
    (f₂ : P₂ →ₗ[R] Q₂) (f₁ : P₁ →ₗ[R] Q₁)
    (hc : q₂.comp f₂ = f₁.comp p₂)
    (h₂ : P₂ →ₗ[R] Q₃) (h₁ : P₁ →ₗ[R] Q₂)
    (hh : f₂ = q₃.comp h₂ + h₁.comp p₂) :
    ∃ h₀ : P₀ →ₗ[R] Q₁, f₁ = q₂.comp h₁ + h₀.comp p₁ := by
  have hz : (f₁ - q₂.comp h₁).comp p₂ = 0 := by
    ext x
    have hc' : f₁ (p₂ x) = q₂ (f₂ x) := (DFunLike.congr_fun hc x).symm
    have hh' : f₂ x = q₃ (h₂ x) + h₁ (p₂ x) := DFunLike.congr_fun hh x
    have hq' : q₂ (q₃ (h₂ x)) = 0 := DFunLike.congr_fun hq (h₂ x)
    change f₁ (p₂ x) - q₂ (h₁ (p₂ x)) = 0
    rw [hc', hh', map_add, hq', zero_add, sub_self]
  obtain ⟨h₀, hh₀⟩ := hp.projective (f₁ - q₂.comp h₁) hz
  refine ⟨h₀, ?_⟩
  rw [hh₀]
  abel

theorem initial_homotopy_of_factorization
    [Module.Projective R P₁] [Module.Finite R Q₁] [Module.Projective R Q₁]
    (e : P₂ →ₗ[R] P₁) (d : P₁ →ₗ[R] P₀) (hd : HomExactAt e d)
    (e' : Q₃ →ₗ[R] Q₂) (f : P₁ →ₗ[R] Q₂)
    (a : (P₁ ⧸ LinearMap.range e) →ₗ[R] Q₁)
    (b : Q₁ →ₗ[R] (Q₂ ⧸ LinearMap.range e'))
    (hf : (LinearMap.range e').mkQ.comp f =
      b.comp (a.comp (LinearMap.range e).mkQ)) :
    ∃ (h₀ : P₀ →ₗ[R] Q₂) (h₁ : P₁ →ₗ[R] Q₃),
      f = e'.comp h₁ + h₀.comp d := by
  have ha : (a.comp (LinearMap.range e).mkQ).comp e = 0 := by
    ext x
    change a ((LinearMap.range e).mkQ (e x)) = 0
    rw [show (LinearMap.range e).mkQ (e x) = 0 by
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero]
  obtain ⟨A, hA⟩ := hd.projective (a.comp (LinearMap.range e).mkQ) ha
  obtain ⟨B, hB⟩ := Module.projective_lifting_property (LinearMap.range e').mkQ b
    (Submodule.mkQ_surjective _)
  have hz : (LinearMap.range e').mkQ.comp (f - (B.comp A).comp d) = 0 := by
    ext x
    have hf' : (LinearMap.range e').mkQ (f x) =
        b (a ((LinearMap.range e).mkQ x)) := DFunLike.congr_fun hf x
    have hB' : (LinearMap.range e').mkQ (B (A (d x))) = b (A (d x)) :=
      DFunLike.congr_fun hB (A (d x))
    have hA' : A (d x) = a ((LinearMap.range e).mkQ x) := DFunLike.congr_fun hA x
    change (LinearMap.range e').mkQ (f x - B (A (d x))) = 0
    rw [map_sub, hf', hB', hA', sub_self]
  obtain ⟨h₁, hh₁⟩ := lift_through_exact e' (LinearMap.range e').mkQ
    (Submodule.ker_mkQ _).symm (f - (B.comp A).comp d) hz
  exact ⟨B.comp A, h₁, by rw [hh₁, sub_add_cancel]⟩

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace ArExplicit

variable (R : Type u) [Ring R]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

variable {R M N}

theorem factorsThroughFiniteFree_iff_projective (f : M →ₗ[R] N) :
    FactorsThroughFiniteFree R M N f ↔ FactorsThroughFiniteProjective R M N f := by
  constructor
  · rintro ⟨P, hP, hRP, hfree, hfinite, i, p, h⟩
    exact ⟨P, hP, hRP, inferInstance, hfinite, i, p, h⟩
  · rintro ⟨P, hP, hRP, hprojective, hfinite, i, p, h⟩
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π (LinearMap.id : P →ₗ[R] P) hπ
    refine ⟨Fin n → R, inferInstance, inferInstance, inferInstance, inferInstance,
      s.comp i, p.comp π, ?_⟩
    ext x
    calc
      p (π (s (i x))) = p (i x) := congrArg p (DFunLike.congr_fun hs (i x))
      _ = f x := DFunLike.congr_fun h x

variable {L P : Type u} [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]

theorem FactorsThroughFiniteFree.postcomp {f : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) (g : N →ₗ[R] P) :
    FactorsThroughFiniteFree R M P (g.comp f) := by
  rcases hf with ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, p, rfl⟩
  exact ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, g.comp p, LinearMap.comp_assoc ..⟩

theorem FactorsThroughFiniteFree.precomp {f : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) (g : L →ₗ[R] M) :
    FactorsThroughFiniteFree R L N (f.comp g) := by
  rcases hf with ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, p, rfl⟩
  exact ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i.comp g, p, (LinearMap.comp_assoc ..).symm⟩

variable (R M N)

namespace StableHom

variable {R M N}

@[simp]
theorem classOf_eq_zero_iff (f : M →ₗ[R] N) :
    classOf R M N f = 0 ↔ FactorsThroughFiniteFree R M N f :=
  QuotientAddGroup.eq_zero_iff f

theorem classOf_eq_zero_iff_projective (f : M →ₗ[R] N) :
    classOf R M N f = 0 ↔ FactorsThroughFiniteProjective R M N f := by
  rw [classOf_eq_zero_iff, factorsThroughFiniteFree_iff_projective]

@[simp]
theorem classOf_eq_iff (f g : M →ₗ[R] N) :
    classOf R M N f = classOf R M N g ↔ FactorsThroughFiniteFree R M N (f - g) :=
  QuotientAddGroup.eq_iff_sub_mem

def postcomp (g : N →ₗ[R] P) : StableHom R M N →+ StableHom R M P :=
  QuotientAddGroup.map (projectiveMaps R M N) (projectiveMaps R M P)
    { toFun := fun f => g.comp f
      map_zero' := LinearMap.comp_zero g
      map_add' := by intros; ext x; simp }
    (fun _ hf => hf.postcomp g)

def precomp (g : L →ₗ[R] M) : StableHom R M N →+ StableHom R L N :=
  QuotientAddGroup.map (projectiveMaps R M N) (projectiveMaps R L N)
    { toFun := fun f => f.comp g
      map_zero' := LinearMap.zero_comp g
      map_add' := by intros; ext x; simp }
    (fun _ hf => hf.precomp g)

@[simp]
theorem postcomp_classOf (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    postcomp g (classOf R M N f) = classOf R M P (g.comp f) := by
  exact QuotientAddGroup.map_mk' _ _ _ _ _

@[simp]
theorem precomp_classOf (g : L →ₗ[R] M) (f : M →ₗ[R] N) :
    precomp g (classOf R M N f) = classOf R L N (f.comp g) := by
  exact QuotientAddGroup.map_mk' _ _ _ _ _

end StableHom

section CentralScalars

variable {R M N}
variable (k : Type u) [CommRing k] [Algebra k R]
variable [Module k N] [IsScalarTower k R N]

theorem FactorsThroughFiniteFree.smul {f : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) (a : k) :
    FactorsThroughFiniteFree R M N (a • f) := by
  rcases hf with ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, p, rfl⟩
  refine ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, i, a • p, ?_⟩
  ext x
  rfl

end CentralScalars

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteNullhomotopy
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem exists_upHomStep (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (n : ℕ) (c : UpHomPair F n) :
    ∃ c' : UpHomPair F (n + 1), c'.lo = c.hi := by
  let := hP.projective ((n + 2 : ℕ) : ℤ)
  obtain ⟨h, hh⟩ := extend_homotopy_up
    (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom (differential_comp P _ _ _)
    (Q.d ((n + 3 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom (Q.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom
    (hQ.exactAt_of_indices (by omega) (by omega))
    (F.f ((n + 2 : ℕ) : ℤ)).hom (F.f ((n + 1 : ℕ) : ℤ)).hom (comm_linear F _ _) c.hi c.lo c.eqn
  exact ⟨⟨c.hi, h, hh⟩, rfl⟩

noncomputable def upHomSequence (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (c : UpHomPair F 0) :
    (n : ℕ) → UpHomPair F n
  | 0 => c
  | n + 1 => Classical.choose (exists_upHomStep hP hQ F n (upHomSequence hP hQ F c n))

theorem upHomSequence_succ_lo (hP : ExactProjectiveComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (c : UpHomPair F 0) (n : ℕ) :
    (upHomSequence hP hQ F c (n + 1)).lo = (upHomSequence hP hQ F c n).hi :=
  Classical.choose_spec (exists_upHomStep hP hQ F n (upHomSequence hP hQ F c n))

theorem exists_downHomStep (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (n : ℕ) (c : DownHomPair F n) :
    ∃ c' : DownHomPair F (n + 1), c'.hi = c.lo := by
  let := hQ.finite (Int.negSucc (n + 1))
  let := hQ.projective (Int.negSucc (n + 1))
  obtain ⟨h, hh⟩ := extend_homotopy_down
    (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom
    (P.d (Int.negSucc (n + 1)) (Int.negSucc (n + 2))).hom
    (hP.dualExact_of_indices (by omega) (by omega))
    (Q.d (-(n : ℤ)) (Int.negSucc n)).hom
    (Q.d (Int.negSucc n) (Int.negSucc (n + 1))).hom
    (differential_comp Q _ _ _)
    (F.f (Int.negSucc n)).hom (F.f (Int.negSucc (n + 1))).hom
    (comm_linear F _ _) c.hi c.lo c.eqn
  exact ⟨⟨c.lo, h, hh⟩, rfl⟩

noncomputable def downHomSequence (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (c : DownHomPair F 0) :
    (n : ℕ) → DownHomPair F n
  | 0 => c
  | n + 1 => Classical.choose
      (exists_downHomStep hP hQ F n (downHomSequence hP hQ F c n))

theorem downHomSequence_succ_hi (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (c : DownHomPair F 0) (n : ℕ) :
    (downHomSequence hP hQ F c (n + 1)).hi = (downHomSequence hP hQ F c n).lo :=
  Classical.choose_spec (exists_downHomStep hP hQ F n (downHomSequence hP hQ F c n))

noncomputable def homComponents (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (c : UpHomPair F 0) (d : DownHomPair F 0) :
    (i j : ℤ) → (ComplexShape.down ℤ).Rel j i → (P.X i ⟶ Q.X j)
  | Int.ofNat n, j, hij => by
      change (n : ℤ) + 1 = j at hij
      subst j
      exact ModuleCat.ofHom (upHomSequence hP.toExactProjectiveComplex hQ F c n).lo
  | Int.negSucc n, j, hij => by
      have hj : j = -(n : ℤ) := by
        change Int.negSucc n + 1 = j at hij
        omega
      clear hij
      subst j
      exact ModuleCat.ofHom (downHomSequence hP hQ F d n).hi

theorem nullhomotopy_from_pairs_with_initial (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (c : UpHomPair F 0) (d : DownHomPair F 0)
    (hzero : (F.f 0).hom =
      (show P.X 0 →ₗ[R] Q.X 0 from (Q.d 1 0).hom.comp c.lo) +
      (show P.X 0 →ₗ[R] Q.X 0 from d.hi.comp (P.d 0 (-1)).hom)) :
    ∃ H : Homotopy F 0, H.hom (-1) 0 = ModuleCat.ofHom d.hi := by
  let h := homComponents hP hQ F c d
  have hF : F = Homotopy.nullHomotopicMap' h := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | ofNat n =>
      cases n with
      | zero =>
        rw [Homotopy.nullHomotopicMap'_f (k₂ := 1) (k₀ := -1) (by decide) (by decide)]
        apply ModuleCat.hom_ext
        change (F.f 0).hom =
          (show P.X 0 →ₗ[R] Q.X 0 from d.hi.comp (P.d 0 (-1)).hom) +
          (show P.X 0 →ₗ[R] Q.X 0 from (Q.d 1 0).hom.comp c.lo)
        rw [add_comm]
        exact hzero
      | succ n =>
        rw [Homotopy.nullHomotopicMap'_f (k₂ := ((n + 2 : ℕ) : ℤ)) (k₀ := (n : ℤ))
          (by change (n + 1 : ℕ) + (1 : ℤ) = (n + 2 : ℕ); omega)
          (by change (n : ℤ) + 1 = (n + 1 : ℕ); omega)]
        apply ModuleCat.hom_ext
        change (F.f ((n + 1 : ℕ) : ℤ)).hom =
          (upHomSequence hP.toExactProjectiveComplex hQ F c n).lo.comp
            (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom + (Q.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom.comp
              (upHomSequence hP.toExactProjectiveComplex hQ F c (n + 1)).lo
        rw [upHomSequence_succ_lo]
        exact (upHomSequence hP.toExactProjectiveComplex hQ F c n).eqn.trans (add_comm _ _)
    | negSucc n =>
      rw [Homotopy.nullHomotopicMap'_f (k₂ := -(n : ℤ)) (k₀ := Int.negSucc (n + 1))
        (by change Int.negSucc n + 1 = -(n : ℤ); omega)
        (by change Int.negSucc (n + 1) + 1 = Int.negSucc n; omega)]
      apply ModuleCat.hom_ext
      change (F.f (Int.negSucc n)).hom =
        (show P.X (Int.negSucc n) →ₗ[R] Q.X (Int.negSucc n) from
          (downHomSequence hP hQ F d (n + 1)).hi.comp
            (P.d (Int.negSucc n) (Int.negSucc (n + 1))).hom) +
            (Q.d (-(n : ℤ)) (Int.negSucc n)).hom.comp
              (downHomSequence hP hQ F d n).hi
      rw [downHomSequence_succ_hi, add_comm]
      exact (downHomSequence hP hQ F d n).eqn
  refine ⟨(Homotopy.ofEq hF).trans (Homotopy.nullHomotopy' h), ?_⟩
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.nullHomotopy'_hom,
    Pi.zero_apply, zero_add]
  rw [dite_eq_left (show (ComplexShape.down ℤ).Rel 0 (-1) by decide)]
  change homComponents hP hQ F c d (Int.negSucc 0) 0 (by decide) = ModuleCat.ofHom d.hi
  rfl

theorem nullhomotopy_of_initial_with_component (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (h₀ : P.X 0 →ₗ[R] Q.X 1) (hneg₁ : P.X (-1) →ₗ[R] Q.X 0)
    (hh : (F.f 0).hom = (Q.d 1 0).hom.comp h₀ + hneg₁.comp (P.d 0 (-1)).hom) :
    ∃ H : Homotopy F 0, H.hom (-1) 0 = ModuleCat.ofHom hneg₁ := by
  let := hP.projective 1
  let := hQ.finite (-1)
  let := hQ.projective (-1)
  obtain ⟨h₁, hh₁⟩ := extend_homotopy_up
    (P.d 1 0).hom (P.d 0 (-1)).hom (differential_comp P _ _ _)
    (Q.d 2 1).hom (Q.d 1 0).hom
    (hQ.exactAt_of_indices (by omega) (by omega))
    (F.f 1).hom (F.f 0).hom (comm_linear F _ _) h₀ hneg₁ hh
  obtain ⟨hneg₂, hhneg₂⟩ := extend_homotopy_down
    (P.d 0 (-1)).hom (P.d (-1) (-2)).hom
    (hP.dualExact_of_indices (by omega) (by omega))
    (Q.d 1 0).hom (Q.d 0 (-1)).hom (differential_comp Q _ _ _)
    (F.f 0).hom (F.f (-1)).hom (comm_linear F _ _) h₀ hneg₁ hh
  exact nullhomotopy_from_pairs_with_initial hP hQ F
    ⟨h₀, h₁, hh₁⟩ ⟨hneg₁, hneg₂, hhneg₂⟩ hh

theorem nullhomotopy_of_initial (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (h₀ : P.X 0 →ₗ[R] Q.X 1) (hneg₁ : P.X (-1) →ₗ[R] Q.X 0)
    (hh : (F.f 0).hom = (Q.d 1 0).hom.comp h₀ + hneg₁.comp (P.d 0 (-1)).hom) :
    Nonempty (Homotopy F 0) := by
  obtain ⟨H, _⟩ := nullhomotopy_of_initial_with_component hP hQ F h₀ hneg₁ hh
  exact ⟨H⟩

theorem nullhomotopy_of_factorization (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q)
    (hf : FactorsThroughFiniteProjective R (Cokernel P 0) (Cokernel Q 0)
      (cokernelMap F 0)) : Nonempty (Homotopy F 0) := by
  rcases hf with ⟨T, hT, hRT, hproj, hfinite, a, b, hab⟩
  let := hP.projective 0
  have hc : (LinearMap.range (Q.d 1 0).hom).mkQ.comp (F.f 0).hom =
      b.comp (a.comp (LinearMap.range (P.d 1 0).hom).mkQ) := by
    calc
      _ = (cokernelMap F 0).comp (LinearMap.range (P.d 1 0).hom).mkQ :=
        (cokernelMap_mkQ F 0).symm
      _ = (b.comp a).comp (LinearMap.range (P.d 1 0).hom).mkQ :=
        congrArg (fun u => u.comp (LinearMap.range (P.d 1 0).hom).mkQ) hab.symm
      _ = _ := LinearMap.comp_assoc _ _ _
  obtain ⟨hneg₁, h₀, hh⟩ := initial_homotopy_of_factorization
    (P.d 1 0).hom (P.d 0 (-1)).hom
    (hP.dualExact_of_indices (by omega) (by omega))
    (Q.d 1 0).hom (F.f 0).hom a b hc
  exact nullhomotopy_of_initial hP hQ F h₀ hneg₁ hh

theorem factorization_of_nullhomotopy (hP : ExactProjectiveComplex P)
    (F : P ⟶ Q) (h : Homotopy F 0) :
    FactorsThroughFiniteProjective R (Cokernel P 0) (Cokernel Q 0) (cokernelMap F 0) := by
  have hh := h.comm 0
  rw [dNext_eq h.hom (i' := -1) (by decide),
    prevD_eq h.hom (j' := 1) (by decide), HomologicalComplex.zero_f_apply, add_zero] at hh
  have hh' : (F.f 0).hom = (Q.d 1 0).hom.comp (h.hom 0 1).hom +
      (h.hom (-1) 0).hom.comp (P.d 0 (-1)).hom := by
    rw [add_comm]
    exact congrArg (fun f : P.X 0 ⟶ Q.X 0 => f.hom) hh
  obtain ⟨a, b, hab⟩ := factorization_of_initial_homotopy
    (P.d 1 0).hom (P.d 0 (-1)).hom (differential_comp P _ _ _)
    (Q.d 1 0).hom (F.f 0).hom (cokernelMap F 0) (cokernelMap_mkQ F 0).symm
    (h.hom (-1) 0).hom (h.hom 0 1).hom hh'
  exact ⟨P.X (-1), inferInstance, inferInstance, hP.projective (-1), hP.finite (-1), a, b, hab⟩

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShiftDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

def DualExactCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ i, HomExactAt (K.d (i - 1) i).hom (K.d i (i + 1)).hom

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_FiniteCompleteResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

attribute [instance] FiniteLeftModule.scalar FiniteLeftModule.tower FiniteLeftModule.finite

namespace FiniteLeftModule

variable {k R} [Module.Finite k R]

structure FreeCover (M : FiniteLeftModule k R) where
  rank : ℕ
  map : (Fin rank → R) →ₗ[R] M.carrier
  surjective : Function.Surjective map

noncomputable def cover (M : FiniteLeftModule k R) : FreeCover M := by
  let := Module.Finite.of_restrictScalars_finite k R M.carrier
  let h := Module.Finite.exists_fin' R M.carrier
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

noncomputable def syzygy (M : FiniteLeftModule k R) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (LinearMap.ker M.cover.map)
  scalar := inferInstance
  tower := inferInstance
  finite := Module.Finite.of_injective
    ((LinearMap.ker M.cover.map).subtype.restrictScalars k) Subtype.val_injective

noncomputable def syzygies (M : FiniteLeftModule k R) : ℕ → FiniteLeftModule k R
  | 0 => M
  | n + 1 => (syzygies M n).syzygy

noncomputable def envelopeRank (M : FiniteLeftModule k R) : ℕ :=
  Module.finrank k M.carrier

noncomputable def envelopeMap (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    M.carrier →ₗ[R] (Fin M.envelopeRank → R) := τ.finiteFreeEmbedding

theorem envelopeMap_injective (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    Function.Injective (M.envelopeMap τ) := τ.finiteFreeEmbedding_injective

noncomputable def cosyzygy (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    FiniteLeftModule k R where
  carrier := ModuleCat.of R ((Fin M.envelopeRank → R) ⧸ LinearMap.range (M.envelopeMap τ))
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance

noncomputable def cosyzygies (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    ℕ → FiniteLeftModule k R
  | 0 => M
  | n + 1 => (cosyzygies τ M n).cosyzygy τ

noncomputable abbrev positiveTerm (M : FiniteLeftModule k R) (n : ℕ) :=
  Fin (M.syzygies n).cover.rank → R

noncomputable def positiveDifferential (M : FiniteLeftModule k R) (n : ℕ) :
    M.positiveTerm (n + 1) →ₗ[R] M.positiveTerm n :=
  (LinearMap.ker (M.syzygies n).cover.map).subtype.comp (M.syzygies (n + 1)).cover.map

theorem positiveDifferential_range (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.range (M.positiveDifferential n) = LinearMap.ker (M.syzygies n).cover.map := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((M.syzygies (n + 1)).cover.map y).property
  · intro hx
    obtain ⟨y, hy⟩ := (M.syzygies (n + 1)).cover.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

theorem positiveDifferential_kernel (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.ker (M.positiveDifferential n) = LinearMap.ker (M.syzygies (n + 1)).cover.map := by
  ext x
  change ((M.syzygies (n + 1)).cover.map x).val = 0 ↔ (M.syzygies (n + 1)).cover.map x = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem positiveDifferential_exact (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.range (M.positiveDifferential (n + 1)) =
      LinearMap.ker (M.positiveDifferential n) := by
  rw [positiveDifferential_range, positiveDifferential_kernel]

noncomputable abbrev negativeTerm (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) (n : ℕ) :=
  Fin (M.cosyzygies τ n).envelopeRank → R

noncomputable def negativeDifferential (τ : FrobeniusTrace k R)
    (M : FiniteLeftModule k R) (n : ℕ) :
    M.negativeTerm τ n →ₗ[R] M.negativeTerm τ (n + 1) :=
  ((M.cosyzygies τ (n + 1)).envelopeMap τ).comp
    (LinearMap.range ((M.cosyzygies τ n).envelopeMap τ)).mkQ

theorem negativeDifferential_range (τ : FrobeniusTrace k R)
    (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.range (M.negativeDifferential τ n) =
      LinearMap.range ((M.cosyzygies τ (n + 1)).envelopeMap τ) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      (LinearMap.range ((M.cosyzygies τ n).envelopeMap τ)) y
    exact ⟨z, rfl⟩

theorem negativeDifferential_kernel (τ : FrobeniusTrace k R)
    (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.ker (M.negativeDifferential τ n) =
      LinearMap.range ((M.cosyzygies τ n).envelopeMap τ) := by
  ext x
  change ((M.cosyzygies τ (n + 1)).envelopeMap τ)
    ((LinearMap.range ((M.cosyzygies τ n).envelopeMap τ)).mkQ x) = 0 ↔ _
  exact (map_eq_zero_iff _ ((M.cosyzygies τ (n + 1)).envelopeMap_injective τ)).trans
    (Submodule.Quotient.mk_eq_zero _)

theorem negativeDifferential_exact (τ : FrobeniusTrace k R)
    (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.range (M.negativeDifferential τ n) =
      LinearMap.ker (M.negativeDifferential τ (n + 1)) := by
  rw [negativeDifferential_range, negativeDifferential_kernel]

noncomputable def seam (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    M.positiveTerm 0 →ₗ[R] M.negativeTerm τ 0 :=
  (M.envelopeMap τ).comp M.cover.map

theorem seam_range (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    LinearMap.range (M.seam τ) = LinearMap.range (M.envelopeMap τ) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := M.cover.surjective y
    exact ⟨z, rfl⟩

theorem seam_kernel (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    LinearMap.ker (M.seam τ) = LinearMap.ker M.cover.map := by
  ext x
  exact map_eq_zero_iff _ (M.envelopeMap_injective τ)

noncomputable def term (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) : ℤ → ModuleCat.{u} R
  | Int.ofNat n => ModuleCat.of R (M.positiveTerm n)
  | Int.negSucc n => ModuleCat.of R (M.negativeTerm τ n)

noncomputable def differential (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    (i : ℤ) → M.term τ (i + 1) ⟶ M.term τ i
  | Int.ofNat n => ModuleCat.ofHom (M.positiveDifferential n)
  | Int.negSucc 0 => ModuleCat.ofHom (M.seam τ)
  | Int.negSucc (n + 1) => ModuleCat.ofHom (M.negativeDifferential τ n)

theorem adjacent_exact (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) (i : ℤ) :
    LinearMap.range (M.differential τ (i + 1)).hom =
      LinearMap.ker (M.differential τ i).hom := by
  cases i with
  | ofNat n => exact M.positiveDifferential_exact n
  | negSucc n =>
    cases n with
    | zero =>
      change LinearMap.range (M.positiveDifferential 0) = LinearMap.ker (M.seam τ)
      rw [positiveDifferential_range, seam_kernel]
      rfl
    | succ n =>
      cases n with
      | zero =>
        change LinearMap.range (M.seam τ) = LinearMap.ker (M.negativeDifferential τ 0)
        rw [seam_range, negativeDifferential_kernel]
        rfl
      | succ n => exact M.negativeDifferential_exact τ n

theorem differential_square (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) (i : ℤ) :
    M.differential τ (i + 1) ≫ M.differential τ i = 0 := by
  apply ModuleCat.hom_ext
  exact LinearMap.range_le_ker_iff.mp (M.adjacent_exact τ i).le

noncomputable def completeComplex (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    ChainComplex (ModuleCat.{u} R) ℤ :=
  ChainComplex.of (M.term τ) (M.differential τ) (M.differential_square τ)

noncomputable def completeCokernelEquiv (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    CompleteComparison.Cokernel (M.completeComplex τ) 0 ≃ₗ[R] M.carrier := by
  change (M.positiveTerm 0 ⧸ LinearMap.range (M.positiveDifferential 0)) ≃ₗ[R] M.carrier
  exact (Submodule.quotEquivOfEq _ _ (M.positiveDifferential_range 0)).trans
    (M.cover.map.quotKerEquivOfSurjective M.cover.surjective)

end FiniteLeftModule

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteCochainResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace FiniteLeftModule

open CompleteComparison

variable {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]

noncomputable def completeCochain (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    CochainComplex (ModuleCat.{u} R) ℤ := cochainOfChain (M.completeComplex τ)

end FiniteLeftModule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorForget
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

abbrev scalarSummands (n : ℕ) (p : Diagonal n) : ModuleCat.{u} k :=
  ModuleCat.of k ((forgetComplex k A P).X p.val.1 ⊗[k] (forgetComplex k B Q).X p.val.2)

end ArExplicit.ExternalTensor

end

end OAI
end


