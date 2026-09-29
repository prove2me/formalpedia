-- Prove2me | Definitions.Def_ValuationSubring_CompletionDecompositionAction
-- name    : ValuationSubring_CompletionDecompositionAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/4be6402e-0f7d-55bc-895f-55630748abef
-- title:
--   Isometric decomposition-group action on a valuation completion
-- statement:
--   Throughout, $K$ is a field with a valuation subring $A \subseteq K$, and $F$ is a field with $K$ an $F$-algebra; $A$ carries its valuation $v_A$ (`A.valuation`) and its decomposition subgroup $D =$ `A.decompositionSubgroup F` inside $K \simeq_{\mathrm{alg}[F]} K$. The predicate [`ValuationSubring.DecompositionIsometric`](../def/ValuationSubring_CompletionDecompositionAction.html#L13) asserts exactly that $v_A(\sigma x) = v_A(x)$ for every $\sigma \in D$ and every $x \in K$, i.e. that the elements of the decomposition group are isometries for $v_A$.
--
--   On `WithVal A.valuation`, the copy of $K$ carrying the $v_A$-adic valued structure, the natural action of $D$ (transport of $\sigma$ through the identification with $K$) is registered as an action by ring automorphisms, `mulSemiringActionWithVal`, with `smul_withVal_def` recording that $\sigma \bullet x$ is the image of $x$ under $\sigma$. Under `DecompositionIsometric` it is shown that this action preserves the valuation (`valued_smul_withVal`), that each $\sigma$ acts continuously (`continuous_smul_withVal`), and hence — with the hypothesis taken as a `Fact` instance — that the action is by uniformly continuous maps, giving `UniformContinuousConstSMul`.
--
--   With that instance available, the scalar action of $D$ on the completion $\widehat{K}_{v_A} =$ `A.valuation.Completion`, obtained by continuous extension, is upgraded from a distributive to a ring-automorphism action (`mulSemiringActionCompletion`), and packaged as a group homomorphism `completionRingAut` from $D$ to $\mathrm{Aut}(\widehat{K}_{v_A})$ with `completionRingAut_apply` identifying its values with the scalar action. The characterising properties proved are: compatibility with the canonical embedding, $\sigma \bullet \iota(a) = \iota(\sigma a)$; invariance of the extended valuation, $\widehat v(\sigma \bullet x) = \widehat v(x)$; continuity of $x \mapsto \sigma \bullet x$; and uniqueness, in that any continuous ring endomorphism of $\widehat{K}_{v_A}$ agreeing with $\sigma$ on the image of $K$ equals $x \mapsto \sigma \bullet x$. Finally, when $K$ has characteristic zero so does $\widehat{K}_{v_A}$.
--
--   **Relation to Mathlib.** `DecompositionIsometric` is the project's own predicate; everything else builds on Mathlib's `ValuationSubring.decompositionSubgroup`, the valued type synonym `WithVal`, and `UniformSpace.Completion`. No new scalar action on the completion is introduced: the action used is Mathlib's canonical continuous extension, here supplied with the uniform-continuity instance and upgraded from `DistribMulAction` to `MulSemiringAction`.
--
--   **Where it is used.** For a valuation subring $A$ of $\overline{\mathbf{Q}}$ lying over a prime $p$, this equips the completion $\widehat{\overline{\mathbf{Q}}}_A$ — a complete non-archimedean field attached to $A$ without choosing an embedding into an algebraic closure of $\mathbf{Q}_p$ — with a continuous action of the decomposition group by ring automorphisms. That action is the one with respect to which $p$-adic rigid-analytic uniformisation of Jacobians of modular curves at $A$ is Galois-equivariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ValuationSubring_CompletionDecompositionAction.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MonoidWithZeroHom WithZeroTopology UniformSpace

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]

def DecompositionIsometric : Prop :=
  ∀ (σ : A.decompositionSubgroup F) (x : K),
    A.valuation ((σ : K ≃ₐ[F] K) x) = A.valuation x

variable {A F}

instance charZero_completion [CharZero K] : CharZero A.valuation.Completion :=
  charZero_of_injective_ringHom
    (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective

theorem smul_withVal_def (σ : A.decompositionSubgroup F) (x : WithVal A.valuation) :
    σ • x = WithVal.toVal A.valuation ((σ : K ≃ₐ[F] K) x.ofVal) := rfl

instance mulSemiringActionWithVal :
    MulSemiringAction (A.decompositionSubgroup F) (WithVal A.valuation) where
  one_smul x := by rw [smul_withVal_def]; rfl
  mul_smul σ τ x := by simp only [smul_withVal_def]; rfl
  smul_zero σ := by rw [smul_withVal_def, WithVal.ofVal_zero, map_zero]; rfl
  smul_add σ x y := by simp only [smul_withVal_def, WithVal.ofVal_add, map_add]; rfl
  smul_one σ := by rw [smul_withVal_def, WithVal.ofVal_one, map_one]; rfl
  smul_mul σ x y := by simp only [smul_withVal_def, WithVal.ofVal_mul, map_mul]; rfl

theorem valued_smul_withVal (h : A.DecompositionIsometric F) (σ : A.decompositionSubgroup F)
    (x : WithVal A.valuation) : Valued.v (σ • x) = Valued.v x := by
  rw [smul_withVal_def]
  change A.valuation ((σ : K ≃ₐ[F] K) x.ofVal) = A.valuation x.ofVal
  exact h σ _

theorem continuous_smul_withVal (h : A.DecompositionIsometric F) (σ : A.decompositionSubgroup F) :
    Continuous (fun x : WithVal A.valuation => σ • x) := by
  let f : WithVal A.valuation →+* WithVal A.valuation :=
    MulSemiringAction.toRingHom (A.decompositionSubgroup F) (WithVal A.valuation) σ
  change Continuous f
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  refine ((Valued.hasBasis_nhds_zero (WithVal A.valuation) A.ValueGroup).tendsto_iff
    (Valued.hasBasis_nhds_zero (WithVal A.valuation) A.ValueGroup)).mpr
    fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  have hres : Valued.v.restrict (f x) = Valued.v.restrict x :=
    (Valuation.restrict_inj _).mpr (valued_smul_withVal h σ x)
  rw [hres]
  exact hx

instance uniformContinuousConstSMul_withVal [h : Fact (A.DecompositionIsometric F)] :
    UniformContinuousConstSMul (A.decompositionSubgroup F) (WithVal A.valuation) :=
  ⟨fun σ => uniformContinuous_addMonoidHom_of_continuous
    (f := (MulSemiringAction.toRingHom (A.decompositionSubgroup F) (WithVal A.valuation) σ :
      WithVal A.valuation →+ WithVal A.valuation)) (continuous_smul_withVal h.out σ)⟩

section Completion

variable [h : Fact (A.DecompositionIsometric F)]

theorem smul_completion_coe (σ : A.decompositionSubgroup F) (a : K) :
    σ • ((a : K) : A.valuation.Completion) =
      (((σ : K ≃ₐ[F] K) a : K) : A.valuation.Completion) :=
  (Completion.coe_smul σ (WithVal.toVal A.valuation a)).symm

omit h in

theorem continuous_smul_completion (σ : A.decompositionSubgroup F) :
    Continuous (fun x : A.valuation.Completion => σ • x) :=
  continuous_const_smul σ

instance mulSemiringActionCompletion :
    MulSemiringAction (A.decompositionSubgroup F) A.valuation.Completion :=
  { (inferInstance : DistribMulAction (A.decompositionSubgroup F) A.valuation.Completion) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, ← Completion.coe_smul, smul_one]
    smul_mul := fun σ x y =>
      Completion.induction_on₂ x y
        (isClosed_eq ((continuous_fst.fun_mul continuous_snd).fun_const_smul (σ : A.decompositionSubgroup F))
          ((continuous_fst.fun_const_smul (σ : A.decompositionSubgroup F)).fun_mul
            (continuous_snd.fun_const_smul (σ : A.decompositionSubgroup F))))
        fun a b => by simp only [← Completion.coe_mul, ← Completion.coe_smul, smul_mul'] }

theorem valuation_smul_completion (σ : A.decompositionSubgroup F) (x : A.valuation.Completion) :
    Valued.v (σ • x) = Valued.v x := by
  rw [← Valuation.restrict_inj]
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((Valued.continuous_valuation (K := A.valuation.Completion)).comp
      (continuous_smul_completion σ)) (Valued.continuous_valuation (K := A.valuation.Completion))
  | ih a =>
    rw [Valuation.restrict_inj, ← Completion.coe_smul, Valued.valuedCompletion_apply,
      Valued.valuedCompletion_apply]
    exact valued_smul_withVal h.out σ a

theorem eq_smul_completion_of_continuous (σ : A.decompositionSubgroup F)
    (g : A.valuation.Completion →+* A.valuation.Completion) (hg : Continuous g)
    (hext : ∀ a : K, g ((a : K) : A.valuation.Completion) =
      (((σ : K ≃ₐ[F] K) a : K) : A.valuation.Completion)) (x : A.valuation.Completion) :
    g x = σ • x := by
  refine congrFun (Completion.ext hg (continuous_smul_completion σ) fun a => ?_) x
  refine (hext (WithVal.equiv A.valuation a)).trans ?_
  exact (smul_completion_coe σ _).symm

def completionRingAut :
    A.decompositionSubgroup F →* (A.valuation.Completion ≃+* A.valuation.Completion) :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup F) A.valuation.Completion

theorem completionRingAut_apply (σ : A.decompositionSubgroup F) (x : A.valuation.Completion) :
    completionRingAut σ x = σ • x := by
  simp only [completionRingAut, MulSemiringAction.toRingAut_apply,
    MulSemiringAction.toRingEquiv_apply_apply]

end Completion

end ValuationSubring

end


