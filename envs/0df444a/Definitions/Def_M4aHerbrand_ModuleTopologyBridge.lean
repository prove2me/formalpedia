-- Prove2me | Definitions.Def_M4aHerbrand_ModuleTopologyBridge
-- name    : M4aHerbrand_ModuleTopologyBridge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/e6904651-55f1-5510-9fe8-d6200540b6e4
-- title:
--   Module topologies on adele rings; conjugation automorphisms
-- statement:
--   This module collects facts about the module topology (Mathlib's `IsModuleTopology`, the infimum of the topologies making addition and scalar multiplication continuous) in two situations: change of scalar ring, and adele rings.
--
--   The transfer lemmas come first. `IsModuleTopology.of_continuousSMul_iff` states that if two scalar actions, of $R$ and of $S$, on an additive type $A$ have the property that for every topology on $A$ continuity of the $R$-action is equivalent to continuity of the $S$-action, then the $R$-module topology hypothesis transfers to $S$; `IsModuleTopology.of_smul_eq` says the predicate only depends on the scalar multiplication function, so two pointwise equal `SMul` structures give the same conclusion. Next, `smulFst` and `smulSnd` define actions of a product ring $R_1 \times R_2$ on $A$ by letting a pair act through its first, respectively second, component; `continuousSMul_smulFst_iff` and `continuousSMul_smulSnd_iff` show that, for any topology on $A$, continuity of such an action is equivalent to continuity of the original one-factor action, and `isModuleTopology_smulFst`, `isModuleTopology_smulSnd` deduce that the module topology for one factor is the module topology for the product ring acting through that factor. `continuous_algEquiv` states that for a topological commutative semiring $R$ and an $R$-algebra $A$ with continuous addition carrying the $R$-module topology, every $R$-algebra automorphism $e$ of $A$ is continuous.
--
--   In the adelic part, $R \subseteq E$ and $S \subseteq F$ are Dedekind domains with fraction fields $E$, $F$ and $F$ is an $E$-algebra. Given an algebra structure of $\mathbb{A}_{R,E}$ on $\mathbb{A}_{S,F}$ and an $\mathbb{A}_{R,E}$-algebra isomorphism $te \colon \mathbb{A}_{R,E} \otimes_E F \to \mathbb{A}_{S,F}$, the definition `conjAct` attaches to an $E$-algebra automorphism $\sigma$ of $F$ the ring automorphism of $\mathbb{A}_{S,F}$ obtained by conjugating $\mathrm{id} \otimes \sigma$ by $te$, i.e. $te \circ (\mathrm{id} \otimes \sigma) \circ te^{-1}$, viewed as a `RingEquiv`. `continuous_conjAct` asserts that when $\mathbb{A}_{S,F}$ carries the $\mathbb{A}_{R,E}$-module topology each such automorphism is continuous. Finally `isModuleTopology_adeleRing_prodMap` takes ring homomorphisms $\beta_\infty$ on infinite adeles and $\beta_f$ on finite adeles, assumes that $\mathbb{A}_{E,\infty}$-module topology on $\mathbb{A}_{F,\infty}$ and the finite-adelic analogue hold for the algebra structures induced by $\beta_\infty$, $\beta_f$, and concludes that $\mathbb{A}_{S,F}$ carries the module topology over $\mathbb{A}_{R,E}$ for the algebra structure induced by the product map $\beta_\infty \times \beta_f$.
--
--   **Relation to Mathlib.** `IsModuleTopology`, `AdeleRing`, `InfiniteAdeleRing` and `FiniteAdeleRing` are Mathlib notions; everything here supplements them with transfer lemmas along changes of scalar ring and with the product decomposition $\mathbb{A} = \mathbb{A}_\infty \times \mathbb{A}_f$. The declarations named `IsModuleTopology.of_continuousSMul_iff` and `IsModuleTopology.of_smul_eq` live in the project namespace and are not part of Mathlib's `IsModuleTopology` API.
--
--   **Where it is used.** These bridging results serve adelic descent arguments, where the adeles of an extension $F/E$ are identified with $\mathbb{A}_E \otimes_E F$ and the resulting Galois action on $\mathbb{A}_F$ must be known to be continuous; the module-topology criterion reduces this to the infinite and finite places separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_ModuleTopologyBridge.lean

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct

section Transfer

variable {R S A : Type*} [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace A] [Add A]

theorem IsModuleTopology.of_continuousSMul_iff [SMul R A] [SMul S A]
    (h : ∀ t : TopologicalSpace A, @ContinuousSMul R A _ _ t ↔ @ContinuousSMul S A _ _ t)
    [hR : IsModuleTopology R A] : IsModuleTopology S A := by
  refine ⟨?_⟩
  rw [eq_moduleTopology R A]
  show sInf _ = sInf _
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  exact and_congr_left' (h t)

theorem IsModuleTopology.of_smul_eq (i₁ i₂ : SMul R A)
    (h : ∀ (r : R) (a : A), i₁.smul r a = i₂.smul r a)
    (h₁ : @IsModuleTopology R _ A _ i₁ _) : @IsModuleTopology R _ A _ i₂ _ := by
  have : i₁ = i₂ := by
    cases i₁; cases i₂; congr; funext r a; exact h r a
  subst this
  exact h₁

end Transfer

section PullBack

variable {R₁ R₂ A : Type*} [TopologicalSpace R₁] [TopologicalSpace R₂]

@[reducible] def smulFst [SMul R₁ A] : SMul (R₁ × R₂) A := ⟨fun p a => p.1 • a⟩

@[reducible] def smulSnd [SMul R₂ A] : SMul (R₁ × R₂) A := ⟨fun p a => p.2 • a⟩

theorem continuousSMul_smulFst_iff [SMul R₁ A] [Zero R₂] (t : TopologicalSpace A) :
    @ContinuousSMul (R₁ × R₂) A smulFst _ t ↔ @ContinuousSMul R₁ A _ _ t := by
  letI : TopologicalSpace A := t
  letI : SMul (R₁ × R₂) A := smulFst
  constructor
  · intro h
    have hc : Continuous fun p : (R₁ × R₂) × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : R₁ × A => p.1 • p.2)
        = (fun p : (R₁ × R₂) × A => p.1 • p.2) ∘ fun p : R₁ × A => ((p.1, (0 : R₂)), p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩
  · intro h
    have hc : Continuous fun p : R₁ × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : (R₁ × R₂) × A => p.1 • p.2)
        = (fun p : R₁ × A => p.1 • p.2) ∘ fun p : (R₁ × R₂) × A => (p.1.1, p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩

theorem continuousSMul_smulSnd_iff [SMul R₂ A] [Zero R₁] (t : TopologicalSpace A) :
    @ContinuousSMul (R₁ × R₂) A smulSnd _ t ↔ @ContinuousSMul R₂ A _ _ t := by
  letI : TopologicalSpace A := t
  letI : SMul (R₁ × R₂) A := smulSnd
  constructor
  · intro h
    have hc : Continuous fun p : (R₁ × R₂) × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : R₂ × A => p.1 • p.2)
        = (fun p : (R₁ × R₂) × A => p.1 • p.2) ∘ fun p : R₂ × A => (((0 : R₁), p.1), p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩
  · intro h
    have hc : Continuous fun p : R₂ × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : (R₁ × R₂) × A => p.1 • p.2)
        = (fun p : R₂ × A => p.1 • p.2) ∘ fun p : (R₁ × R₂) × A => (p.1.2, p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩

theorem isModuleTopology_smulFst [Add A] [SMul R₁ A] [Zero R₂] [TopologicalSpace A]
    [IsModuleTopology R₁ A] :
    @IsModuleTopology (R₁ × R₂) _ A _ smulFst _ :=
  @IsModuleTopology.of_continuousSMul_iff R₁ (R₁ × R₂) A _ _ _ _ _ smulFst
    (fun t => (continuousSMul_smulFst_iff t).symm) _

theorem isModuleTopology_smulSnd [Add A] [SMul R₂ A] [Zero R₁] [TopologicalSpace A]
    [IsModuleTopology R₂ A] :
    @IsModuleTopology (R₁ × R₂) _ A _ smulSnd _ :=
  @IsModuleTopology.of_continuousSMul_iff R₂ (R₁ × R₂) A _ _ _ _ _ smulSnd
    (fun t => (continuousSMul_smulSnd_iff t).symm) _

end PullBack

section AlgEquiv

variable {R A : Type*} [CommSemiring R] [TopologicalSpace R] [Semiring A] [Algebra R A]
  [TopologicalSpace A] [IsModuleTopology R A] [ContinuousAdd A]

theorem continuous_algEquiv (e : A ≃ₐ[R] A) : Continuous e :=
  (IsModuleTopology.continuous_of_linearMap e.toLinearMap).congr fun _ => rfl

end AlgEquiv

section Adele

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

noncomputable def conjAct [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (σ : F ≃ₐ[E] F) : AdeleRing S F ≃+* AdeleRing S F :=
  (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te)).toRingEquiv

theorem continuous_conjAct [Algebra (AdeleRing R E) (AdeleRing S F)]
    [IsModuleTopology (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) (σ : F ≃ₐ[E] F) :
    Continuous (conjAct R E S F te σ) :=
  (continuous_algEquiv (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te))).congr
    fun _ => rfl

omit [Algebra E F] in

theorem isModuleTopology_adeleRing_prodMap
    (βi : InfiniteAdeleRing E →+* InfiniteAdeleRing F)
    (βf : FiniteAdeleRing R E →+* FiniteAdeleRing S F)
    (hi : letI := βi.toAlgebra; IsModuleTopology (InfiniteAdeleRing E) (InfiniteAdeleRing F))
    (hf : letI := βf.toAlgebra; IsModuleTopology (FiniteAdeleRing R E) (FiniteAdeleRing S F)) :
    letI : Algebra (AdeleRing R E) (AdeleRing S F) := (RingHom.prodMap βi βf).toAlgebra
    IsModuleTopology (AdeleRing R E) (AdeleRing S F) := by
  letI : Algebra (InfiniteAdeleRing E) (InfiniteAdeleRing F) := βi.toAlgebra
  letI : Algebra (FiniteAdeleRing R E) (FiniteAdeleRing S F) := βf.toAlgebra

  letI mi : Module (InfiniteAdeleRing E × FiniteAdeleRing R E) (InfiniteAdeleRing F) :=
    Module.compHom _ (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing R E))
  letI mf : Module (InfiniteAdeleRing E × FiniteAdeleRing R E) (FiniteAdeleRing S F) :=
    Module.compHom _ (RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing R E))
  have hi' : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E) (InfiniteAdeleRing F) :=
    IsModuleTopology.of_smul_eq smulFst _ (fun _ _ => rfl) isModuleTopology_smulFst
  have hf' : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E) (FiniteAdeleRing S F) :=
    IsModuleTopology.of_smul_eq smulSnd _ (fun _ _ => rfl) isModuleTopology_smulSnd
  have hprod : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E)
      (InfiniteAdeleRing F × FiniteAdeleRing S F) := IsModuleTopology.instProd
  exact IsModuleTopology.of_smul_eq _ _ (fun _ _ => rfl) hprod

end Adele

end M4aHerbrand.Bridge


