-- Prove2me | Definitions.Def_InvariantsCompletion
-- name    : InvariantsCompletion
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/122c1969-a7bd-5ba7-b8d8-606743455fe4
-- title:
--   Invariants of adic completions along a finite group action
-- statement:
--   Throughout, $A$ and $B$ are commutative rings, $B$ an $A$-algebra, and $G$ a group acting on $B$ by ring automorphisms that commute with the $A$-action; $\mathfrak p$ is an ideal of $A$, maximal where needed. A first group of lemmas compares the two descriptions of the fibre over $\mathfrak p$: for a prime $Q$ of $B$, containing $\mathfrak p B=\mathfrak p\cdot{}$`map (algebraMap A B)` is equivalent to lying over $\mathfrak p$, and under $G$-invariance of $A$ in $B$ with $G$ finite such a $Q$ is maximal; `isMaximal_and_map_le_iff` identifies the index set $\{Q : Q$ maximal, $\mathfrak pB\le Q\}$ used for the semilocal decomposition with `𝔭.primesOver B`, and `exists_smul_eq_of_liesOver` records transitivity of $G$ on that set.
--
--   The first definition, `transportOf A B G g h` for $g\in G$ and $h : g\cdot\mathfrak P\le Q$, is the $A$-algebra map from the $\mathfrak P$-adic completion of $B$ to the $Q$-adic completion obtained by functoriality (`mapₐ`) from the $A$-algebra automorphism $b\mapsto g\cdot b$ of $B$; it sends $\mathrm{of}(b)$ to $\mathrm{of}(g\cdot b)$, and on an element fixed by $\mathrm{Stab}_G(\mathfrak P)$ it does not depend on which $g$ with $g\cdot\mathfrak P=Q$ is chosen (`transportOf_eq_of_fixed`).
--
--   In the remaining part $A$ is Noetherian, $B$ is module-finite and faithful over $A$, $G$ is finite with $A$ the $G$-invariants of $B$, $\mathfrak p$ is maximal and $\mathfrak P$ is a prime of $B$ over $\mathfrak p$. `invariantsCompletionHom` is the composite of the base-change map $\widehat{A}_{\mathfrak p}\to\widehat{B}_{\mathfrak pB}$ with the semilocal component at $\mathfrak P$, i.e. the $A$-algebra map $\widehat{A}_{\mathfrak p}\to\widehat{B}_{\mathfrak P}$ whose $n$-th level value on a class of a Cauchy sequence $a$ is $\mathrm{algebraMap}\,A\,B(a_n)\bmod\mathfrak P^n$. Its image consists of elements fixed by the induced action of $\mathrm{Stab}_G(\mathfrak P)$ on $\widehat{B}_{\mathfrak P}$ through `stabAut`; it is injective, and every fixed element is in the image. `invariantsCompletionEquiv` is the resulting $A$-algebra isomorphism of $\widehat{A}_{\mathfrak p}$ with `FixedPoints.subalgebra A (AdicCompletion 𝔓 B) (MulAction.stabilizer G 𝔓)`, and `invariantsCompletionRingEquiv` its underlying ring isomorphism. Supporting results include Noetherianness of $B$ and Artinianness of $B/\mathfrak pB$, the $G$-stability of the index set, the identification of the base-change map with $x\mapsto x\otimes 1$ followed by `tensorRingHom` together with its injectivity, level formulas for semilocal components and transports, and `mem_fixedPoints_iff`, which unfolds membership in the fixed-point subalgebra to invariance under all `stabAut` for elements of the stabiliser.
--
--   **Relation to Mathlib.** Mathlib provides the adic completion `AdicCompletion`, the invariance predicate `Algebra.IsInvariant` and `FixedPoints.subalgebra`; the semilocal decomposition of the $\mathfrak pB$-adic completion, the transport maps along group elements, and the identification of $\widehat{A}_{\mathfrak p}$ with the stabiliser-fixed points of $\widehat{B}_{\mathfrak P}$ are the project's own.
--
--   **Where it is used.** This is commutative-algebra input for the parts of the argument where a completion of a ring of invariants must be recognised inside a completion of the larger ring: it identifies the $\mathfrak p$-adic completion of $A=B^G$ with the subalgebra of elements of the $\mathfrak P$-adic completion of $B$ fixed by the stabiliser of $\mathfrak P$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_InvariantsCompletion.lean

import Definitions.Def_CompletionInvariants
import Definitions.Def_SemilocalAdicCompletion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u₁ u₂ u₃

open Pointwise
open scoped TensorProduct

namespace AdicCompletion

variable (A : Type u₁) (B : Type u₂) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type u₃) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable (𝔭 : Ideal A)

section FibreIndex

variable [𝔭.IsMaximal]

theorem liesOver_of_isPrime_of_map_le (Q : Ideal B) [hQp : Q.IsPrime]
    (hQ : 𝔭.map (algebraMap A B) ≤ Q) : Q.LiesOver 𝔭 := by
  constructor
  have h1 : 𝔭 ≤ Q.under A := Ideal.map_le_iff_le_comap.mp hQ
  have h2 : Q.under A ≠ ⊤ := Ideal.comap_ne_top _ hQp.ne_top
  exact ‹𝔭.IsMaximal›.eq_of_le h2 h1

omit [𝔭.IsMaximal] in
theorem under_eq_of_liesOver (Q : Ideal B) [h : Q.LiesOver 𝔭] :
    Q.comap (algebraMap A B) = 𝔭 := by
  rw [← Ideal.under_def]
  exact (Ideal.over_def Q 𝔭).symm

omit [𝔭.IsMaximal] in
theorem map_le_of_liesOver (Q : Ideal B) [Q.LiesOver 𝔭] :
    𝔭.map (algebraMap A B) ≤ Q :=
  Ideal.map_le_iff_le_comap.mpr (le_of_eq (under_eq_of_liesOver A B 𝔭 Q).symm)

variable [Finite G] [Algebra.IsInvariant A B G]

include G in
omit [SMulCommClass G A B] in
theorem isMaximal_of_isPrime_of_liesOver (Q : Ideal B) [Q.IsPrime] [Q.LiesOver 𝔭] :
    Q.IsMaximal := by
  haveI := Algebra.IsInvariant.isIntegral A B G
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) Q ?_
  rw [under_eq_of_liesOver A B 𝔭 Q]
  infer_instance

include G in
omit [SMulCommClass G A B] in

theorem isMaximal_and_map_le_iff (Q : Ideal B) :
    (Q.IsMaximal ∧ 𝔭.map (algebraMap A B) ≤ Q) ↔ Q ∈ 𝔭.primesOver B := by
  constructor
  · rintro ⟨hmax, hle⟩
    haveI := hmax.isPrime
    exact ⟨hmax.isPrime, liesOver_of_isPrime_of_map_le A B 𝔭 Q hle⟩
  · rintro ⟨hprime, hover⟩
    haveI := hprime
    haveI := hover
    exact ⟨isMaximal_of_isPrime_of_liesOver A B G 𝔭 Q, map_le_of_liesOver A B 𝔭 Q⟩

omit [𝔭.IsMaximal] in

theorem exists_smul_eq_of_liesOver (Q Q' : Ideal B) [Q.IsPrime] [Q.LiesOver 𝔭]
    [Q'.IsPrime] [Q'.LiesOver 𝔭] : ∃ g : G, Q' = g • Q := by
  refine Algebra.IsInvariant.exists_smul_of_under_eq A B G Q Q' ?_
  rw [← Ideal.over_def Q 𝔭, ← Ideal.over_def Q' 𝔭]

end FibreIndex

section Transport

theorem map_toAlgEquiv_le_of_smul_le {𝔓 Q : Ideal B} (g : G) (h : g • 𝔓 ≤ Q) :
    𝔓.map (MulSemiringAction.toAlgEquiv A B g : B →ₐ[A] B) ≤ Q := by
  refine le_trans (le_of_eq ?_) h
  rw [Ideal.pointwise_smul_def]
  rfl

noncomputable def transportOf (g : G) {𝔓 Q : Ideal B} (h : g • 𝔓 ≤ Q) :
    AdicCompletion 𝔓 B →ₐ[A] AdicCompletion Q B :=
  mapₐ 𝔓 Q (MulSemiringAction.toAlgEquiv A B g : B →ₐ[A] B)
    (map_toAlgEquiv_le_of_smul_le A B G g h)

theorem evalₐ_transportOf (g : G) {𝔓 Q : Ideal B} (h : g • 𝔓 ≤ Q) (n : ℕ)
    (x : AdicCompletion 𝔓 B) (z : B)
    (hz : Ideal.Quotient.mk (𝔓 ^ n) z = evalₐ 𝔓 n x) :
    evalₐ Q n (transportOf A B G g h x) = Ideal.Quotient.mk (Q ^ n) (g • z) := by
  rw [transportOf, evalₐ_mapₐ, ← hz, levelMapₐ_mk]
  rfl

@[simp]
theorem transportOf_of (g : G) {𝔓 Q : Ideal B} (h : g • 𝔓 ≤ Q) (b : B) :
    transportOf A B G g h (of 𝔓 B b) = of Q B (g • b) := by
  rw [transportOf, mapₐ_of]
  rfl

theorem transportOf_eq_of_fixed {𝔓 Q : Ideal B} (g g' : G) (hg : g • 𝔓 = Q)
    (hg' : g' • 𝔓 = Q) (y : AdicCompletion 𝔓 B)
    (hy : ∀ h : MulAction.stabilizer G 𝔓, stabAut A B G 𝔓 h y = y) :
    transportOf A B G g hg.le y = transportOf A B G g' hg'.le y := by
  have hmem : g'⁻¹ * g ∈ MulAction.stabilizer G 𝔓 := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hg, ← hg', inv_smul_smul]
  refine ext_evalₐ fun n => ?_
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ 𝔓 n y)
  rw [evalₐ_transportOf A B G g hg.le n y z hz,
    evalₐ_transportOf A B G g' hg'.le n y z hz]
  have h1 : Ideal.Quotient.mk (𝔓 ^ n) ((g'⁻¹ * g) • z) = Ideal.Quotient.mk (𝔓 ^ n) z := by
    have h0 := congrArg (evalₐ 𝔓 n) (hy ⟨g'⁻¹ * g, hmem⟩)
    rw [evalₐ_stabAut A B G 𝔓 _ n y z hz, ← hz] at h0
    exact h0
  have h2 := congrArg (levelMapₐ 𝔓 Q (MulSemiringAction.toAlgEquiv A B g' : B →ₐ[A] B)
    (map_toAlgEquiv_le_of_smul_le A B G g' hg'.le) n) h1
  rw [levelMapₐ_mk, levelMapₐ_mk] at h2
  have h3 : Ideal.Quotient.mk (Q ^ n) (g' • (g'⁻¹ * g) • z) =
      Ideal.Quotient.mk (Q ^ n) (g' • z) := h2
  rwa [← mul_smul, mul_inv_cancel_left] at h3

theorem map_algebraMap_le_smul {Q : Ideal B} (g : G)
    (hQ : 𝔭.map (algebraMap A B) ≤ Q) : 𝔭.map (algebraMap A B) ≤ g • Q := by
  rw [← smul_map_algebraMap A B G 𝔭 g, Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
  exact Ideal.map_mono hQ

theorem semilocalComponent_selfSmul (g : G) {Q : Ideal B}
    (hQ : 𝔭.map (algebraMap A B) ≤ Q)
    (x : AdicCompletion (𝔭.map (algebraMap A B)) B) :
    letI := selfCompletionMulSemiringAction A B G 𝔭
    semilocalComponent (𝔭.map (algebraMap A B)) (map_algebraMap_le_smul A B G 𝔭 g hQ)
        (g • x) =
      transportOf A B G g (le_refl (g • Q)) (semilocalComponent _ hQ x) := by
  letI := selfCompletionMulSemiringAction A B G 𝔭
  refine ext_evalₐ fun n => ?_
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ (𝔭.map (algebraMap A B)) n x)
  have hcomp : Ideal.Quotient.mk (Q ^ n) z =
      evalₐ Q n (semilocalComponent (𝔭.map (algebraMap A B)) hQ x) := by
    rw [semilocalComponent, evalₐ_mapₐ, ← hz, levelMapₐ_mk]
    rfl
  have hsmul : Ideal.Quotient.mk ((𝔭.map (algebraMap A B)) ^ n) (g • z) =
      evalₐ (𝔭.map (algebraMap A B)) n (g • x) := by
    rw [show (g • x : AdicCompletion (𝔭.map (algebraMap A B)) B) =
        stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) x from rfl,
      evalₐ_stabAut A B G _ _ n x z hz]
    rfl
  rw [semilocalComponent, evalₐ_mapₐ, ← hsmul, levelMapₐ_mk,
    evalₐ_transportOf A B G g (le_refl (g • Q)) n
      (semilocalComponent (𝔭.map (algebraMap A B)) hQ x) z hcomp]
  rfl

end Transport

end AdicCompletion

section SameUniverseHead

namespace AdicCompletion

variable (A : Type u₁) (B : Type u₁) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type u₃) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B]
variable [Algebra.IsInvariant A B G]
variable (𝔭 : Ideal A) [𝔭.IsMaximal]

include A in
omit [FaithfulSMul A B] in

theorem isNoetherianRing_of_finite_algebra : IsNoetherianRing B :=
  isNoetherian_of_tower A (inferInstance : IsNoetherian A B)

omit [IsNoetherianRing A] [FaithfulSMul A B] in

theorem isArtinianRing_quotient_map :
    IsArtinianRing (B ⧸ 𝔭.map (algebraMap A B)) := by
  letI : DivisionRing (A ⧸ 𝔭) := Ideal.Quotient.divisionRing 𝔭
  haveI : IsArtinianRing (A ⧸ 𝔭) := inferInstance
  haveI : Module.Finite A (B ⧸ 𝔭.map (algebraMap A B)) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ A (𝔭.map (algebraMap A B))).toLinearMap
      (Ideal.Quotient.mkₐ_surjective A _)
  haveI : IsArtinian A (B ⧸ 𝔭.map (algebraMap A B)) := by
    refine isArtinian_of_finite_of_smul_eq_zero 𝔭 ?_
    rintro i hi m
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [show i • (Ideal.Quotient.mk (𝔭.map (algebraMap A B)) b) =
        Ideal.Quotient.mk (𝔭.map (algebraMap A B)) (i • b) from
      (map_smul (Ideal.Quotient.mkₐ A (𝔭.map (algebraMap A B))) i b).symm,
      Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hi)
  exact isArtinian_of_tower A inferInstance

variable (𝔓 : Ideal B) [𝔓.IsPrime] [𝔓.LiesOver 𝔭]

include G in
omit [SMulCommClass G A B] [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B] in

theorem mem_index_self : 𝔓.IsMaximal ∧ 𝔭.map (algebraMap A B) ≤ 𝔓 :=
  (isMaximal_and_map_le_iff A B G 𝔭 𝔓).mpr ⟨inferInstance, inferInstance⟩

omit [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B] in

theorem smul_mem_index (g : G) {Q : Ideal B}
    (h : Q.IsMaximal ∧ 𝔭.map (algebraMap A B) ≤ Q) :
    (g • Q).IsMaximal ∧ 𝔭.map (algebraMap A B) ≤ g • Q := by
  haveI : Q.IsMaximal := h.1
  haveI hp : (g • Q).IsPrime := by
    rw [Ideal.pointwise_smul_def]
    refine Ideal.map_isPrime_of_surjective (f := MulSemiringAction.toRingHom G B g)
      (fun b => ⟨g⁻¹ • b, smul_inv_smul g b⟩) ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (fun x y hxy => by simpa using congrArg (fun t => g⁻¹ • t) hxy)]
    exact bot_le
  have hle : 𝔭.map (algebraMap A B) ≤ g • Q := map_algebraMap_le_smul A B G 𝔭 g h.2
  haveI : (g • Q).LiesOver 𝔭 := liesOver_of_isPrime_of_map_le A B 𝔭 (g • Q) hle
  exact ⟨isMaximal_of_isPrime_of_liesOver A B G 𝔭 (g • Q), hle⟩

omit [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B] [𝔭.IsMaximal] in

theorem completionBaseChangeHom_eq_tensor (x : AdicCompletion 𝔭 A) :
    completionBaseChangeHom B 𝔭 x = tensorRingHom B 𝔭 (x ⊗ₜ[A] 1) := by
  have h : of (𝔭.map (algebraMap A B)) B (1 : B) = 1 :=
    map_one (completionOfAlgHom B 𝔭)
  rw [tensorRingHom_tmul, h, mul_one]

omit [𝔭.IsMaximal] in
theorem completionBaseChangeHom_injective :
    Function.Injective (completionBaseChangeHom B 𝔭) := by
  intro x y hxy
  rw [completionBaseChangeHom_eq_tensor, completionBaseChangeHom_eq_tensor] at hxy
  exact Algebra.TensorProduct.includeLeft_injective (S := A)
    (FaithfulSMul.algebraMap_injective A B)
    ((tensorRingHom_bijective B 𝔭).injective hxy)

include G in

noncomputable def invariantsCompletionHom :
    AdicCompletion 𝔭 A →ₐ[A] AdicCompletion 𝔓 B :=
  ((semilocalComponent (𝔭.map (algebraMap A B))
      (mem_index_self A B G 𝔭 𝔓).2).restrictScalars A).comp
    (completionBaseChangeHom B 𝔭)

include G in
omit [SMulCommClass G A B] [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B] in
theorem evalₐ_invariantsCompletionHom (a : AdicCauchySequence 𝔭 A) (n : ℕ) :
    evalₐ 𝔓 n (invariantsCompletionHom A B G 𝔭 𝔓 (mk 𝔭 A a)) =
      Ideal.Quotient.mk (𝔓 ^ n) (algebraMap A B (a.val n)) := by
  show evalₐ 𝔓 n (semilocalComponent (𝔭.map (algebraMap A B))
      (mem_index_self A B G 𝔭 𝔓).2 (completionBaseChangeHom B 𝔭 (mk 𝔭 A a))) = _
  have hbc : Ideal.Quotient.mk ((𝔭.map (algebraMap A B)) ^ n)
      (algebraMap A B (a.val n)) =
      evalₐ (𝔭.map (algebraMap A B)) n (completionBaseChangeHom B 𝔭 (mk 𝔭 A a)) := by
    simp [completionBaseChangeHom, Algebra.ofId_apply]
  rw [semilocalComponent, evalₐ_mapₐ, ← hbc, levelMapₐ_mk]
  rfl

omit [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B] in

theorem stabAut_invariantsCompletionHom (h : MulAction.stabilizer G 𝔓)
    (x : AdicCompletion 𝔭 A) :
    stabAut A B G 𝔓 h (invariantsCompletionHom A B G 𝔭 𝔓 x) =
      invariantsCompletionHom A B G 𝔭 𝔓 x := by
  induction x using AdicCompletion.induction_on with
  | _ a =>
    refine ext_evalₐ fun n => ?_
    rw [evalₐ_stabAut A B G 𝔓 h n _ _
        (evalₐ_invariantsCompletionHom A B G 𝔭 𝔓 a n).symm,
      smul_algebraMap, evalₐ_invariantsCompletionHom]

omit [FaithfulSMul A B] in

theorem eq_of_component_eq_of_smul_eq
    (w w' : AdicCompletion (𝔭.map (algebraMap A B)) B)
    (hw : ∀ g : G, stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) w = w)
    (hw' : ∀ g : G, stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) w' = w')
    (h𝔓 : semilocalComponent (𝔭.map (algebraMap A B))
        (mem_index_self A B G 𝔭 𝔓).2 w =
      semilocalComponent (𝔭.map (algebraMap A B)) (mem_index_self A B G 𝔭 𝔓).2 w') :
    w = w' := by
  haveI := isNoetherianRing_of_finite_algebra A B
  haveI := isArtinianRing_quotient_map A B 𝔭
  apply semilocalPiHom_injective (𝔭.map (algebraMap A B))
  funext P
  obtain ⟨Q, hQ⟩ := P
  haveI : Q.IsPrime := hQ.1.isPrime
  haveI : Q.LiesOver 𝔭 := liesOver_of_isPrime_of_map_le A B 𝔭 Q hQ.2
  obtain ⟨g, hg⟩ := exists_smul_eq_of_liesOver A B G 𝔭 𝔓 Q
  subst hg
  show semilocalComponent _ hQ.2 w = semilocalComponent _ hQ.2 w'
  calc semilocalComponent _ hQ.2 w
      = semilocalComponent _ hQ.2
          (stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) w) := by rw [hw g]
    _ = transportOf A B G g (le_refl (g • 𝔓))
          (semilocalComponent _ (mem_index_self A B G 𝔭 𝔓).2 w) :=
        semilocalComponent_selfSmul A B G 𝔭 g (mem_index_self A B G 𝔭 𝔓).2 w
    _ = transportOf A B G g (le_refl (g • 𝔓))
          (semilocalComponent _ (mem_index_self A B G 𝔭 𝔓).2 w') := by rw [h𝔓]
    _ = semilocalComponent _ hQ.2
          (stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) w') :=
        (semilocalComponent_selfSmul A B G 𝔭 g (mem_index_self A B G 𝔭 𝔓).2 w').symm
    _ = semilocalComponent _ hQ.2 w' := by rw [hw' g]

omit [Finite G] [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B]
  [Algebra.IsInvariant A B G] in

theorem transportOf_one (J : Ideal B) (y : AdicCompletion J B) :
    transportOf A B G 1 ((one_smul G J).le) y = y := by
  refine ext_evalₐ fun n => ?_
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ J n y)
  rw [evalₐ_transportOf A B G 1 ((one_smul G J).le) n y z hz, one_smul, hz]

omit [Finite G] [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B]
  [Algebra.IsInvariant A B G] [𝔭.IsMaximal] in

theorem evalₐ_component_selfSmul (g : G) {Q : Ideal B}
    (hQ : 𝔭.map (algebraMap A B) ≤ Q)
    (x : AdicCompletion (𝔭.map (algebraMap A B)) B) (n : ℕ) (z : B)
    (hz : Ideal.Quotient.mk ((𝔭.map (algebraMap A B)) ^ n) z =
      evalₐ (𝔭.map (algebraMap A B)) n x) :
    evalₐ Q n (semilocalComponent (𝔭.map (algebraMap A B)) hQ
        (stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) x)) =
      Ideal.Quotient.mk (Q ^ n) (g • z) := by
  have hsmul : Ideal.Quotient.mk ((𝔭.map (algebraMap A B)) ^ n) (g • z) =
      evalₐ (𝔭.map (algebraMap A B)) n
        (stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) x) := by
    rw [evalₐ_stabAut A B G _ _ n x z hz]
    rfl
  rw [semilocalComponent, evalₐ_mapₐ, ← hsmul, levelMapₐ_mk]
  rfl

omit [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B] [𝔭.IsMaximal] in

theorem evalₐ_component {Q : Ideal B} (hQ : 𝔭.map (algebraMap A B) ≤ Q)
    (x : AdicCompletion (𝔭.map (algebraMap A B)) B) (n : ℕ) (z : B)
    (hz : Ideal.Quotient.mk ((𝔭.map (algebraMap A B)) ^ n) z =
      evalₐ (𝔭.map (algebraMap A B)) n x) :
    evalₐ Q n (semilocalComponent (𝔭.map (algebraMap A B)) hQ x) =
      Ideal.Quotient.mk (Q ^ n) z := by
  rw [semilocalComponent, evalₐ_mapₐ, ← hz, levelMapₐ_mk]
  rfl

include G in

theorem invariantsCompletionHom_injective :
    Function.Injective (invariantsCompletionHom A B G 𝔭 𝔓) := by
  intro x y hxy
  refine completionBaseChangeHom_injective A B 𝔭 ?_
  refine eq_of_component_eq_of_smul_eq A B G 𝔭 𝔓 _ _
    (fun g => selfCompletion_smul_completionBaseChangeHom A B G 𝔭 g x)
    (fun g => selfCompletion_smul_completionBaseChangeHom A B G 𝔭 g y) hxy

omit [FaithfulSMul A B] in

theorem exists_invariantsCompletionHom_eq (y : AdicCompletion 𝔓 B)
    (hy : ∀ h : MulAction.stabilizer G 𝔓, stabAut A B G 𝔓 h y = y) :
    ∃ x : AdicCompletion 𝔭 A, invariantsCompletionHom A B G 𝔭 𝔓 x = y := by
  haveI := isNoetherianRing_of_finite_algebra A B
  haveI := isArtinianRing_quotient_map A B 𝔭

  have hch : ∀ P : {Q : Ideal B // Q.IsMaximal ∧ 𝔭.map (algebraMap A B) ≤ Q},
      ∃ g : G, (P : Ideal B) = g • 𝔓 := by
    rintro ⟨Q, hQ⟩
    haveI : Q.IsPrime := hQ.1.isPrime
    haveI : Q.LiesOver 𝔭 := liesOver_of_isPrime_of_map_le A B 𝔭 Q hQ.2
    exact exists_smul_eq_of_liesOver A B G 𝔭 𝔓 Q
  choose gO hgO using hch
  set w : AdicCompletion (𝔭.map (algebraMap A B)) B :=
    (semilocalPiEquiv (𝔭.map (algebraMap A B))).symm
      (fun P => transportOf A B G (gO P) (hgO P).ge y) with hw
  have hwF : ∀ P : {Q : Ideal B // Q.IsMaximal ∧ 𝔭.map (algebraMap A B) ≤ Q},
      semilocalComponent (𝔭.map (algebraMap A B)) P.2.2 w =
        transportOf A B G (gO P) (hgO P).ge y := fun P =>
    congrFun ((semilocalPiEquiv (𝔭.map (algebraMap A B))).apply_symm_apply _) P

  have hwfix : ∀ g : G, stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) w = w := by
    intro g
    apply semilocalPiHom_injective (𝔭.map (algebraMap A B))
    funext P
    show semilocalComponent _ P.2.2 _ = semilocalComponent _ P.2.2 w
    rw [hwF P]
    refine ext_evalₐ fun n => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
      (evalₐ (𝔭.map (algebraMap A B)) n w)
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (evalₐ 𝔓 n y)

    set P' : {Q : Ideal B // Q.IsMaximal ∧ 𝔭.map (algebraMap A B) ≤ Q} :=
      ⟨g⁻¹ • (P : Ideal B), smul_mem_index A B G 𝔭 g⁻¹ P.2⟩ with hP'

    have h1 : Ideal.Quotient.mk ((g⁻¹ • (P : Ideal B)) ^ n) z =
        Ideal.Quotient.mk ((g⁻¹ • (P : Ideal B)) ^ n) (gO P' • u) := by
      have hc := congrArg (evalₐ (g⁻¹ • (P : Ideal B)) n) (hwF P')
      rw [evalₐ_component A B 𝔭 P'.2.2 w n z hz] at hc
      exact hc.trans (evalₐ_transportOf A B G (gO P') (hgO P').ge n y u hu)

    have h2 := congrArg (levelMapₐ (g⁻¹ • (P : Ideal B)) (P : Ideal B)
      (MulSemiringAction.toAlgEquiv A B g : B →ₐ[A] B)
      (map_toAlgEquiv_le_of_smul_le A B G g (smul_inv_smul g (P : Ideal B)).le) n) h1
    rw [levelMapₐ_mk, levelMapₐ_mk] at h2
    have h3 : Ideal.Quotient.mk ((P : Ideal B) ^ n) (g • z) =
        Ideal.Quotient.mk ((P : Ideal B) ^ n) (g • gO P' • u) := h2

    have hco : transportOf A B G (g * gO P')
        (show (g * gO P') • 𝔓 = (P : Ideal B) from by
          rw [mul_smul, ← (hgO P'), smul_inv_smul]).le y =
        transportOf A B G (gO P) ((hgO P).symm).le y :=
      transportOf_eq_of_fixed A B G (g * gO P') (gO P)
        (by rw [mul_smul, ← (hgO P'), smul_inv_smul]) (hgO P).symm y hy
    have h4 := congrArg (evalₐ (P : Ideal B) n) hco
    rw [evalₐ_transportOf A B G (g * gO P') _ n y u hu,
      evalₐ_transportOf A B G (gO P) _ n y u hu, mul_smul] at h4

    rw [evalₐ_component_selfSmul A B G 𝔭 g P.2.2 w n z hz,
      evalₐ_transportOf A B G (gO P) (hgO P).ge n y u hu]
    exact h3.trans h4

  set z' : AdicCompletion 𝔭 A ⊗[A] B := (tensorRingEquiv B 𝔭).symm w with hz'
  have hz'fix : ∀ g : G,
      (letI := Algebra.TensorProduct.rightMulSemiringAction A (AdicCompletion 𝔭 A) B G
      g • z') = z' := by
    intro g
    letI := Algebra.TensorProduct.rightMulSemiringAction A (AdicCompletion 𝔭 A) B G
    refine (tensorRingHom_bijective B 𝔭).injective ?_
    have he := tensorRingHom_equivariant A B G 𝔭 g z'
    rw [he, show tensorRingHom B 𝔭 z' = w from (tensorRingEquiv B 𝔭).apply_symm_apply w]
    exact hwfix g
  haveI := Algebra.IsInvariant.isInvariant_tensorProduct_of_flat A
    (AdicCompletion 𝔭 A) B G
  obtain ⟨x, hx⟩ := Algebra.IsInvariant.isInvariant
    (A := AdicCompletion 𝔭 A) (B := (AdicCompletion 𝔭 A) ⊗[A] B) (G := G) z' hz'fix
  refine ⟨x, ?_⟩

  have hbc : completionBaseChangeHom B 𝔭 x = w := by
    rw [completionBaseChangeHom_eq_tensor, show (x ⊗ₜ[A] (1 : B)) = z' from hx,
      show tensorRingHom B 𝔭 z' = w from (tensorRingEquiv B 𝔭).apply_symm_apply w]
  show semilocalComponent _ (mem_index_self A B G 𝔭 𝔓).2 (completionBaseChangeHom B 𝔭 x) = y
  rw [hbc, hwF ⟨𝔓, mem_index_self A B G 𝔭 𝔓⟩]
  exact (transportOf_eq_of_fixed A B G (gO ⟨𝔓, mem_index_self A B G 𝔭 𝔓⟩) 1
    (hgO ⟨𝔓, mem_index_self A B G 𝔭 𝔓⟩).symm (one_smul G 𝔓) y hy).trans
    (transportOf_one A B G 𝔓 y)

noncomputable def invariantsCompletionEquiv :
    letI := stabilizerMulSemiringAction A B G 𝔓
    haveI := stabilizer_smulCommClass A B G 𝔓
    AdicCompletion 𝔭 A ≃ₐ[A]
      FixedPoints.subalgebra A (AdicCompletion 𝔓 B) (MulAction.stabilizer G 𝔓) := by
  letI := stabilizerMulSemiringAction A B G 𝔓
  haveI := stabilizer_smulCommClass A B G 𝔓
  refine AlgEquiv.ofBijective
    ((invariantsCompletionHom A B G 𝔭 𝔓).codRestrict
      (FixedPoints.subalgebra A (AdicCompletion 𝔓 B) (MulAction.stabilizer G 𝔓))
      fun x h => stabAut_invariantsCompletionHom A B G 𝔭 𝔓 h x) ⟨?_, ?_⟩
  · intro x y hxy
    exact invariantsCompletionHom_injective A B G 𝔭 𝔓 (congrArg Subtype.val hxy)
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_invariantsCompletionHom_eq A B G 𝔭 𝔓 y hy
    exact ⟨x, Subtype.ext hx⟩

include G in

noncomputable def invariantsCompletionRingEquiv :
    letI := stabilizerMulSemiringAction A B G 𝔓
    haveI := stabilizer_smulCommClass A B G 𝔓
    AdicCompletion 𝔭 A ≃+*
      FixedPoints.subalgebra A (AdicCompletion 𝔓 B) (MulAction.stabilizer G 𝔓) :=
  (invariantsCompletionEquiv A B G 𝔭 𝔓).toRingEquiv

include G in
omit [Finite G] [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B]
  [Algebra.IsInvariant A B G] [𝔓.IsPrime] in

theorem mem_fixedPoints_iff (x : AdicCompletion 𝔓 B) :
    (letI := stabilizerMulSemiringAction A B G 𝔓
    haveI := stabilizer_smulCommClass A B G 𝔓
    x ∈ FixedPoints.subalgebra A (AdicCompletion 𝔓 B) (MulAction.stabilizer G 𝔓)) ↔
      ∀ h : MulAction.stabilizer G 𝔓, stabAut A B G 𝔓 h x = x :=
  Iff.rfl

end AdicCompletion

end SameUniverseHead

set_option pp.universes true in
#check @AdicCompletion.transportOf
set_option pp.universes true in
#check @AdicCompletion.transportOf_eq_of_fixed
#print axioms AdicCompletion.liesOver_of_isPrime_of_map_le
#print axioms AdicCompletion.isMaximal_of_isPrime_of_liesOver
#print axioms AdicCompletion.isMaximal_and_map_le_iff
#print axioms AdicCompletion.exists_smul_eq_of_liesOver
#print axioms AdicCompletion.map_toAlgEquiv_le_of_smul_le
#print axioms AdicCompletion.transportOf
#print axioms AdicCompletion.evalₐ_transportOf
#print axioms AdicCompletion.transportOf_of
#print axioms AdicCompletion.transportOf_eq_of_fixed
#print axioms AdicCompletion.map_algebraMap_le_smul
#print axioms AdicCompletion.semilocalComponent_selfSmul

set_option pp.universes true in
#check @AdicCompletion.invariantsCompletionEquiv
set_option pp.universes true in
#check @AdicCompletion.invariantsCompletionHom
#print axioms AdicCompletion.isNoetherianRing_of_finite_algebra
#print axioms AdicCompletion.isArtinianRing_quotient_map
#print axioms AdicCompletion.mem_index_self
#print axioms AdicCompletion.smul_mem_index
#print axioms AdicCompletion.completionBaseChangeHom_eq_tensor
#print axioms AdicCompletion.completionBaseChangeHom_injective
#print axioms AdicCompletion.invariantsCompletionHom
#print axioms AdicCompletion.evalₐ_invariantsCompletionHom
#print axioms AdicCompletion.stabAut_invariantsCompletionHom
#print axioms AdicCompletion.eq_of_component_eq_of_smul_eq
#print axioms AdicCompletion.transportOf_one
#print axioms AdicCompletion.evalₐ_component_selfSmul
#print axioms AdicCompletion.evalₐ_component
#print axioms AdicCompletion.invariantsCompletionHom_injective
#print axioms AdicCompletion.exists_invariantsCompletionHom_eq
#print axioms AdicCompletion.invariantsCompletionEquiv
#print axioms AdicCompletion.invariantsCompletionRingEquiv
#print axioms AdicCompletion.mem_fixedPoints_iff


