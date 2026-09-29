-- Prove2me | Definitions.Def_AdicCompletionGaloisAction
-- name    : AdicCompletionGaloisAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/57b14d90-1585-5e0c-b0ce-1aa6a2f18a71
-- title:
--   Group actions on adic completions of commutative rings
-- statement:
--   Throughout, $C$ is a commutative ring carrying an action of a group $G$ by ring automorphisms (`MulSemiringAction G C`), and completions are the project's $\mathrm{AdicCompletion}$ of a ring at an ideal, $\widehat{C}^{I}=\varprojlim_n C/I^n$, together with the functoriality `mapₐ` for a $\mathbb{Z}$- or $k$-algebra map sending one ideal into another. The basic construction is `smulAlgHom`: given an ideal $I$ with $g\bullet I=I$ for all $g\in G$ (pointwise action on ideals), the helper `map_toIntAlgHom_le_of_smul_eq` shows $I.\mathrm{map}\,g\le I$, and `smulAlgHom I h g` is the induced $\mathbb{Z}$-algebra endomorphism of $\widehat{C}^{I}$, characterised by $g\cdot \mathrm{of}(c)=\mathrm{of}(g\bullet c)$ and, levelwise, by $\mathrm{ev}_n(g\cdot x)=\overline{g\bullet c}$ whenever $\mathrm{ev}_n(x)=\overline{c}$ in $C/I^n$. Assembling these gives `mulSemiringActionOfSMulEq`, an action of $G$ on $\widehat{C}^{I}$ by ring automorphisms, with the value lemmas `smul_def'`, `smul_of'`, `evalₐ_smul'`.
--
--   Two instances specialise this: `instMulSemiringActionStabilizer`, the action of $\mathrm{Stab}_G(\mathfrak{n})$ on $\widehat{C}^{\mathfrak n}$ for an arbitrary ideal $\mathfrak n$, and, for a base ring $O$ with $C$ an $O$-algebra whose $G$-action commutes with the $O$-action, `instMulSemiringActionMap`, the action of all of $G$ on the completion of $C$ at $J\cdot C=J.\mathrm{map}(\mathrm{algebraMap}\,O\,C)$ for $J\subseteq O$ an ideal; here `smul_algebraMap_eq` and `smul_map_algebraMap_eq` record that $G$ fixes the image of $O$ and stabilises $J\cdot C$. Further declarations supply the compatibilities: `SMulCommClass` of the group action with scalars from $O$ in both situations; `instFaithfulSMulStabilizer`, faithfulness of the $\mathrm{Stab}_G(\mathfrak n)$-action on $\widehat{C}^{\mathfrak n}$ when $G$ acts faithfully on $C$ and $C$ is $\mathfrak n$-adically Hausdorff (so that $\mathrm{of}$ is injective); and, for $\mathfrak n$ lying over $J$ (i.e. $J=\mathfrak n\cap O$ as a comap), the algebra map $\widehat{O}^{J}\to\widehat{C}^{\mathfrak n}$ induced by $O\to C$ (`algHomOfLiesOver`, `instAlgebraOfLiesOver`, declared with low priority), the scalar tower $O\to\widehat{O}^{J}\to\widehat{C}^{\mathfrak n}$, its values on $\mathrm{of}$ and levelwise, and the facts that $\mathrm{Stab}_G(\mathfrak n)$ fixes the image of $\widehat{O}^{J}$ pointwise and commutes with its scalar action. All the action, algebra, tower and commutation instances are attached only inside the scope `AdicCompletion.GaloisAction`.
--
--   **Relation to Mathlib.** Mathlib provides `AdicCompletion`, `MulSemiringAction`, pointwise actions on ideals and `Ideal.LiesOver`, but no group action on an adic completion; these instances are the project's own, built on its `mapₐ` functoriality for adic completions, and are made available only through the scoped namespace `AdicCompletion.GaloisAction` rather than globally on Mathlib's heads.
--
--   **Where it is used.** These instances are what allows a Galois group, or the stabiliser (decomposition group) of a prime, to act on the completion of a ring at that prime, and make such a completion an algebra over the completion of the base at the prime below, compatibly with the group action. They are used wherever completed local rings with their residual group actions occur in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AdicCompletionGaloisAction.lean

import Mathlib
import Definitions.Def_AdicCompletionRingFunctoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

namespace AdicCompletion.GaloisAction
end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section Generic

variable (I : Ideal C)

theorem map_toIntAlgHom_le_of_smul_eq (g : G) (h : g • I = I) :
    I.map (MulSemiringAction.toRingHom G C g).toIntAlgHom ≤ I := by
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  rw [Ideal.mem_comap]
  have hmem : g • c ∈ g • I := Ideal.smul_mem_pointwise_smul g c I hc
  rw [h] at hmem
  exact hmem

noncomputable def smulAlgHom (h : ∀ g : G, g • I = I) (g : G) :
    AdicCompletion I C →ₐ[ℤ] AdicCompletion I C :=
  mapₐ I I (MulSemiringAction.toRingHom G C g).toIntAlgHom (map_toIntAlgHom_le_of_smul_eq I g (h g))

theorem smulAlgHom_of (h : ∀ g : G, g • I = I) (g : G) (c : C) :
    smulAlgHom I h g (of I C c) = of I C (g • c) := by
  rw [smulAlgHom, mapₐ_of]
  rfl

theorem evalₐ_smulAlgHom (h : ∀ g : G, g • I = I) (g : G) (n : ℕ) (c : C)
    (x : AdicCompletion I C) (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) c) :
    evalₐ I n (smulAlgHom I h g x) = Ideal.Quotient.mk (I ^ n) (g • c) := by
  rw [smulAlgHom, evalₐ_mapₐ, hx, levelMapₐ_mk]
  rfl

@[reducible]
noncomputable def mulSemiringActionOfSMulEq (h : ∀ g : G, g • I = I) :
    MulSemiringAction G (AdicCompletion I C) where
  smul g x := smulAlgHom I h g x
  one_smul x := by
    apply ext_evalₐ
    intro n
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    show evalₐ I n (smulAlgHom I h 1 x) = _
    rw [evalₐ_smulAlgHom I h 1 n c x hc.symm, one_smul, hc]
  mul_smul g g' x := by
    apply ext_evalₐ
    intro n
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    show evalₐ I n (smulAlgHom I h (g * g') x)
      = evalₐ I n (smulAlgHom I h g (smulAlgHom I h g' x))
    rw [evalₐ_smulAlgHom I h (g * g') n c x hc.symm,
      evalₐ_smulAlgHom I h g n (g' • c) _ (evalₐ_smulAlgHom I h g' n c x hc.symm), mul_smul]
  smul_zero g := _root_.map_zero (smulAlgHom I h g)
  smul_add g x y := _root_.map_add (smulAlgHom I h g) x y
  smul_one g := _root_.map_one (smulAlgHom I h g)
  smul_mul g x y := _root_.map_mul (smulAlgHom I h g) x y

theorem smul_def' (h : ∀ g : G, g • I = I) (g : G) (x : AdicCompletion I C) :
    (letI := mulSemiringActionOfSMulEq I h; g • x) = smulAlgHom I h g x :=
  rfl

theorem smul_of' (h : ∀ g : G, g • I = I) (g : G) (c : C) :
    (letI := mulSemiringActionOfSMulEq I h; g • of I C c) = of I C (g • c) :=
  smulAlgHom_of I h g c

theorem evalₐ_smul' (h : ∀ g : G, g • I = I) (g : G) (n : ℕ) (c : C) (x : AdicCompletion I C)
    (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) c) :
    (letI := mulSemiringActionOfSMulEq I h; evalₐ I n (g • x)) = Ideal.Quotient.mk (I ^ n) (g • c) :=
  evalₐ_smulAlgHom I h g n c x hx

end Generic

section Stabilizer

variable (𝔫 : Ideal C)

@[reducible]
noncomputable def instMulSemiringActionStabilizer :
    MulSemiringAction (MulAction.stabilizer G 𝔫) (AdicCompletion 𝔫 C) :=
  mulSemiringActionOfSMulEq 𝔫 (fun d => d.2)

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instMulSemiringActionStabilizer

@[simp]
theorem stabilizer_smul_of (d : MulAction.stabilizer G 𝔫) (c : C) :
    d • of 𝔫 C c = of 𝔫 C ((d : G) • c) :=
  smul_of' 𝔫 (fun d => d.2) d c

theorem evalₐ_stabilizer_smul (d : MulAction.stabilizer G 𝔫) (n : ℕ) (c : C)
    (x : AdicCompletion 𝔫 C) (hx : evalₐ 𝔫 n x = Ideal.Quotient.mk (𝔫 ^ n) c) :
    evalₐ 𝔫 n (d • x) = Ideal.Quotient.mk (𝔫 ^ n) ((d : G) • c) :=
  evalₐ_smul' 𝔫 (fun d => d.2) d n c x hx

end Stabilizer

section MapIdeal

variable {O : Type w} [CommRing O] [Algebra O C]

theorem smul_algebraMap_eq [SMulCommClass G O C] (g : G) (o : O) :
    g • algebraMap O C o = algebraMap O C o := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

theorem smul_map_algebraMap_eq [SMulCommClass G O C] (J : Ideal O) (g : G) :
    g • J.map (algebraMap O C) = J.map (algebraMap O C) := by
  rw [Ideal.pointwise_smul_def, Ideal.map_map]
  congr 1
  ext o
  exact smul_algebraMap_eq g o

@[reducible]
noncomputable def instMulSemiringActionMap [SMulCommClass G O C] (J : Ideal O) :
    MulSemiringAction G (AdicCompletion (J.map (algebraMap O C)) C) :=
  mulSemiringActionOfSMulEq _ (smul_map_algebraMap_eq J)

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instMulSemiringActionMap

@[simp]
theorem map_smul_of [SMulCommClass G O C] (J : Ideal O) (g : G) (c : C) :
    g • of (J.map (algebraMap O C)) C c = of (J.map (algebraMap O C)) C (g • c) :=
  smul_of' _ (smul_map_algebraMap_eq J) g c

theorem evalₐ_map_smul [SMulCommClass G O C] (J : Ideal O) (g : G) (n : ℕ) (c : C)
    (x : AdicCompletion (J.map (algebraMap O C)) C)
    (hx : evalₐ (J.map (algebraMap O C)) n x = Ideal.Quotient.mk _ c) :
    evalₐ (J.map (algebraMap O C)) n (g • x) = Ideal.Quotient.mk _ (g • c) :=
  evalₐ_smul' _ (smul_map_algebraMap_eq J) g n c x hx

theorem instSMulCommClassStabilizer [SMulCommClass G O C] (𝔫 : Ideal C) :
    SMulCommClass (MulAction.stabilizer G 𝔫) O (AdicCompletion 𝔫 C) where
  smul_comm d o x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', algebraMap_apply, stabilizer_smul_of,
      smul_algebraMap_eq]

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instSMulCommClassStabilizer

theorem instSMulCommClassMap [SMulCommClass G O C] (J : Ideal O) :
    SMulCommClass G O (AdicCompletion (J.map (algebraMap O C)) C) where
  smul_comm g o x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', algebraMap_apply, map_smul_of,
      smul_algebraMap_eq]

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instSMulCommClassMap

end MapIdeal

section Faithful

theorem instFaithfulSMulStabilizer [FaithfulSMul G C] (𝔫 : Ideal C) [IsHausdorff 𝔫 C] :
    FaithfulSMul (MulAction.stabilizer G 𝔫) (AdicCompletion 𝔫 C) where
  eq_of_smul_eq_smul {d₁ d₂} h := by
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := C)
    intro c
    apply of_injective 𝔫 (M := C)
    rw [← stabilizer_smul_of, ← stabilizer_smul_of, h]

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instFaithfulSMulStabilizer

end Faithful

section LiesOver

variable {O : Type w} [CommRing O] [Algebra O C] (J : Ideal O) (𝔫 : Ideal C)

theorem map_ofId_le_of_liesOver [h𝔫 : 𝔫.LiesOver J] : J.map (Algebra.ofId O C) ≤ 𝔫 := by
  rw [Ideal.map_le_iff_le_comap]
  intro o ho
  rw [h𝔫.over] at ho
  exact ho

noncomputable def algHomOfLiesOver [𝔫.LiesOver J] :
    AdicCompletion J O →ₐ[O] AdicCompletion 𝔫 C :=
  mapₐ J 𝔫 (Algebra.ofId O C) (map_ofId_le_of_liesOver J 𝔫)

@[reducible]
noncomputable def instAlgebraOfLiesOver [𝔫.LiesOver J] :
    Algebra (AdicCompletion J O) (AdicCompletion 𝔫 C) :=
  (algHomOfLiesOver J 𝔫).toRingHom.toAlgebra

scoped[AdicCompletion.GaloisAction] attribute [instance low] AdicCompletion.instAlgebraOfLiesOver

theorem algebraMap_eq_algHomOfLiesOver [𝔫.LiesOver J] (x : AdicCompletion J O) :
    algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) x = algHomOfLiesOver J 𝔫 x :=
  rfl

theorem instIsScalarTowerOfLiesOver [𝔫.LiesOver J] :
    IsScalarTower O (AdicCompletion J O) (AdicCompletion 𝔫 C) :=
  IsScalarTower.of_algebraMap_eq fun o =>
    (AlgHom.commutes (algHomOfLiesOver J 𝔫) o).symm

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instIsScalarTowerOfLiesOver

@[simp]
theorem algebraMap_of [𝔫.LiesOver J] (o : O) :
    algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) (of J O o) = of 𝔫 C (algebraMap O C o) := by
  rw [algebraMap_eq_algHomOfLiesOver, algHomOfLiesOver, mapₐ_of]
  rfl

theorem evalₐ_algebraMap_of_liesOver [𝔫.LiesOver J] (n : ℕ) (o : O) (x : AdicCompletion J O)
    (hx : evalₐ J n x = Ideal.Quotient.mk (J ^ n) o) :
    evalₐ 𝔫 n (algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) x)
      = Ideal.Quotient.mk (𝔫 ^ n) (algebraMap O C o) := by
  rw [algebraMap_eq_algHomOfLiesOver, algHomOfLiesOver, evalₐ_mapₐ, hx, levelMapₐ_mk]
  rfl

theorem stabilizer_smul_algebraMap [SMulCommClass G O C] [𝔫.LiesOver J]
    (d : MulAction.stabilizer G 𝔫) (a : AdicCompletion J O) :
    d • algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) a
      = algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) a := by
  apply ext_evalₐ
  intro n
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (evalₐ J n a)
  rw [evalₐ_stabilizer_smul 𝔫 d n (algebraMap O C o) _ (evalₐ_algebraMap_of_liesOver J 𝔫 n o a ho.symm),
    evalₐ_algebraMap_of_liesOver J 𝔫 n o a ho.symm, smul_algebraMap_eq]

theorem instSMulCommClassStabilizerOfLiesOver [SMulCommClass G O C] [𝔫.LiesOver J] :
    SMulCommClass (MulAction.stabilizer G 𝔫) (AdicCompletion J O) (AdicCompletion 𝔫 C) where
  smul_comm d a x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', stabilizer_smul_algebraMap]

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instSMulCommClassStabilizerOfLiesOver

end LiesOver

end AdicCompletion

#print axioms AdicCompletion.mulSemiringActionOfSMulEq
#print axioms AdicCompletion.smul_of'
#print axioms AdicCompletion.evalₐ_smul'
#print axioms AdicCompletion.instMulSemiringActionStabilizer
#print axioms AdicCompletion.stabilizer_smul_of
#print axioms AdicCompletion.evalₐ_stabilizer_smul
#print axioms AdicCompletion.instMulSemiringActionMap
#print axioms AdicCompletion.map_smul_of
#print axioms AdicCompletion.evalₐ_map_smul
#print axioms AdicCompletion.instSMulCommClassStabilizer
#print axioms AdicCompletion.instSMulCommClassMap
#print axioms AdicCompletion.instFaithfulSMulStabilizer
#print axioms AdicCompletion.instAlgebraOfLiesOver
#print axioms AdicCompletion.instIsScalarTowerOfLiesOver
#print axioms AdicCompletion.algebraMap_of
#print axioms AdicCompletion.evalₐ_algebraMap_of_liesOver
#print axioms AdicCompletion.stabilizer_smul_algebraMap
#print axioms AdicCompletion.instSMulCommClassStabilizerOfLiesOver


