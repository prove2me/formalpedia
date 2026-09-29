-- Prove2me | Definitions.Def_AutomorphicForm_TransversalMeasure
-- name    : AutomorphicForm_TransversalMeasure
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/5b0bf7e6-147e-5a6d-bf72-12bf8c20242b
-- title:
--   Semi-local unit groups, idele boxes and level subgroups
-- statement:
--   Throughout, $K \subseteq L$ are number fields. Above a finite place $v$ of $K$ the module works inside the unit group of the semi-local algebra $L \otimes_K K_v$. Here `integralUnits` is the subgroup of those units which, together with their inverses, lie in the image of the integral base-change map $\mathcal{O}_L \otimes \mathcal{O}_{K_v} \to L \otimes_K K_v$ (the group of units of the submonoid given by the range of `HeightOneSpectrum.tensorAdicCompletionIntegersTo`); `includeUnits` is the group homomorphism $K_v^{\times} \to (L \otimes_K K_v)^{\times}$ induced by $s \mapsto 1 \otimes s$; `normOneUnits` is the kernel of the homomorphism sending a unit to the valuation of its norm down to $K_v$, the valuation taking values in $\mathrm{WithZero}(\mathrm{Multiplicative}\,\mathbb{Z})$; and `saturatedUnits` is the pointwise product of `integralUnits` with the image of `includeUnits`. On the base, `valOneUnits` is the set, and `valOneUnitsSubgroup` the corresponding subgroup (kernel of the valuation on units), of units of $K_v$ of valuation $1$. Above an infinite place $v$ of $K$ the ambient group is the unit group of $\prod_{w \mid v} L_w$, indexed by the extensions of $v$ to $L$: `includeArchUnits` is induced by the diagonal $K_v$-structure map, `archNormOneUnits` is the kernel of the composite of the norm to $K_v$ with the real absolute value, and `archFibre` sends a unit of the infinite adele ring of $L$ to its components at the places above $v$. Both unit groups are equipped with their Borel $\sigma$-algebras (`semiLocalUnitsBorel`, `archUnitsBorel`). The coordinate maps on the idele group of $L$ are `archSemiLocalIdele` (infinite part followed by `archFibre`) and `semiLocalIdele` (finite part followed by [`AutomorphicForm.semiLocalEval K L v`](../def/AutomorphicForm_TwistedOrbital.html#L441), the evaluation at the places above $v$ transported to $L \otimes_K K_v$), while `idelesBaseChange` is induced by the ring homomorphism $\mathbb{A}_K \to \mathbb{A}_L$ given by the archimedean conorm and the finite conorm. Then `saturated Sτ` is the set of ideles of $L$ whose semi-local component is saturated at every finite place of $K$ outside the finite set $Sτ$. Separately, `levelSubgroup` is a purely group-theoretic construction: given a group $B$, families of groups $A_a$, $G_k$ with homomorphisms $q_a : B \to A_a$, $p_k : B \to G_k$, subgroups $NA_a \le A_a$ and $N_k, U_k \le G_k$, and a finite set $\mathrm{bad}$ of indices $k$, it is the subgroup of those $b$ with $q_a(b) \in NA_a$ for all $a$, $p_k(b) \in N_k$ for $k \in \mathrm{bad}$ and $p_k(b) \in U_k$ otherwise. Finally, `IsBox E` asserts that a set $E$ of ideles of $L$ is cut out by conditions on the semi-local coordinates: there are Borel-measurable sets $D_v$ in the archimedean semi-local unit groups, for $v$ an infinite place of $K$, and Borel-measurable sets $C_v$ in the semi-local unit groups, for $v$ a finite place, with $C_v$ equal to `integralUnits K L v` for all but finitely many $v$, such that $E$ consists exactly of the $t$ with $\mathrm{archSemiLocalIdele}_v(t) \in D_v$ and $\mathrm{semiLocalIdele}_v(t) \in C_v$ for all $v$.
--
--   **Relation to Mathlib.** The adele and idele machinery (`AdeleRing`, `FiniteAdeleRing`, `InfiniteAdeleRing`, `HeightOneSpectrum.adicCompletion`, `InfinitePlace.Completion`, `Submonoid.units`, `Units.map`) is Mathlib's; the semi-local unit subgroups above a place of the base field, the saturation condition and the box predicate are the project's own notions. Since these unit groups carry no canonical measurable space in Mathlib, `semiLocalUnitsBorel` and `archUnitsBorel` supply the Borel $\sigma$-algebras and are used as local instances.
--
--   **Where it is used.** These unit-group coordinates, level subgroups and boxes are the adelic bookkeeping for the comparison of automorphic forms on $\mathrm{GL}_2$ over $K$ and over $L$ (twisted orbital integrals and base change), which feeds the modularity input to Fermat's Last Theorem via the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_TransversalMeasure.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_M4aHerbrand_GenuineBeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

namespace AutomorphicForm.TransversalMeasure

section Definitions

noncomputable def integralUnits (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Subgroup (L ⊗[K] v.adicCompletion K)ˣ :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubmonoid.units

noncomputable def includeUnits (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom

open scoped TensorProduct.RightActions in

noncomputable def normOneUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Subgroup (L ⊗[K] v.adicCompletion K)ˣ :=
  MonoidHom.ker
    ((Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom.comp
      ((Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K →* v.adicCompletion K).comp (Units.coeHom _)))

def saturatedUnits (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Set (L ⊗[K] v.adicCompletion K)ˣ :=
  (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) * Set.range (includeUnits K L v)

def valOneUnits (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Set (v.adicCompletion K)ˣ :=
  {s | Valued.v (s : v.adicCompletion K) = 1}

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

noncomputable def includeArchUnits (K L : Type) [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) : (v.Completion)ˣ →* (∀ w : v.Extension L, w.1.Completion)ˣ :=
  Units.map (algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion)).toMonoidHom

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

noncomputable def archNormOneUnits (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) : Subgroup (∀ w : v.Extension L, w.1.Completion)ˣ :=
  MonoidHom.ker
    ((normHom : v.Completion →*₀ ℝ).toMonoidHom.comp
      ((Algebra.norm v.Completion : (∀ w : v.Extension L, w.1.Completion) →* v.Completion).comp (Units.coeHom _)))

noncomputable def archFibre (K L : Type) [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) : (InfiniteAdeleRing L)ˣ →* (∀ w : v.Extension L, w.1.Completion)ˣ :=
  Units.map
    (RingHom.pi fun w : v.Extension L => Pi.evalRingHom (fun u : InfinitePlace L => u.Completion) w.1 :
      InfiniteAdeleRing L →+* (∀ w : v.Extension L, w.1.Completion)).toMonoidHom

end Definitions

section Borel

open scoped TensorProduct.RightActions in

@[reducible] noncomputable def semiLocalUnitsBorel (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ :=
  borel _

@[reducible] noncomputable def archUnitsBorel (K L : Type) [Field K] [Field L]
    [Algebra K L] (v : InfinitePlace K) : MeasurableSpace (∀ w : v.Extension L, w.1.Completion)ˣ :=
  borel _

end Borel

noncomputable def archSemiLocalIdele (K L : Type) [Field K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlace K) : (AdeleRing (𝓞 L) L)ˣ →* (∀ w : v.Extension L, w.1.Completion)ˣ :=
  (archFibre K L v).comp
    (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom)

noncomputable def semiLocalIdele (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : (AdeleRing (𝓞 L) L)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ :=
  (Units.map (AutomorphicForm.semiLocalEval K L v).toMonoidHom).comp (NumberField.AdeleRing.finitePartUnits (𝓞 L) L)

noncomputable def idelesBaseChange (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (M4aHerbrand.Bridge.genuineβ K L).toMonoidHom

def saturated (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 L) L)ˣ :=
  {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ → semiLocalIdele K L v t ∈ saturatedUnits K L v}

noncomputable def valOneUnitsSubgroup (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  MonoidHom.ker
    ((Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom.comp
      (Units.coeHom (v.adicCompletion K)))

def levelSubgroup {B α κ : Type*} [Group B] {A : α → Type*} [∀ a, Group (A a)] {G : κ → Type*}
    [∀ k, Group (G k)] (q : ∀ a, B →* A a) (NA : ∀ a, Subgroup (A a)) (p : ∀ k, B →* G k)
    (N U : ∀ k, Subgroup (G k)) (bad : Finset κ) : Subgroup B where
  carrier := {b | (∀ a, q a b ∈ NA a) ∧ (∀ k ∈ bad, p k b ∈ N k) ∧ ∀ k ∉ bad, p k b ∈ U k}
  one_mem' := ⟨fun a => by rw [map_one]; exact one_mem _, fun k _ => by rw [map_one]; exact one_mem _,
    fun k _ => by rw [map_one]; exact one_mem _⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨fun i => by rw [map_mul]; exact mul_mem (ha.1 i) (hb.1 i),
      fun k hk => by rw [map_mul]; exact mul_mem (ha.2.1 k hk) (hb.2.1 k hk),
      fun k hk => by rw [map_mul]; exact mul_mem (ha.2.2 k hk) (hb.2.2 k hk)⟩
  inv_mem' := fun {a} ha =>
    ⟨fun i => by rw [map_inv]; exact inv_mem (ha.1 i), fun k hk => by rw [map_inv]; exact inv_mem (ha.2.1 k hk),
      fun k hk => by rw [map_inv]; exact inv_mem (ha.2.2 k hk)⟩

section Boxes

attribute [local instance] semiLocalUnitsBorel archUnitsBorel

def IsBox (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (E : Set (AdeleRing (𝓞 L) L)ˣ) : Prop :=
  ∃ (D : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ)
    (C : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ),
    (∀ v, MeasurableSet (D v)) ∧ (∀ v, MeasurableSet (C v)) ∧
      {v | C v ≠ (TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)}.Finite ∧
      E = {t | (∀ v, TransversalMeasure.archSemiLocalIdele K L v t ∈ D v) ∧
        ∀ v, TransversalMeasure.semiLocalIdele K L v t ∈ C v}

end Boxes

end AutomorphicForm.TransversalMeasure


