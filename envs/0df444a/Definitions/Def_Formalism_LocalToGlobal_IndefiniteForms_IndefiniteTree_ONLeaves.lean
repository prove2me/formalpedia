-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
-- name    : Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T17:43:00.542368+00:00
-- url     : https://prove2.me/theorems/ce7c7588-6642-459f-bd85-eb98266907c9
-- title:
--   ONLeaves
-- statement:
--   Definitions and structural lemmas for ONLeaves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONLeaves.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain CategoryTheory
namespace Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
section Level
variable {ι : Type} [Fintype ι] [DecidableEq ι] (kf : ι → Type) [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] (n : ℕ)
def IsLevelGroups (Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))) (Uv : ∀ v, Subgroup (Pm v)) : Prop :=
  (∀ v (h : GL (Fin (n + 1)) (kf v)), h ∈ Pm v ↔ IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf v))) ∧
  ∀ v (h : Pm v), h ∈ Uv v ↔ IsUniU ((h : GL (Fin (n + 1)) (kf v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf v))
def IsGenericChar (χ : ∀ v, AddChar (kf v) (𝓞 K)) : Prop := ∀ v, χ v ≠ 1
def psiU (χ : ∀ v, AddChar (kf v) (𝓞 K)) (Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))) : (∀ v, Pm v) → 𝓞 K :=
  fun h => ∏ v, χ v (supd (((h v : Pm v) : GL (Fin (n + 1)) (kf v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf v)))
end Level
section Ties
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
def TieU {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} (O : OnObj S (∀ v, Pm v) c) (Uv : ∀ v, Subgroup (Pm v)) : Prop :=
  O.U = Subgroup.pi Set.univ Uv
def TiePsi {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} (O : OnObj S (∀ v, Pm v) c) (χ : ∀ v, AddChar (kf v) (𝓞 K)) :
    Prop :=
  O.ψ = psiU kf n χ Pm
def TieLevelNum {P : Type} [Group P] [Finite P] (O : OnObj S P c) (n fN : ℕ) : Prop :=
  O.f = (fN : ℝ) ∧ O.rr = (n : ℝ) + 1
def LeafLevelSq {P : Type} [Group P] [Finite P] (O : OnObj S P c) (kf : ι → Type) [∀ v, Field (kf v)] [∀ v, Fintype (kf v)]
    (fN : ℕ) : Prop :=
  O.g1.Prime ∧ O.g2.Prime ∧ O.g1 ≠ O.g2 ∧ (∀ v, Fintype.card (kf v) = O.g1 ∨ Fintype.card (kf v) = O.g2) ∧
    (Finset.univ.filter fun v => Fintype.card (kf v) = O.g1).card = fN ∧
    (Finset.univ.filter fun v => Fintype.card (kf v) = O.g2).card = fN
def LeafYBound {P : Type} [Group P] [Finite P] (O : OnObj S P c) : Prop :=
  2 * O.f / (((min O.g1 O.g2 : ℕ) : ℝ) - 1) ≤ O.y
end Ties
section Orders
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
variable {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} {Uv : ∀ v, Subgroup (Pm v)}
end Orders
section Discharge
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
variable {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} {Uv : ∀ v, Subgroup (Pm v)}
def IsTypeList {G : Type} [Group G] [Fintype G] {τ : Type} (V : τ → FDRep ℂ G) : Prop :=
  (∀ t, Simple (V t)) ∧ ∀ t u, t ≠ u → IsEmpty (V t ≅ V u)
def IsGoodIdem {G : Type} [Group G] [Fintype G] (σ : K →+* ℂ) {τ : Type} [Fintype τ] (V : τ → FDRep ℂ G)
    (ε : MonoidAlgebra K G) : Prop :=
  MonoidAlgebra.mapRingHom G σ ε = ∑ t, PI.CharIdem.charIdem (V t)
def TieProj {G : Type} [Group G] {P : Type} [Group P] [Finite P] (O : OnObj S P c)
    (ρG : ∀ j, Representation K G (Fin (O.nZ j) → K)) (ε : Bs.J → MonoidAlgebra K G) : Prop :=
  ∀ j, O.e j = (ρG j).asAlgebraHom (ε j) ∧ O.V₀ j = LinearMap.range (O.e j)
end Discharge
section Builder
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}
abbrev regroup {P' : Type} [Group P'] [Finite P'] (T : OnObj S P' c) (P : Type) [Group P] [Finite P]
    (ρ : ∀ j, Representation K P (Fin (T.nZ j) → K)) (U : Subgroup P) (ψ : P → 𝓞 K)
    (V₀ : ∀ j, Submodule K (Fin (T.nZ j) → K)) (e : ∀ j, (Fin (T.nZ j) → K) →ₗ[K] (Fin (T.nZ j) → K))
    (f rr k : ℝ) (g1 g2 : ℕ) : OnObj S P c where
  nZ := T.nZ
  ρ := ρ
  U := U
  ψ := ψ
  V₀ := V₀
  e := e
  Ms := T.Ms
  φ := T.φ
  Th1 := T.Th1
  Th := T.Th
  ThK := T.ThK
  Th0 := T.Th0
  ThJ := T.ThJ
  X₃ := T.X₃
  σ := T.σ
  a := T.a
  E := T.E
  r1 := T.r1
  r2 := T.r2
  pde := T.pde
  ε0 := T.ε0
  nX := T.nX
  θ' := T.θ'
  eX := T.eX
  pr := T.pr
  Mt := T.Mt
  nnK := T.nnK
  Jp := T.Jp
  k := k
  m := T.m
  f := f
  bp := T.bp
  Sc := T.Sc
  eta := T.eta
  T := T.T
  DF := T.DF
  X2 := T.X2
  x := T.x
  eps := T.eps
  vd := T.vd
  rr := rr
  de2 := T.de2
  Nc := T.Nc
  wt := T.wt
  th := T.th
  ad := T.ad
  T2 := T.T2
  g1 := g1
  g2 := g2
  q1 := T.q1
  dd := T.dd
  sm := T.sm
end Builder
section Groups
def mirabSub (k : Type) [Field k] [Fintype k] (n : ℕ) : Subgroup (GL (Fin (n + 1)) k) where
  carrier := {h | IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)}
  mul_mem' := by
    intro a b ha hb
    show PI.MirabIndex.IsMirab _
    rw [PI.MirabolicIndex₂.isMirab_iff, PI.MirabolicIndex₂.row_mul_of_mirab n a b ha]
    exact (PI.MirabolicIndex₂.isMirab_iff n _).mp hb
  one_mem' := by
    show PI.MirabIndex.IsMirab _
    rw [PI.MirabolicIndex₂.isMirab_iff, Units.val_one]
    exact PI.MirabolicIndex₂.one_last n
  inv_mem' := by
    intro h hh
    have := PI.MirabolicIndex₂.mirab_mul_inv n 1 h (by
      rw [Units.val_one, PI.MirabolicIndex₂.one_last]
      exact ((PI.MirabolicIndex₂.isMirab_iff n _).mp hh).symm)
    rwa [one_mul] at this
theorem isUniU_mul {k : Type} [Field k] {n : ℕ} {a b : Matrix (Fin (n + 1)) (Fin (n + 1)) k}
    (ha : IsUniU a) (hb : IsUniU b) : IsUniU (a * b) := by
  have hta : a.BlockTriangular id := fun i j hij => ha.2 i j hij
  have htb : b.BlockTriangular id := fun i j hij => hb.2 i j hij
  refine ⟨fun i => ?_, fun i j hij => (hta.mul htb) hij⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [ha.1 i, hb.1 i, one_mul]
  · intro m _ hm
    rcases lt_or_gt_of_ne hm with h | h
    · rw [ha.2 i m h, zero_mul]
    · rw [hb.2 m i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
theorem isUniU_one {k : Type} [Field k] {n : ℕ} : IsUniU (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
  ⟨fun i => Matrix.one_apply_eq i, fun _ _ hij => Matrix.one_apply_ne (ne_of_gt hij)⟩
def uniSub (k : Type) [Field k] [Fintype k] (n : ℕ) : Subgroup (mirabSub k n) where
  carrier := {h | IsUniU (((h : mirabSub k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)}
  mul_mem' := by
    intro a b ha hb
    show IsUniU ((((a * b : mirabSub k n) : GL (Fin (n + 1)) k)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact isUniU_mul ha hb
  one_mem' := by
    show IsUniU ((((1 : mirabSub k n) : GL (Fin (n + 1)) k)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    rw [OneMemClass.coe_one, Units.val_one]
    exact isUniU_one
  inv_mem' := by
    intro x hx
    have hpow : ∀ m : ℕ, IsUniU ((((x ^ m : mirabSub k n) : GL (Fin (n + 1)) k)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
      intro m
      induction m with
      | zero =>
        rw [pow_zero, OneMemClass.coe_one, Units.val_one]
        exact isUniU_one
      | succ m ih =>
        rw [pow_succ, Subgroup.coe_mul, Units.val_mul]
        exact isUniU_mul ih hx
    have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    show IsUniU ((((x⁻¹ : mirabSub k n) : GL (Fin (n + 1)) k)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    rw [hinv]
    exact hpow _
end Groups
section ToyLevel
def toyG : Fin 2 → ℕ := ![11, 13]
instance fact_prime_examplePrime (v : Fin 2) : Fact (toyG v).Prime := ⟨by fin_cases v <;> norm_num [toyG]⟩
instance neZero_examplePrime (v : Fin 2) : NeZero (toyG v) := ⟨(fact_prime_examplePrime v).out.ne_zero⟩
abbrev ExampleFiniteField (v : Fin 2) : Type := ZMod (toyG v)
abbrev KC : Type := CyclotomicField 143 ℚ
@[instance_reducible] noncomputable def starKC : StarRing KC := starRingOfComm
theorem one_hundred_forty_three_ne_zero : NeZero ((143 : ℕ) : ℚ) := ⟨by norm_num⟩
attribute [local instance] starKC one_hundred_forty_three_ne_zero
theorem cycKC : IsCyclotomicExtension {143} ℚ KC := CyclotomicField.isCyclotomicExtension 143 ℚ
attribute [local instance] cycKC
noncomputable def zC : 𝓞 KC := (IsCyclotomicExtension.zeta_spec 143 ℚ KC).toInteger
theorem zC_prim : IsPrimitiveRoot zC 143 := (IsCyclotomicExtension.zeta_spec 143 ℚ KC).toInteger_isPrimitiveRoot
theorem toyRoot_prim (v : Fin 2) : IsPrimitiveRoot (zC ^ (143 / toyG v)) (toyG v) :=
  zC_prim.pow (by norm_num) (by fin_cases v <;> norm_num [toyG])
noncomputable def toyAddChar (v : Fin 2) : AddChar (ExampleFiniteField v) (𝓞 KC) :=
  AddChar.zmodChar (toyG v) (toyRoot_prim v).pow_eq_one
abbrev ExampleMirabolicGroup : Type := ∀ v : Fin 2, mirabSub (ExampleFiniteField v) 1
noncomputable abbrev mirabolicExample (v0 : InfinitePlace KC) (Tw0 : Finset (HeightOneSpectrum (𝓞 KC))) :
    OnObj (exampleIndefiniteData KC v0 Tw0 0) ExampleMirabolicGroup exampleC :=
  regroup (exampleObject KC v0 Tw0) ExampleMirabolicGroup (fun _ => 1) (Subgroup.pi Set.univ fun v => uniSub (ExampleFiniteField v) 1)
    (psiU ExampleFiniteField 1 toyAddChar fun v => mirabSub (ExampleFiniteField v) 1) (fun _ => ⊥) (fun _ => 0) 1 2 1 11 13
variable (v0 : InfinitePlace KC) (Tw0 : Finset (HeightOneSpectrum (𝓞 KC)))
end ToyLevel
section NotProjectiveExample
variable (K)
variable (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))
end NotProjectiveExample
end Formalism.L2.Indef.Tree


