-- Prove2me | Definitions.Def_RepTheory_SmoothVectors
-- name    : RepTheory_SmoothVectors
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/42a8c14d-6260-5f12-a9ce-674507758207
-- title:
--   Smooth vectors for actions of a topological group
-- statement:
--   For a topological group $G$ acting on a type $M$, this module defines `IsSmoothVector G v` to mean exactly that the stabiliser $\mathrm{Stab}_G(v)$ is an open subset of $G$; nothing more is assumed of $M$ than a multiplicative action. Reformulations are recorded: smoothness is equivalent to the existence of an open subgroup (or of an `OpenSubgroup`) fixing $v$, and, in the presence of at least one compact open subgroup of $G$, to the existence of a compact open subgroup fixing $v$ (obtained by intersecting a given one with the stabiliser). The link with the project's own typeclass [`ContinuousSMulDiscrete`](../def/Deformations_ContinuousSMulDiscrete.html#L7) is both directions: every vector is smooth for such an action, and conversely, for $G$ with continuous multiplication, [`ContinuousSMulDiscrete G M`](../def/Deformations_ContinuousSMulDiscrete.html#L7) holds iff every $v : M$ is smooth. Stability lemmas show that smoothness is preserved by the $G$-action ($\mathrm{Stab}_G(g\cdot v)$ is the preimage of $\mathrm{Stab}_G(v)$ under conjugation), that $0$ is smooth, and that sums and scalar multiples $r\cdot v$ (for $r$ in a ring acting commutingly) of smooth vectors are smooth; hence `smoothVectors G R M` is defined as the $R$-submodule of $M$ whose carrier is the set of smooth vectors, and it is shown to be $G$-stable, with $g\cdot v$ smooth iff $v$ is. Restriction lemmas relate smoothness over $G$ and over a subgroup $H$ (always downwards; upwards when $H$ is open), and a finite family of smooth vectors admits a single open subgroup fixing all of them.
--
--   The final section introduces `RightTranslationFn G M`, a type synonym for $G \to M$ carrying the right-translation action $(g\cdot f)(x) = f(xg)$ (with its additive monoid and distributive action instances), and proves that for $G$ nonarchimedean and $f : G \to M$ locally constant with compact support, `RightTranslationFn.mk f` is a smooth vector, i.e. some open subgroup $W \le G$ satisfies $f(yw) = f(y)$ for all $y \in G$, $w \in W$.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients (`MulAction.stabilizer`, `OpenSubgroup`, `Subgroup.isOpen_mono`, `NonarchimedeanGroup`, `IsLocallyConstant`, `HasCompactSupport`) but no predicate for smooth vectors of a group action; `IsSmoothVector`, the submodule `smoothVectors`, and `RightTranslationFn` are the project's own, built over the project's [`ContinuousSMulDiscrete`](../def/Deformations_ContinuousSMulDiscrete.html#L7) typeclass.
--
--   **Where it is used.** This is the foundational layer for the smooth representation theory of $p$-adic groups used on the automorphic side of the argument: it is instantiated for congruence subgroups of $\mathrm{GL}_2(\mathbb{Q}_p)$, supports the Hecke action on smooth vectors and the admissibility predicates, and the right-translation result certifies that locally constant compactly supported test functions are smooth vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_SmoothVectors.lean

import Mathlib
import Definitions.Def_Deformations_ContinuousSMulDiscrete

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Topology

namespace FLT.SmoothVectors

section Predicate

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*}

def IsSmoothVector (G : Type*) {M : Type*} [Group G] [TopologicalSpace G] [MulAction G M]
    (v : M) : Prop :=
  IsOpen ((MulAction.stabilizer G v : Subgroup G) : Set G)

variable [MulAction G M]

theorem isSmoothVector_iff_isOpen_stabilizer (v : M) :
    IsSmoothVector G v ↔ IsOpen ((MulAction.stabilizer G v : Subgroup G) : Set G) :=
  Iff.rfl

theorem isSmoothVector_iff_exists_isOpen_subgroup [ContinuousMul G] {v : M} :
    IsSmoothVector G v ↔
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, u • v = v := by
  constructor
  · intro hv
    exact ⟨MulAction.stabilizer G v, hv, fun u hu => MulAction.mem_stabilizer_iff.mp hu⟩
  · rintro ⟨U, hUo, hUv⟩
    exact Subgroup.isOpen_mono (fun u hu => MulAction.mem_stabilizer_iff.mpr (hUv u hu)) hUo

theorem isSmoothVector_iff_exists_openSubgroup [ContinuousMul G] {v : M} :
    IsSmoothVector G v ↔ ∃ U : OpenSubgroup G, ∀ u ∈ U, u • v = v := by
  rw [isSmoothVector_iff_exists_isOpen_subgroup]
  constructor
  · rintro ⟨U, hUo, hUv⟩
    exact ⟨⟨U, hUo⟩, hUv⟩
  · rintro ⟨U, hUv⟩
    exact ⟨U.toSubgroup, U.isOpen, hUv⟩

theorem isSmoothVector_iff_exists_isCompact_isOpen_subgroup [ContinuousMul G]
    (hex : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G)) {v : M} :
    IsSmoothVector G v ↔
      ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ ∀ u ∈ K, u • v = v := by
  constructor
  · intro hv
    obtain ⟨K₀, hK₀c, hK₀o⟩ := hex
    refine ⟨K₀ ⊓ MulAction.stabilizer G v, ?_, ?_, ?_⟩
    · rw [Subgroup.coe_inf]
      exact hK₀c.inter_right (Subgroup.isClosed_of_isOpen _ hv)
    · rw [Subgroup.coe_inf]
      exact hK₀o.inter hv
    · intro u hu
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hu).2
  · rintro ⟨K, _, hKo, hKv⟩
    rw [isSmoothVector_iff_isOpen_stabilizer]
    exact Subgroup.isOpen_mono (fun u hu => MulAction.mem_stabilizer_iff.mpr (hKv u hu)) hKo

theorem isSmoothVector_of_continuousSMulDiscrete [ContinuousSMulDiscrete G M] (v : M) :
    IsSmoothVector G v :=
  ContinuousSMulDiscrete.isOpen_stabilizer G v

theorem continuousSMulDiscrete_iff_forall_isSmoothVector [ContinuousMul G] :
    ContinuousSMulDiscrete G M ↔ ∀ v : M, IsSmoothVector G v :=
  continuousSMulDiscrete_iff_isOpen_stabilizer

end Predicate

section Stability

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*}

theorem IsSmoothVector.smul [MulAction G M] [ContinuousMul G] {v : M}
    (hv : IsSmoothVector G v) (g : G) : IsSmoothVector G (g • v) := by
  rw [isSmoothVector_iff_isOpen_stabilizer] at hv ⊢
  have hset : ((MulAction.stabilizer G (g • v) : Subgroup G) : Set G)
      = (fun h : G => g⁻¹ * h * g) ⁻¹' ((MulAction.stabilizer G v : Subgroup G) : Set G) := by
    ext h
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff]
    constructor
    · intro hh
      calc (g⁻¹ * h * g) • v = g⁻¹ • h • g • v := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • g • v := by rw [hh]
        _ = v := inv_smul_smul g v
    · intro hh
      calc h • g • v = g • g⁻¹ • h • g • v := (smul_inv_smul g _).symm
        _ = g • (g⁻¹ * h * g) • v := by rw [mul_smul, mul_smul]
        _ = g • v := by rw [hh]
  rw [hset]
  exact hv.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem isSmoothVector_zero [AddMonoid M] [DistribMulAction G M] :
    IsSmoothVector G (0 : M) := by
  rw [isSmoothVector_iff_isOpen_stabilizer]
  have h : ((MulAction.stabilizer G (0 : M) : Subgroup G) : Set G) = Set.univ := by
    ext g
    simp [MulAction.mem_stabilizer_iff]
  rw [h]
  exact isOpen_univ

theorem IsSmoothVector.add [AddMonoid M] [DistribMulAction G M] [ContinuousMul G] {v w : M}
    (hv : IsSmoothVector G v) (hw : IsSmoothVector G w) : IsSmoothVector G (v + w) := by
  rw [isSmoothVector_iff_isOpen_stabilizer] at hv hw ⊢
  refine Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G v ⊓ MulAction.stabilizer G w) (fun g hg => ?_) ?_
  · obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    rw [MulAction.mem_stabilizer_iff] at hg1 hg2 ⊢
    rw [smul_add, hg1, hg2]
  · rw [Subgroup.coe_inf]
    exact hv.inter hw

theorem IsSmoothVector.const_smul [MulAction G M] [ContinuousMul G] {R : Type*} [SMul R M]
    [SMulCommClass G R M] {v : M} (hv : IsSmoothVector G v) (r : R) :
    IsSmoothVector G (r • v) := by
  rw [isSmoothVector_iff_isOpen_stabilizer] at hv ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G v) (fun g hg => ?_) hv
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [smul_comm, hg]

end Stability

section Submodule

variable (G : Type*) [Group G] [TopologicalSpace G] [ContinuousMul G]
variable (R : Type*) [Semiring R]
variable (M : Type*) [AddCommMonoid M] [Module R M]
variable [DistribMulAction G M] [SMulCommClass G R M]

def smoothVectors : Submodule R M where
  carrier := {v : M | IsSmoothVector G v}
  zero_mem' := isSmoothVector_zero
  add_mem' hv hw := hv.add hw
  smul_mem' r _v hv := hv.const_smul r

variable {G R M}

@[simp]
theorem mem_smoothVectors_iff {v : M} : v ∈ smoothVectors G R M ↔ IsSmoothVector G v :=
  Iff.rfl

theorem smul_mem_smoothVectors (g : G) {v : M} (hv : v ∈ smoothVectors G R M) :
    g • v ∈ smoothVectors G R M :=
  IsSmoothVector.smul hv g

theorem smul_mem_smoothVectors_iff (g : G) {v : M} :
    g • v ∈ smoothVectors G R M ↔ v ∈ smoothVectors G R M := by
  constructor
  · intro hv
    have h := smul_mem_smoothVectors g⁻¹ hv
    rwa [inv_smul_smul] at h
  · exact smul_mem_smoothVectors g

end Submodule

section Restriction

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [MulAction G M]

theorem IsSmoothVector.restrict_subgroup {v : M} (hv : IsSmoothVector G v) (H : Subgroup G) :
    IsSmoothVector H v := by
  rw [isSmoothVector_iff_isOpen_stabilizer] at hv ⊢
  have hset : ((MulAction.stabilizer H v : Subgroup H) : Set H)
      = (Subtype.val : H → G) ⁻¹' ((MulAction.stabilizer G v : Subgroup G) : Set G) := by
    ext h
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff,
      Subgroup.smul_def]
  rw [hset]
  exact hv.preimage continuous_subtype_val

theorem IsSmoothVector.of_isOpen_subgroup [ContinuousMul G] {v : M} (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (hv : IsSmoothVector H v) : IsSmoothVector G v := by
  rw [isSmoothVector_iff_isOpen_stabilizer] at hv ⊢
  refine Subgroup.isOpen_mono (H₁ := (MulAction.stabilizer H v).map H.subtype)
    (fun g hg => ?_) ?_
  · obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
    rw [MulAction.mem_stabilizer_iff] at hh ⊢
    rw [Subgroup.smul_def] at hh
    simpa using hh
  · rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hH.isOpenEmbedding_subtypeVal.isOpenMap _ hv

theorem isOpen_coe_inf_stabilizer {v w : M} (hv : IsSmoothVector G v)
    (hw : IsSmoothVector G w) :
    IsOpen ((MulAction.stabilizer G v ⊓ MulAction.stabilizer G w : Subgroup G) : Set G) := by
  rw [isSmoothVector_iff_isOpen_stabilizer] at hv hw
  rw [Subgroup.coe_inf]
  exact hv.inter hw

theorem exists_isOpen_subgroup_forall_smul_eq {ι : Type*} (s : Finset ι) (v : ι → M)
    (hv : ∀ i ∈ s, IsSmoothVector G (v i)) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ i ∈ s, ∀ u ∈ U, u • v i = v i := by
  classical
  refine ⟨⨅ i : s, MulAction.stabilizer G (v i), ?_, ?_⟩
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i =>
      (isSmoothVector_iff_isOpen_stabilizer (G := G) (v i)).mp (hv i i.2)
  · intro i hi u hu
    have h := Subgroup.mem_iInf.mp hu (⟨i, hi⟩ : s)
    exact MulAction.mem_stabilizer_iff.mp h

end Restriction

def RightTranslationFn (G M : Type*) : Type _ := G → M

namespace RightTranslationFn

variable {G M : Type*}

def mk (f : G → M) : RightTranslationFn G M := f

def toFun (f : RightTranslationFn G M) : G → M := f

@[simp] theorem toFun_mk (f : G → M) : toFun (mk f) = f := rfl

@[simp] theorem mk_toFun (f : RightTranslationFn G M) : mk (toFun f) = f := rfl

theorem ext {f g : RightTranslationFn G M} (h : ∀ x, toFun f x = toFun g x) : f = g :=
  funext h

instance [AddCommMonoid M] : AddCommMonoid (RightTranslationFn G M) :=
  inferInstanceAs (AddCommMonoid (G → M))

instance [Group G] : MulAction G (RightTranslationFn G M) where
  smul g f := mk fun x => toFun f (x * g)
  one_smul f := ext fun x => congrArg (toFun f) (mul_one x)
  mul_smul g h f := ext fun x => (congrArg (toFun f) (mul_assoc x g h)).symm

@[simp]
theorem toFun_smul [Group G] (g : G) (f : RightTranslationFn G M) (x : G) :
    toFun (g • f) x = toFun f (x * g) := rfl

instance [Group G] [AddCommMonoid M] : DistribMulAction G (RightTranslationFn G M) where
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

end RightTranslationFn

section Engine

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable {M : Type*} [Zero M]

theorem isSmoothVector_rightTranslationFn_of_isLocallyConstant_of_hasCompactSupport
    [NonarchimedeanGroup G] {f : G → M}
    (hlc : IsLocallyConstant f) (hsupp : HasCompactSupport f) :
    IsSmoothVector G (RightTranslationFn.mk f) := by
  classical

  have key : ∀ x : G, ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ v ∈ V, f (x * v) = f x := by
    intro x
    obtain ⟨U, hUopen, hxU, hUconst⟩ := hlc.exists_open x
    have h1 : (fun v : G => x * v) ⁻¹' U ∈ 𝓝 (1 : G) :=
      (hUopen.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using hxU)
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ h1
    exact ⟨V.toSubgroup, V.isOpen, fun v hv => hUconst _ (hV hv)⟩
  choose V hVopen hVconst using key

  set T : G → Set G := fun x => (fun y : G => x⁻¹ * y) ⁻¹' (V x : Set G) with hTdef
  have hTopen : ∀ x, IsOpen (T x) := fun x =>
    (hVopen x).preimage (continuous_const.mul continuous_id)
  have hmemT : ∀ x, x ∈ T x := fun x => by
    show x⁻¹ * x ∈ (V x : Set G)
    rw [inv_mul_cancel]
    exact (V x).one_mem
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hsupp
    (fun x : tsupport f => T (x : G)) (fun x => hTopen (x : G))
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hmemT y⟩)

  set W : Subgroup G := ⨅ x : t, V ((x : tsupport f) : G) with hWdef
  have hWopen : IsOpen (W : Set G) := by
    rw [hWdef, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun x => hVopen _
  have hWle : ∀ (x : tsupport f), x ∈ t → W ≤ V (x : G) := by
    intro x hx
    rw [hWdef]
    exact iInf_le _ (⟨x, hx⟩ : t)

  have hfix : ∀ w ∈ W, ∀ y : G, f (y * w) = f y := by
    intro w hw y
    by_cases hy : ∃ x : tsupport f, x ∈ t ∧ y ∈ T (x : G)
    · obtain ⟨x, hxt, hyx⟩ := hy
      have hv : (x : G)⁻¹ * y ∈ V (x : G) := hyx
      have hvw : (x : G)⁻¹ * (y * w) ∈ V (x : G) := by
        have heq : (x : G)⁻¹ * (y * w) = ((x : G)⁻¹ * y) * w := by rw [mul_assoc]
        rw [heq]
        exact (V (x : G)).mul_mem hv (hWle x hxt hw)
      have h1 : f (y * w) = f (x : G) := by
        have h2 := hVconst (x : G) _ hvw
        rwa [mul_inv_cancel_left] at h2
      have h3 : f y = f (x : G) := by
        have h4 := hVconst (x : G) _ hv
        rwa [mul_inv_cancel_left] at h4
      rw [h1, h3]
    · have hy' : ∀ x : tsupport f, x ∈ t → y ∉ T (x : G) := fun x hx hmem => hy ⟨x, hx, hmem⟩
      have hy1 : y ∉ tsupport f := by
        intro hmem
        obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hmem)
        exact hy' x hxt hyx
      have hy2 : y * w ∉ tsupport f := by
        intro hmem
        obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hmem)
        refine hy' x hxt ?_
        have hvw : (x : G)⁻¹ * (y * w) ∈ V (x : G) := hyx
        have heq : (x : G)⁻¹ * y = ((x : G)⁻¹ * (y * w)) * w⁻¹ := by group
        show (x : G)⁻¹ * y ∈ (V (x : G) : Set G)
        rw [heq]
        exact (V (x : G)).mul_mem hvw ((V (x : G)).inv_mem (hWle x hxt hw))
      rw [image_eq_zero_of_notMem_tsupport hy1, image_eq_zero_of_notMem_tsupport hy2]

  rw [isSmoothVector_iff_isOpen_stabilizer]
  refine Subgroup.isOpen_mono (H₁ := W) (fun w hw => ?_) hWopen
  rw [MulAction.mem_stabilizer_iff]
  exact RightTranslationFn.ext fun y => hfix w hw y

end Engine

end FLT.SmoothVectors


