-- Prove2me | Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
-- name    : AlgebraicGeometry_OrderedAffineCoverCech
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/6955efb9-bac7-56d8-9a58-a8dc9328fc66
-- title:
--   Ordered affine covers and Čech complexes of module-presheaves
-- statement:
--   For a scheme $V$, `Scheme.OrderedAffineCover` packages a finite linearly ordered index type $\iota$, opens $U_i \subseteq V$, proofs that each $U_i$ is affine, and the condition $\bigsqcup_i U_i = \top$. Attached to a cover $K$ are `Idx i`, the type of strictly monotone maps $\mathrm{Fin}(i+1) \to \iota$ (i.e. chains $s_0 < \dots < s_i$), a finite type; `inter s`, the open $\bigwedge_j U_{s_j}$; and `face s j`, the chain obtained by precomposing $s$ with `Fin.succAbove j`, that is by deleting the $j$-th entry. Two order lemmas record $\mathrm{inter}\,s \le U_{s_j}$ and $\mathrm{inter}\,s \le \mathrm{inter}(\mathrm{face}\,s\,j)$. `ofAffine` is the one-element cover of an affine scheme by $\top$, and `toOrderedAffineCover` turns a two-affine open cover $(U_0,U_1)$ into an ordered cover indexed by $\{0<1\}$.
--
--   Given a commutative ring $R$ and a morphism $\pi\colon V \to \operatorname{Spec} R$, `OModulePresheaf π` is a datum: abelian groups $F(U)$ for each open $U$, with compatible $R$- and $\Gamma(V,U)$-module structures (the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$), $R$-linear restrictions $F(U') \to F(U)$ for $U \le U'$ satisfying semilinearity $\mathrm{res}(a\cdot x) = a|_U \cdot \mathrm{res}\,x$, $\mathrm{res}_{U\le U} = \mathrm{id}$ and transitivity. No sheaf axiom is imposed. The alternating Čech objects are `cochain K i` $= \prod_{s \in \mathrm{Idx}\,i} F(\mathrm{inter}\,s)$ with differential $(dc)_s = \sum_j (-1)^j\, c_{\mathrm{face}\,s\,j}|_{\mathrm{inter}\,s}$; `H0` is the submodule $\ker d^0$ and `HSucc i` the quotient of $\ker d^{i+1}$ by the preimage of $\operatorname{im} d^{i}$ under the inclusion of $\ker d^{i+1}$. Four predicates follow: `CechFinite K` (all these are finite $R$-modules), `IsCoherent` ($F(U)$ finite over $\Gamma(V,U)$ for every affine open $U$), `IsQuasicoherent` (for affine $U$ and $f \in \Gamma(V,U)$: every section over the basic open $D(f)$ becomes a restriction after multiplication by some $f^n$, and a section of $F(U)$ restricting to $0$ is killed by some $f^n$), and `SupportedIn Y` ($F(U)$ is a subsingleton for every affine open $U$ disjoint from the closed set $Y$). `unit π` is the datum $U \mapsto \Gamma(V,U)$ with restriction of functions, and `twoChartSections` reads off from $F$ and a two-affine open cover the two-chart sections datum $(F(U_0), F(U_1), F(U_0 \wedge U_1))$ with the two restrictions. Small bridge lemmas unfold each predicate and each component.
--
--   **Relation to Mathlib.** Mathlib's affine open covers carry no linear order on the index type, and its presheaves of modules are set up categorically; the structures here are the project's own elementwise variants, with the Čech complex written directly as a product of modules over strictly monotone chains and quasi-coherence and coherence stated as predicates on the datum rather than derived from Mathlib's sheaf-theoretic definitions.
--
--   **Where it is used.** These definitions supply the vocabulary in which Čech cohomology of coherent and quasi-coherent data on schemes over $\operatorname{Spec} R$, and its finiteness, are phrased in the geometric parts of the formalisation; the two-chart specialisation connects them with the two-term Čech machinery used for covers by two affine opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Pi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

structure Scheme.OrderedAffineCover (V : Scheme.{u}) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → V.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  iSup_eq_top : ⨆ i, U i = ⊤

attribute [instance] Scheme.OrderedAffineCover.instFintype Scheme.OrderedAffineCover.instLinearOrder

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

instance instFintypeIdx (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _

instance instDecidableEqIdx (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem face_val {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : (K.face s j).1 = s.1 ∘ Fin.succAbove j :=
  rfl

theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) := iInf_le _ j

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

variable (V) in

def ofAffine [IsAffine V] : V.OrderedAffineCover where
  ι := PUnit.{u + 1}
  U _ := ⊤
  isAffineOpen _ := isAffineOpen_top V
  iSup_eq_top := iSup_const

theorem ofAffine_U [IsAffine V] (i : PUnit.{u + 1}) : (ofAffine V).U i = ⊤ := rfl

end Scheme.OrderedAffineCover

namespace Scheme.TwoAffineOpenCover

variable {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)

def toOrderedAffineCover : X.OrderedAffineCover where
  ι := ULift.{u} (Fin 2)
  instLinearOrder := LinearOrder.lift' ULift.down ULift.down_injective
  U i := ![𝒱.U0, 𝒱.U1] i.down
  isAffineOpen i := by
    rcases i with ⟨i⟩
    fin_cases i
    · exact 𝒱.isAffineOpen_U0
    · exact 𝒱.isAffineOpen_U1
  iSup_eq_top := by
    rw [eq_top_iff, ← 𝒱.sup_eq_top]
    exact sup_le (le_iSup (fun i : ULift.{u} (Fin 2) => ![𝒱.U0, 𝒱.U1] i.down) ⟨0⟩)
      (le_iSup (fun i : ULift.{u} (Fin 2) => ![𝒱.U0, 𝒱.U1] i.down) ⟨1⟩)

theorem toOrderedAffineCover_ι : 𝒱.toOrderedAffineCover.ι = ULift.{u} (Fin 2) := rfl
theorem toOrderedAffineCover_U_zero : 𝒱.toOrderedAffineCover.U ⟨0⟩ = 𝒱.U0 := rfl
theorem toOrderedAffineCover_U_one : 𝒱.toOrderedAffineCover.U ⟨1⟩ = 𝒱.U1 := rfl
theorem toOrderedAffineCover_U (i : ULift.{u} (Fin 2)) : 𝒱.toOrderedAffineCover.U i = ![𝒱.U0, 𝒱.U1] i.down := rfl

end Scheme.TwoAffineOpenCover

structure OModulePresheaf {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) where

  obj : V.Opens → Type u
  [addCommGroup : ∀ U, AddCommGroup (obj U)]

  [module : ∀ U, Module R (obj U)]

  [moduleSections : ∀ U, Module Γ(V, U) (obj U)]

  [isScalarTower : ∀ U, letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    IsScalarTower R Γ(V, U) (obj U)]

  res : ∀ {U U' : V.Opens}, U ≤ U' → obj U' →ₗ[R] obj U

  res_smul : ∀ {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : obj U'),
    res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x

  res_refl : ∀ U, res (le_refl U) = LinearMap.id

  res_comp : ∀ {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U''), res (h.trans h') = res h ∘ₗ res h'

attribute [instance] OModulePresheaf.addCommGroup OModulePresheaf.module OModulePresheaf.moduleSections
  OModulePresheaf.isScalarTower

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem res_refl_apply (U : V.Opens) (x : F.obj U) : F.res (le_refl U) x = x := by
  rw [F.res_refl]; rfl

theorem res_res {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U'') (x : F.obj U'') :
    F.res h (F.res h' x) = F.res (h.trans h') x := by
  rw [F.res_comp h h']; rfl

abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, F.obj (K.inter s)

def d (i : ℕ) : F.cochain K i →ₗ[R] F.cochain K (i + 1) :=
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

theorem d_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx (i + 1)) :
    F.d K i c s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) • F.res (K.inter_le_inter_face s j) (c (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

abbrev H0 : Submodule R (F.cochain K 0) := LinearMap.ker (F.d K 0)

abbrev HSucc (i : ℕ) : Type u :=
  LinearMap.ker (F.d K (i + 1)) ⧸ (LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype

def CechFinite : Prop := Module.Finite R (F.H0 K) ∧ ∀ i, Module.Finite R (F.HSucc K i)

theorem cechFinite_iff : F.CechFinite K ↔ Module.Finite R (F.H0 K) ∧ ∀ i, Module.Finite R (F.HSucc K i) :=
  Iff.rfl

def IsCoherent : Prop := ∀ U : V.affineOpens, Module.Finite Γ(V, U.1) (F.obj U.1)

theorem isCoherent_iff : F.IsCoherent ↔ ∀ U : V.affineOpens, Module.Finite Γ(V, U.1) (F.obj U.1) := Iff.rfl

def IsQuasicoherent : Prop :=
  ∀ (U : V.affineOpens) (f : Γ(V, U.1)),
    (∀ x : F.obj (V.basicOpen f), ∃ (n : ℕ) (y : F.obj U.1),
        F.res (V.basicOpen_le f) y = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x)
      ∧ (∀ y : F.obj U.1, F.res (V.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • y = 0)

theorem isQuasicoherent_iff : F.IsQuasicoherent ↔
    ∀ (U : V.affineOpens) (f : Γ(V, U.1)),
      (∀ x : F.obj (V.basicOpen f), ∃ (n : ℕ) (y : F.obj U.1),
          F.res (V.basicOpen_le f) y = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x)
        ∧ (∀ y : F.obj U.1, F.res (V.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • y = 0) :=
  Iff.rfl

def SupportedIn (Y : Closeds V) : Prop :=
  ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Y = ∅ → Subsingleton (F.obj U)

theorem supportedIn_iff (Y : Closeds V) :
    F.SupportedIn Y ↔ ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Y = ∅ → Subsingleton (F.obj U) :=
  Iff.rfl

variable (π) in

def unit : OModulePresheaf π where
  obj U := Γ(V, U)
  addCommGroup _ := inferInstance
  module U := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule
  moduleSections _ := Semiring.toModule
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact IsScalarTower.right
  res {U U'} h :=
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U'
    (Scheme.TwoAffineOpenCover.restrictAlgHom π h).toLinearMap
  res_smul h a x := by
    show (V.presheaf.map (homOfLE h).op).hom (a * x)
      = (V.presheaf.map (homOfLE h).op).hom a * (V.presheaf.map (homOfLE h).op).hom x
    exact map_mul _ a x
  res_refl U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    refine LinearMap.ext fun x => ?_
    show (V.presheaf.map (homOfLE (le_refl U)).op).hom x = x
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), V.presheaf.map_id]; rfl
  res_comp {U U' U''} h h' := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U''
    refine LinearMap.ext fun x => ?_
    show (V.presheaf.map (homOfLE (h.trans h')).op).hom x
      = (V.presheaf.map (homOfLE h).op).hom ((V.presheaf.map (homOfLE h').op).hom x)
    rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem unit_obj (U : V.Opens) : (unit π).obj U = Γ(V, U) := rfl

theorem unit_res_apply {U U' : V.Opens} (h : U ≤ U') (x : Γ(V, U')) :
    (unit π).res h (show (unit π).obj U' from x) = (V.presheaf.map (homOfLE h).op).hom x :=
  rfl

theorem unit_smul (U : V.Opens) (a x : Γ(V, U)) :
    a • (show (unit π).obj U from x) = (show (unit π).obj U from a * x) := rfl

theorem unit_algebraMap_smul (U : V.Opens) (r : R) (x : Γ(V, U)) :
    r • (show (unit π).obj U from x)
      = (show (unit π).obj U from (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r * x) :=
  rfl

section TwoChart

variable (𝒱 : V.TwoAffineOpenCover)

def twoChartSections : TwoChartCech.Sections (𝒱.cover π) :=
  letI : Module (𝒱.cover π).A0 (F.obj 𝒱.U0) := inferInstanceAs (Module Γ(V, 𝒱.U0) (F.obj 𝒱.U0))
  letI : Module (𝒱.cover π).A1 (F.obj 𝒱.U1) := inferInstanceAs (Module Γ(V, 𝒱.U1) (F.obj 𝒱.U1))
  letI : Module (𝒱.cover π).A01 (F.obj (𝒱.U0 ⊓ 𝒱.U1)) :=
    inferInstanceAs (Module Γ(V, 𝒱.U0 ⊓ 𝒱.U1) (F.obj (𝒱.U0 ⊓ 𝒱.U1)))
  haveI : IsScalarTower R (𝒱.cover π).A0 (F.obj 𝒱.U0) := F.isScalarTower 𝒱.U0
  haveI : IsScalarTower R (𝒱.cover π).A1 (F.obj 𝒱.U1) := F.isScalarTower 𝒱.U1
  haveI : IsScalarTower R (𝒱.cover π).A01 (F.obj (𝒱.U0 ⊓ 𝒱.U1)) := F.isScalarTower (𝒱.U0 ⊓ 𝒱.U1)
  { M0 := F.obj 𝒱.U0
    M1 := F.obj 𝒱.U1
    M01 := F.obj (𝒱.U0 ⊓ 𝒱.U1)
    r0 := F.res inf_le_left
    r1 := F.res inf_le_right
    r0_smul := fun a m => F.res_smul inf_le_left a m
    r1_smul := fun a m => F.res_smul inf_le_right a m }

theorem twoChartSections_M0 : (F.twoChartSections 𝒱).M0 = F.obj 𝒱.U0 := rfl
theorem twoChartSections_M1 : (F.twoChartSections 𝒱).M1 = F.obj 𝒱.U1 := rfl
theorem twoChartSections_M01 : (F.twoChartSections 𝒱).M01 = F.obj (𝒱.U0 ⊓ 𝒱.U1) := rfl
theorem twoChartSections_r0_apply (x : F.obj 𝒱.U0) :
    (F.twoChartSections 𝒱).r0 (show (F.twoChartSections 𝒱).M0 from x) = F.res inf_le_left x := rfl
theorem twoChartSections_r1_apply (x : F.obj 𝒱.U1) :
    (F.twoChartSections 𝒱).r1 (show (F.twoChartSections 𝒱).M1 from x) = F.res inf_le_right x := rfl

end TwoChart

end OModulePresheaf

end AlgebraicGeometry

end


