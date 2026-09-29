-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
-- name    : AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/c464389e-8f3e-5427-b64c-a30cbf853cd8
-- title:
--   Graded module of frame-wise twisted sections of a family
-- statement:
--   Throughout, $A$ is a commutative ring, $\iota : P \to \operatorname{Proj} A[x_0,\dots,x_r]$ and $q : P \to \operatorname{Spec} A$ are morphisms of schemes, $U_j = \iota^{-1}D_+(x_j)$ and $U_{jl} = \iota^{-1}D_+(x_jx_l)$ are the pulled-back charts and overlaps, $u_{jl} \in \Gamma(P,U_j)$ is the frame unit $\iota^\sharp(x_l/x_j)$, and the module data are objects of `OModulePresheaf q`, i.e. presheaf-like assignments $U \mapsto F(U)$ with compatible $A$- and $\Gamma(P,U)$-actions and restriction maps, with no sheaf condition imposed. For such an $F$, a natural number $d$ and a family $t_j \in F(U_j)$, `FramesCompat` asserts the transition rule of $\mathcal O(d)$ in these frames: $t_j|_{U_{jl}} = (u_{jl}|_{U_{jl}})^d \, t_l|_{U_{jl}}$ for all $j,l$. This condition is closed under addition and under the $A$-action, and multiplying $t_j$ by $u_{jl_0}$ raises $d$ by one, by the cocycle identity for the frame units.
--
--   Given a sequence $(G_k)_{k\ge 0}$ of module data, `FamilyFrames` is the $A$-module of all families $f(e,k,j) \in G_k(U_j)$ indexed by a degree $e \in \mathbb Z$, a level $k$ and a chart $j$, with `xEnd` $l$ the commuting $A$-linear operators $(x_l f)(e,k,j) = u_{jl}\,f(e-1,k,j)$. An element is `IsHomogeneousElem` of degree $e$ when it is supported in degree $e$, vanishes when $e<0$, has each level frames-compatible of degree $e$ when $e \ge 0$, and is non-zero at only finitely many levels; `FamilyFrames.single` places a single family at one degree and level, and homogeneity of such an element is characterised exactly by the two remaining conditions.
--
--   In the second half, $\iota$ is affine, so the charts and overlaps are affine opens, and $\theta_1,\dots,\theta_s$ are level-raising morphisms $G_k \to G_{k+1}$ defined on affine opens. `yEnd` $m$ shifts the level by applying $\theta_m$, killing level $0$; it commutes with the `xEnd`. Under `YComm`, the assertion that the $\theta$'s commute in the evident sense, `polyEnd` is the $A$-algebra map $A[y_1,\dots,y_s] \to \operatorname{End}_A$ sending $y_m$ to `yEnd` $m$, and `polyModule` the resulting module structure. `familyFramesGradedModule` packages this as a [`ProjSpaceCech.GradedModule`](../def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18) over $A[y_1,\dots,y_s]$ with $r+1$ variables: the module is `FamilyFrames`, the grading is by the homogeneous elements, and the commuting degree-raising operators are the `xEnd`. Further lemmas compute the action of a monomial $\prod_l x_l^{c_l}$ as multiplication by $\prod_l u_{jl}^{c_l}$ together with a degree shift by $\sum_l c_l$.
--
--   **Relation to Mathlib.** Mathlib has no frame-wise model of twisted sections of this kind; `OModulePresheaf`, `AffHom` and [`ProjSpaceCech.GradedModule`](../def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18) are the project's own notions, built on Mathlib's `Proj` of `MvPolynomial.homogeneousSubmodule` and its homogeneous localisations.
--
--   **Where it is used.** The construction turns a family of module data on $P$ with commuting level-raising operators into a single graded module over $A[y_1,\dots,y_s][x_0,\dots,x_r]$, in the shape required by the project's Čech machinery for $\operatorname{Proj}$, where cohomology of twists and its finiteness and base-change behaviour are analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace OModulePresheaf

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  {q : P ⟶ Spec (.of A)}

theorem sections_smul_comm (F : OModulePresheaf q) (U : P.Opens) (a : A) (f : Γ(P, U)) (x : F.obj U) :
    f • (a • x) = a • (f • x) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  haveI : IsScalarTower A Γ(P, U) (F.obj U) := F.isScalarTower U
  exact smul_algebra_smul_comm a f x

section FramesCompat

def FramesCompat (F : OModulePresheaf q) (d : ℕ) (t : ∀ j : Fin (r + 1), F.obj (ProjSpace.pullbackChart ι j)) : Prop :=
  ∀ j l : Fin (r + 1),
    F.res (ProjSpace.pullbackOverlap_le_left ι j l) (t j) =
      ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι j l) (ProjSpace.frameUnit ι j l) ^ d •
        F.res (ProjSpace.pullbackOverlap_le_right ι j l) (t l)

variable {ι}

theorem framesCompat_iff (F : OModulePresheaf q) (d : ℕ) (t : ∀ j : Fin (r + 1), F.obj (ProjSpace.pullbackChart ι j)) :
    FramesCompat ι F d t ↔ ∀ j l : Fin (r + 1),
      F.res (ProjSpace.pullbackOverlap_le_left ι j l) (t j) =
        ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι j l) (ProjSpace.frameUnit ι j l) ^ d •
          F.res (ProjSpace.pullbackOverlap_le_right ι j l) (t l) :=
  Iff.rfl

theorem FramesCompat.zero (F : OModulePresheaf q) (d : ℕ) : FramesCompat ι F d 0 := fun j l => by
  simp only [Pi.zero_apply, map_zero, smul_zero]

theorem FramesCompat.add {F : OModulePresheaf q} {d : ℕ} {t t' : ∀ j : Fin (r + 1), F.obj (ProjSpace.pullbackChart ι j)}
    (ht : FramesCompat ι F d t) (ht' : FramesCompat ι F d t') : FramesCompat ι F d (t + t') := fun j l => by
  simp only [Pi.add_apply, map_add, smul_add, ht j l, ht' j l]

theorem FramesCompat.smul {F : OModulePresheaf q} {d : ℕ} {t : ∀ j : Fin (r + 1), F.obj (ProjSpace.pullbackChart ι j)}
    (ht : FramesCompat ι F d t) (a : A) : FramesCompat ι F d (a • t) := fun j l => by
  simp only [Pi.smul_apply, map_smul, ht j l, sections_smul_comm]

theorem FramesCompat.frameUnit_smul {F : OModulePresheaf q} {d : ℕ}
    {t : ∀ j : Fin (r + 1), F.obj (ProjSpace.pullbackChart ι j)} (ht : FramesCompat ι F d t) (l₀ : Fin (r + 1)) :
    FramesCompat ι F (d + 1) (fun j => ProjSpace.frameUnit ι j l₀ • t j) := fun j l => by
  rw [F.res_smul, F.res_smul, ht j l, smul_smul, smul_smul, pow_succ, ← ProjSpace.frameUnit_cocycle ι j l l₀]
  congr 1
  show _ = _ * _ * ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right ι j l) (ProjSpace.frameUnit ι l l₀)
  ring

end FramesCompat

section Ambient

variable (G : ℕ → OModulePresheaf q)

def FamilyFrames : Type u := ℤ → (k : ℕ) → (j : Fin (r + 1)) → (G k).obj (ProjSpace.pullbackChart ι j)

instance FamilyFrames.addCommGroup : AddCommGroup (FamilyFrames ι G) :=
  inferInstanceAs (AddCommGroup (ℤ → (k : ℕ) → (j : Fin (r + 1)) → (G k).obj (ProjSpace.pullbackChart ι j)))

instance FamilyFrames.module : Module A (FamilyFrames ι G) :=
  inferInstanceAs (Module A (ℤ → (k : ℕ) → (j : Fin (r + 1)) → (G k).obj (ProjSpace.pullbackChart ι j)))

variable {ι G}

theorem FamilyFrames.zero_apply (e : ℤ) (k : ℕ) (j : Fin (r + 1)) : (0 : FamilyFrames ι G) e k j = 0 := rfl

theorem FamilyFrames.add_apply (f g : FamilyFrames ι G) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    (f + g) e k j = f e k j + g e k j := rfl

theorem FamilyFrames.neg_apply (f : FamilyFrames ι G) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    (-f) e k j = -f e k j := rfl

theorem FamilyFrames.sub_apply (f g : FamilyFrames ι G) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    (f - g) e k j = f e k j - g e k j := rfl

theorem FamilyFrames.smul_apply (a : A) (f : FamilyFrames ι G) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    (a • f) e k j = a • f e k j := rfl

@[ext] theorem FamilyFrames.ext {f g : FamilyFrames ι G} (h : ∀ e k j, f e k j = g e k j) : f = g :=
  funext fun e => funext fun k => funext fun j => h e k j

variable (ι G)

def xEnd (l : Fin (r + 1)) : FamilyFrames ι G →ₗ[A] FamilyFrames ι G where
  toFun f := fun e k j => ProjSpace.frameUnit ι j l • f (e - 1) k j
  map_add' f g := by
    refine FamilyFrames.ext fun e k j => ?_
    exact smul_add _ _ _
  map_smul' a f := by
    refine FamilyFrames.ext fun e k j => ?_
    exact sections_smul_comm (G k) _ a _ _

theorem xEnd_apply (l : Fin (r + 1)) (f : FamilyFrames ι G) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    xEnd ι G l f e k j = ProjSpace.frameUnit ι j l • f (e - 1) k j := rfl

theorem xEnd_comm (l l' : Fin (r + 1)) : xEnd ι G l ∘ₗ xEnd ι G l' = xEnd ι G l' ∘ₗ xEnd ι G l := by
  refine LinearMap.ext fun f => FamilyFrames.ext fun e k j => ?_
  simp only [LinearMap.comp_apply, xEnd_apply, smul_smul, mul_comm]

def IsHomogeneousElem (e : ℤ) (f : FamilyFrames ι G) : Prop :=
  (∀ e' : ℤ, e' ≠ e → f e' = 0) ∧ (e < 0 → f e = 0) ∧
    (0 ≤ e → ∀ k : ℕ, FramesCompat ι (G k) e.toNat (f e k)) ∧ Set.Finite {k : ℕ | f e k ≠ 0}

variable {ι G}

theorem isHomogeneousElem_iff (e : ℤ) (f : FamilyFrames ι G) :
    IsHomogeneousElem ι G e f ↔ (∀ e' : ℤ, e' ≠ e → f e' = 0) ∧ (e < 0 → f e = 0) ∧
      (0 ≤ e → ∀ k : ℕ, FramesCompat ι (G k) e.toNat (f e k)) ∧ Set.Finite {k : ℕ | f e k ≠ 0} :=
  Iff.rfl

theorem IsHomogeneousElem.zero (e : ℤ) : IsHomogeneousElem ι G e 0 :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ k => FramesCompat.zero (G k) _, Set.finite_empty.subset fun _ hk => (hk rfl).elim⟩

theorem IsHomogeneousElem.add {e : ℤ} {f g : FamilyFrames ι G} (hf : IsHomogeneousElem ι G e f)
    (hg : IsHomogeneousElem ι G e g) : IsHomogeneousElem ι G e (f + g) := by
  refine ⟨fun e' he' => ?_, fun he => ?_, fun he k => ?_, ?_⟩
  · show f e' + g e' = 0
    rw [hf.1 e' he', hg.1 e' he', add_zero]
  · show f e + g e = 0
    rw [hf.2.1 he, hg.2.1 he, add_zero]
  · exact (hf.2.2.1 he k).add (hg.2.2.1 he k)
  · refine (hf.2.2.2.union hg.2.2.2).subset fun k hk => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hk (show f e k + g e k = 0 by rw [h.1, h.2, add_zero])

theorem IsHomogeneousElem.smul {e : ℤ} {f : FamilyFrames ι G} (hf : IsHomogeneousElem ι G e f) (a : A) :
    IsHomogeneousElem ι G e (a • f) := by
  refine ⟨fun e' he' => ?_, fun he => ?_, fun he k => (hf.2.2.1 he k).smul a, ?_⟩
  · show a • f e' = 0
    rw [hf.1 e' he', smul_zero]
  · show a • f e = 0
    rw [hf.2.1 he, smul_zero]
  · refine hf.2.2.2.subset fun k hk => ?_
    intro h
    exact hk (show a • f e k = 0 by rw [show f e k = 0 from h, smul_zero])

theorem IsHomogeneousElem.xEnd {e : ℤ} {f : FamilyFrames ι G} (hf : IsHomogeneousElem ι G e f) (l : Fin (r + 1)) :
    IsHomogeneousElem ι G (e + 1) (xEnd ι G l f) := by
  refine ⟨fun e' he' => ?_, fun he => ?_, fun he k => ?_, ?_⟩
  · funext k j
    rw [xEnd_apply, show f (e' - 1) k j = 0 from congrFun (congrFun (hf.1 (e' - 1) (by omega)) k) j, smul_zero]; rfl
  · funext k j
    rw [xEnd_apply, show e + 1 - 1 = e by ring, show f e k j = 0 from congrFun (congrFun (hf.2.1 (by omega)) k) j,
      smul_zero]; rfl
  · rcases lt_or_ge e 0 with hlt | hge
    · intro j l'
      have h0 : ∀ j', f e k j' = 0 := fun j' => congrFun (congrFun (hf.2.1 hlt) k) j'
      simp only [xEnd_apply, show e + 1 - 1 = e by ring, h0, smul_zero, map_zero]
    · have hc := (hf.2.2.1 hge k).frameUnit_smul l
      have hnat : (e + 1).toNat = e.toNat + 1 := by omega
      rw [hnat]
      show FramesCompat ι (G k) (e.toNat + 1) (fun j => ProjSpace.frameUnit ι j l • f (e + 1 - 1) k j)
      rw [show e + 1 - 1 = e by ring]
      exact hc
  · refine hf.2.2.2.subset fun k hk => ?_
    intro h
    refine hk ?_
    funext j
    rw [xEnd_apply, show e + 1 - 1 = e by ring, show f e k j = 0 from congrFun h j, smul_zero]; rfl

variable (ι G)

def FamilyFrames.single (e : ℤ) (k : ℕ) (t : ∀ j : Fin (r + 1), (G k).obj (ProjSpace.pullbackChart ι j)) :
    FamilyFrames ι G :=
  fun e' => if e' = e then Pi.single (M := fun k' : ℕ => ∀ j : Fin (r + 1), (G k').obj (ProjSpace.pullbackChart ι j)) k t
    else 0

variable {ι G}

theorem FamilyFrames.single_apply_self (e : ℤ) (k : ℕ) (t : ∀ j : Fin (r + 1), (G k).obj (ProjSpace.pullbackChart ι j)) :
    FamilyFrames.single ι G e k t e k = t := by
  simp only [FamilyFrames.single, if_true, Pi.single_eq_same]

theorem FamilyFrames.single_apply_of_ne_degree {e e' : ℤ} (h : e' ≠ e) (k : ℕ)
    (t : ∀ j : Fin (r + 1), (G k).obj (ProjSpace.pullbackChart ι j)) :
    FamilyFrames.single ι G e k t e' = 0 := by
  simp only [FamilyFrames.single, h, if_false]

theorem FamilyFrames.single_apply_of_ne_level (e e' : ℤ) {k k' : ℕ} (h : k' ≠ k)
    (t : ∀ j : Fin (r + 1), (G k).obj (ProjSpace.pullbackChart ι j)) :
    FamilyFrames.single ι G e k t e' k' = 0 := by
  unfold FamilyFrames.single
  split_ifs
  · exact Pi.single_eq_of_ne h _
  · rfl

theorem isHomogeneousElem_single_iff (e : ℤ) (k : ℕ) (t : ∀ j : Fin (r + 1), (G k).obj (ProjSpace.pullbackChart ι j)) :
    IsHomogeneousElem ι G e (FamilyFrames.single ι G e k t) ↔
      (e < 0 → t = 0) ∧ (0 ≤ e → FramesCompat ι (G k) e.toNat t) := by
  constructor
  · rintro ⟨-, h2, h3, -⟩
    refine ⟨fun he => ?_, fun he => ?_⟩
    · have := congrFun (h2 he) k
      rwa [FamilyFrames.single_apply_self] at this
    · simpa only [FamilyFrames.single_apply_self] using h3 he k
  · rintro ⟨h2, h3⟩
    refine ⟨fun e' he' => FamilyFrames.single_apply_of_ne_degree he' k t, fun he => ?_, fun he k' => ?_, ?_⟩
    · funext k'
      by_cases hk : k' = k
      · subst hk; rw [FamilyFrames.single_apply_self]; exact h2 he
      · exact FamilyFrames.single_apply_of_ne_level e e hk t
    · by_cases hk : k' = k
      · subst hk; rw [FamilyFrames.single_apply_self]; exact h3 he
      · rw [FamilyFrames.single_apply_of_ne_level e e hk t]; exact FramesCompat.zero (G k') _
    · refine (Set.finite_singleton k).subset fun k' hk' => ?_
      by_contra hk
      exact hk' (FamilyFrames.single_apply_of_ne_level e e hk t)

end Ambient

section Family

variable [IsAffineHom ι] (G : ℕ → OModulePresheaf q) {s : ℕ}
  (θ : Fin s → ∀ k : ℕ, AffHom (G k) (G (k + 1)))

abbrev framesChart (j : Fin (r + 1)) : P.affineOpens :=
  ⟨ProjSpace.pullbackChart ι j, ProjSpace.isAffineOpen_pullbackChart ι j⟩

abbrev framesOverlap (j l : Fin (r + 1)) : P.affineOpens :=
  ⟨ProjSpace.pullbackOverlap ι j l, ProjSpace.isAffineOpen_pullbackOverlap ι j l⟩

def ySucc (m : Fin s) (f : FamilyFrames ι G) (e : ℤ) :
    (k : ℕ) → (j : Fin (r + 1)) → (G k).obj (ProjSpace.pullbackChart ι j)
  | 0, _ => 0
  | k + 1, j => (θ m k).app (framesChart ι j) (f e k j)

theorem ySucc_zero (m : Fin s) (f : FamilyFrames ι G) (e : ℤ) (j : Fin (r + 1)) : ySucc ι G θ m f e 0 j = 0 := rfl

theorem ySucc_succ (m : Fin s) (f : FamilyFrames ι G) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    ySucc ι G θ m f e (k + 1) j = (θ m k).app (framesChart ι j) (f e k j) := rfl

def yEnd (m : Fin s) : FamilyFrames ι G →ₗ[A] FamilyFrames ι G where
  toFun f := fun e => ySucc ι G θ m f e
  map_add' f g := by
    refine FamilyFrames.ext fun e k j => ?_
    cases k with
    | zero => exact (add_zero (0 : (G 0).obj _)).symm
    | succ k => exact map_add _ _ _
  map_smul' a f := by
    refine FamilyFrames.ext fun e k j => ?_
    cases k with
    | zero => exact (smul_zero a).symm
    | succ k => exact LinearMap.map_smul _ _ _

theorem yEnd_apply_zero (m : Fin s) (f : FamilyFrames ι G) (e : ℤ) (j : Fin (r + 1)) : yEnd ι G θ m f e 0 j = 0 := rfl

theorem yEnd_apply_succ (m : Fin s) (f : FamilyFrames ι G) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    yEnd ι G θ m f e (k + 1) j = (θ m k).app (framesChart ι j) (f e k j) := rfl

theorem xEnd_comp_yEnd (l : Fin (r + 1)) (m : Fin s) : xEnd ι G l ∘ₗ yEnd ι G θ m = yEnd ι G θ m ∘ₗ xEnd ι G l := by
  refine LinearMap.ext fun f => FamilyFrames.ext fun e k j => ?_
  cases k with
  | zero => exact smul_zero _
  | succ k => exact ((θ m k).app_smul (framesChart ι j) _ _).symm

def YComm : Prop :=
  ∀ (m m' : Fin s) (k : ℕ) (U : P.affineOpens) (x : (G k).obj U.1),
    (θ m (k + 1)).app U ((θ m' k).app U x) = (θ m' (k + 1)).app U ((θ m k).app U x)

variable {ι G θ}

theorem yComm_iff : YComm G θ ↔ ∀ (m m' : Fin s) (k : ℕ) (U : P.affineOpens) (x : (G k).obj U.1),
    (θ m (k + 1)).app U ((θ m' k).app U x) = (θ m' (k + 1)).app U ((θ m k).app U x) := Iff.rfl

theorem yEnd_comm (hθ : YComm G θ) (m m' : Fin s) : yEnd ι G θ m ∘ₗ yEnd ι G θ m' = yEnd ι G θ m' ∘ₗ yEnd ι G θ m := by
  refine LinearMap.ext fun f => FamilyFrames.ext fun e k j => ?_
  match k with
  | 0 => rfl
  | 1 =>
    show (θ m 0).app _ (0 : (G 0).obj _) = (θ m' 0).app _ (0 : (G 0).obj _)
    rw [map_zero, map_zero]
  | k + 2 => exact hθ m m' k (framesChart ι j) (f e k j)

theorem yEnd_mul_comm (hθ : YComm G θ) (m m' : Fin s) :
    (yEnd ι G θ m * yEnd ι G θ m' : Module.End A (FamilyFrames ι G)) = yEnd ι G θ m' * yEnd ι G θ m :=
  yEnd_comm hθ m m'

variable (ι G θ)

open scoped IsMulCommutative in

def polyEnd (hθ : YComm G θ) : MvPolynomial (Fin s) A →ₐ[A] Module.End A (FamilyFrames ι G) :=
  haveI := Algebra.isMulCommutative_adjoin A (s := Set.range (yEnd ι G θ))
    (by rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩; exact yEnd_mul_comm hθ m m')
  (Algebra.adjoin A (Set.range (yEnd ι G θ))).val.comp
    (MvPolynomial.aeval fun m =>
      (⟨yEnd ι G θ m, Algebra.subset_adjoin ⟨m, rfl⟩⟩ : Algebra.adjoin A (Set.range (yEnd ι G θ))))

theorem polyEnd_X (hθ : YComm G θ) (m : Fin s) : polyEnd ι G θ hθ (MvPolynomial.X m) = yEnd ι G θ m := by
  simp only [polyEnd, AlgHom.comp_apply, MvPolynomial.aeval_X, Subalgebra.coe_val]

theorem polyEnd_C (hθ : YComm G θ) (a : A) (f : FamilyFrames ι G) : polyEnd ι G θ hθ (MvPolynomial.C a) f = a • f := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]

@[reducible] def polyModule (hθ : YComm G θ) : Module (MvPolynomial (Fin s) A) (FamilyFrames ι G) :=
  Module.compHom (FamilyFrames ι G) (polyEnd ι G θ hθ).toRingHom

theorem polyModule_smul_def (hθ : YComm G θ) (p : MvPolynomial (Fin s) A) (f : FamilyFrames ι G) :
    (letI := polyModule ι G θ hθ; p • f) = polyEnd ι G θ hθ p f := rfl

theorem xEnd_polyEnd (hθ : YComm G θ) (l : Fin (r + 1)) (p : MvPolynomial (Fin s) A) (f : FamilyFrames ι G) :
    xEnd ι G l (polyEnd ι G θ hθ p f) = polyEnd ι G θ hθ p (xEnd ι G l f) := by
  induction p using MvPolynomial.induction_on generalizing f with
  | C a => rw [polyEnd_C, polyEnd_C, LinearMap.map_smul]
  | add p p' hp hp' => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hp']
  | mul_X p m hp =>
    rw [map_mul, polyEnd_X, Module.End.mul_apply, Module.End.mul_apply, hp]
    exact congrArg (polyEnd ι G θ hθ p) (LinearMap.congr_fun (xEnd_comp_yEnd ι G θ l m) f)

variable {ι G θ}

theorem IsHomogeneousElem.yEnd {e : ℤ} {f : FamilyFrames ι G} (hf : IsHomogeneousElem ι G e f) (m : Fin s) :
    IsHomogeneousElem ι G e (yEnd ι G θ m f) := by
  refine ⟨fun e' he' => ?_, fun he => ?_, fun he k => ?_, ?_⟩
  · funext k j
    cases k with
    | zero => rfl
    | succ k =>
      rw [yEnd_apply_succ, show f e' k j = 0 from congrFun (congrFun (hf.1 e' he') k) j, map_zero]; rfl
  · funext k j
    cases k with
    | zero => rfl
    | succ k =>
      rw [yEnd_apply_succ, show f e k j = 0 from congrFun (congrFun (hf.2.1 he) k) j, map_zero]; rfl
  · cases k with
    | zero => exact FramesCompat.zero (G 0) _
    | succ k =>
      intro j l
      have hc := hf.2.2.1 he k j l
      show (G (k + 1)).res _ ((θ m k).app (framesChart ι j) (f e k j))
        = _ • (G (k + 1)).res _ ((θ m k).app (framesChart ι l) (f e k l))
      rw [← (θ m k).naturality_apply (U := framesOverlap ι j l) (U' := framesChart ι j),
        ← (θ m k).naturality_apply (U := framesOverlap ι j l) (U' := framesChart ι l), hc, (θ m k).app_smul]
  · refine (hf.2.2.2.image Nat.succ).subset fun k hk => ?_
    cases k with
    | zero => exact absurd rfl hk
    | succ k =>
      refine ⟨k, fun h => hk ?_, rfl⟩
      funext j
      rw [yEnd_apply_succ, show f e k j = 0 from congrFun h j, map_zero]; rfl

theorem IsHomogeneousElem.polyEnd (hθ : YComm G θ) {e : ℤ} {f : FamilyFrames ι G} (hf : IsHomogeneousElem ι G e f)
    (p : MvPolynomial (Fin s) A) : IsHomogeneousElem ι G e (polyEnd ι G θ hθ p f) := by
  induction p using MvPolynomial.induction_on generalizing f with
  | C a => rw [polyEnd_C]; exact hf.smul a
  | add p p' hp hp' => rw [map_add, LinearMap.add_apply]; exact (hp hf).add (hp' hf)
  | mul_X p m hp => rw [map_mul, polyEnd_X, Module.End.mul_apply]; exact hp (hf.yEnd m)

variable (ι G θ)

def familyFramesGradedModule (hθ : YComm G θ) : ProjSpaceCech.GradedModule (MvPolynomial (Fin s) A) r :=
  letI : Module (MvPolynomial (Fin s) A) (FamilyFrames ι G) := polyModule ι G θ hθ
  { M := FamilyFrames ι G
    grade := fun e =>
      { carrier := {f | IsHomogeneousElem ι G e f}
        zero_mem' := IsHomogeneousElem.zero e
        add_mem' := fun hf hg => hf.add hg
        smul_mem' := fun p _ hf => IsHomogeneousElem.polyEnd hθ hf p }
    xMul := fun l =>
      { toFun := xEnd ι G l
        map_add' := map_add _
        map_smul' := fun p f => xEnd_polyEnd ι G θ hθ l p f }
    xMul_mem_grade := fun l _ _ hf => IsHomogeneousElem.xEnd hf l
    xMul_comm := fun l l' => LinearMap.ext fun f => LinearMap.congr_fun (xEnd_comm ι G l l') f }

theorem familyFramesGradedModule_M (hθ : YComm G θ) : (familyFramesGradedModule ι G θ hθ).M = FamilyFrames ι G := rfl

instance familyFramesGradedModule.moduleBase (hθ : YComm G θ) : Module A (familyFramesGradedModule ι G θ hθ).M :=
  FamilyFrames.module ι G

variable {ι G θ}

theorem mem_grade_iff (hθ : YComm G θ) (e : ℤ) (f : (familyFramesGradedModule ι G θ hθ).M) :
    f ∈ (familyFramesGradedModule ι G θ hθ).grade e ↔ IsHomogeneousElem ι G e f := Iff.rfl

theorem xMul_apply (hθ : YComm G θ) (l : Fin (r + 1)) (f : (familyFramesGradedModule ι G θ hθ).M) :
    (familyFramesGradedModule ι G θ hθ).xMul l f = xEnd ι G l f := rfl

theorem xMul_apply_apply (hθ : YComm G θ) (l : Fin (r + 1)) (f : (familyFramesGradedModule ι G θ hθ).M)
    (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    (familyFramesGradedModule ι G θ hθ).xMul l f e k j = ProjSpace.frameUnit ι j l • f (e - 1) k j :=
  rfl

theorem smul_def (hθ : YComm G θ) (p : MvPolynomial (Fin s) A) (f : (familyFramesGradedModule ι G θ hθ).M) :
    p • f = polyEnd ι G θ hθ p f := rfl

theorem X_smul (hθ : YComm G θ) (m : Fin s) (f : (familyFramesGradedModule ι G θ hθ).M) :
    (MvPolynomial.X m : MvPolynomial (Fin s) A) • f = yEnd ι G θ m f := by
  rw [smul_def, polyEnd_X]

theorem C_smul (hθ : YComm G θ) (a : A) (f : (familyFramesGradedModule ι G θ hθ).M) :
    (MvPolynomial.C a : MvPolynomial (Fin s) A) • f = a • f := by
  rw [smul_def, polyEnd_C]; rfl

theorem base_smul_apply (hθ : YComm G θ) (a : A) (f : (familyFramesGradedModule ι G θ hθ).M) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    (a • f) e k j = a • f e k j := rfl

theorem xMul_pow_apply (hθ : YComm G θ) (l : Fin (r + 1)) (n : ℕ) (f : (familyFramesGradedModule ι G θ hθ).M)
    (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    ((familyFramesGradedModule ι G θ hθ).xMul l ^ n) f e k j = ProjSpace.frameUnit ι j l ^ n • f (e - n) k j := by
  induction n generalizing e with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, one_smul, Nat.cast_zero, sub_zero]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, xMul_apply_apply, ih (e - 1), smul_smul, ← pow_succ', Nat.cast_succ,
      show e - 1 - (n : ℤ) = e - (n + 1) by ring]

theorem monMul_apply (hθ : YComm G θ) (c : Fin (r + 1) → ℕ) (f : (familyFramesGradedModule ι G θ hθ).M)
    (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    ProjSpaceCech.GradedModule.monMul (familyFramesGradedModule ι G θ hθ) c f e k j
      = (∏ l, ProjSpace.frameUnit ι j l ^ c l) • f (e - ∑ l, (c l : ℤ)) k j := by
  suffices h : ∀ (t : Finset (Fin (r + 1))) (hc : _) (e' : ℤ),
      (t.noncommProd (fun l => (familyFramesGradedModule ι G θ hθ).xMul l ^ c l) hc) f e' k j
        = (∏ l ∈ t, ProjSpace.frameUnit ι j l ^ c l) • f (e' - ∑ l ∈ t, (c l : ℤ)) k j from
    h Finset.univ _ e
  intro t
  induction t using Finset.induction with
  | empty =>
    intro _ e'
    rw [Finset.noncommProd_empty, Module.End.one_apply, Finset.prod_empty, one_smul, Finset.sum_empty, sub_zero]
  | insert l t hl ih =>
    intro hc e'
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hl, Finset.prod_insert hl, Finset.sum_insert hl, Module.End.mul_apply,
      xMul_pow_apply, ih (hc.mono (by simp)) (e' - c l), smul_smul,
      show e' - (c l : ℤ) - ∑ x ∈ t, (c x : ℤ) = e' - ((c l : ℤ) + ∑ x ∈ t, (c x : ℤ)) by ring]

end Family

end OModulePresheaf

end AlgebraicGeometry

end


