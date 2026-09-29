-- Prove2me | Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
-- name    : AlgebraicGeometry_OrderedAffineCoverOf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/cf2c5e3f-3eb4-5e1f-879e-44e882928e72
-- title:
--   Ordered affine covers of an open subscheme; Čech complexes
-- statement:
--   For a scheme $V$ and an open $W \subseteq V$, `Scheme.OrderedAffineCoverOf W` is a structure recording a finite linearly ordered index type $\iota$ (the `Fintype` and `LinearOrder` instances are fields), a family of opens $U : \iota \to V.\mathrm{Opens}$, proofs that each $U_i$ is an affine open and that $U_i \le W$, and the equality $\bigsqcup_i U_i = W$; it is the variant of the project's `Scheme.OrderedAffineCover` (where the supremum is $\top$) relative to an open base. The simplicial bookkeeping copies that case: `Idx i` is the type of strictly monotone $s : \mathrm{Fin}(i+1) \to \iota$, `inter s` is $\bigwedge_j U_{s(j)}$, and `face s j` deletes the $j$-th entry via `Fin.succAbove`; `inter_le_inter_face`, `inter_le` and `inter_le_base` record $U_s \le U_{\partial_j s}$, $U_s \le U_{s(j)}$ and $U_s \le W$. Two constructions produce such covers: `toCoverOf` views an ordered affine cover of $V$ as one of $W = \top$, and `restrict`, for a separated morphism $\pi : V \to \operatorname{Spec} R$ and an affine open $W$, intersects the members of an ordered affine cover of $V$ with $W$, affineness of $U_i \wedge W$ coming from separatedness.
--
--   Fixing $\pi : V \to \operatorname{Spec} R$, `moduleSections` supplies on each $\Gamma(V, O)$ the $R$-module structure underlying the $\pi$-induced $R$-algebra structure, and `res π h` is the restriction map $\Gamma(V, O') \to \Gamma(V, O)$ for $O \le O'$ as an $R$-linear map (that it is the presheaf map is `res_apply`). Then `cochain i` is $\prod_{s \in \mathrm{Idx}\,i} \Gamma(V, U_s)$, `d π i` is the $R$-linear map with $(dc)_s = \sum_{j} (-1)^j\, c_{\partial_j s}|_{U_s}$, and `aug π` sends $w \in \Gamma(V, W)$ to $(w|_{U_s})_s$ in degree $0$. Finally `H0` is the type $\ker d^0$ and `HSucc i` is $\ker d^{i+1}$ modulo the preimage in $\ker d^{i+1}$ of $\operatorname{im} d^i$; no identity $d \circ d = 0$ is asserted here. `d_toCoverOf` states that the differential of `toCoverOf K` is, definitionally, the differential of the structure-sheaf presheaf datum `OModulePresheaf.unit π` on $K$.
--
--   **Relation to Mathlib.** Mathlib has affine open covers of schemes and categorical Čech constructions, but no alternating Čech complex of the structure sheaf presented as $R$-linear maps between products of section modules; the structure here, and its restriction to an open $W$, are the project's own, parallel to its `Scheme.OrderedAffineCover` and `OModulePresheaf`.
--
--   **Where it is used.** These covers and their explicit alternating Čech complexes are the computational vocabulary for the finiteness and base-change results about coherent cohomology used in the modular-forms input to the proof; restriction of a cover to an affine open (for separated $\pi$) is what makes affine acyclicity arguments available, and `d_toCoverOf` identifies the complex of a cover of $V$ with the one attached to the structure-sheaf presheaf datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverOf.lean

import Mathlib

import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

structure Scheme.OrderedAffineCoverOf {V : Scheme.{u}} (W : V.Opens) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → V.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  le : ∀ i, U i ≤ W
  iSup_eq : ⨆ i, U i = W

attribute [instance] Scheme.OrderedAffineCoverOf.instFintype Scheme.OrderedAffineCoverOf.instLinearOrder

namespace Scheme.OrderedAffineCoverOf

variable {W : V.Opens} (K : V.OrderedAffineCoverOf W)

def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

instance (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _
instance (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) := iInf_le _ j

theorem inter_le_base {i : ℕ} (s : K.Idx i) : K.inter s ≤ W := (iInf_le _ 0).trans (K.le _)

end Scheme.OrderedAffineCoverOf

namespace Scheme.OrderedAffineCover

def toCoverOf (K : V.OrderedAffineCover) : V.OrderedAffineCoverOf ⊤ where
  ι := K.ι
  U := K.U
  isAffineOpen := K.isAffineOpen
  le _ := le_top
  iSup_eq := K.iSup_eq_top

@[simp] theorem toCoverOf_U (K : V.OrderedAffineCover) (i : K.ι) : K.toCoverOf.U i = K.U i := rfl

def restrict (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W : V.Opens}
    (hW : IsAffineOpen W) : V.OrderedAffineCoverOf W where
  ι := K.ι
  U i := K.U i ⊓ W
  isAffineOpen i := isAffineOpen_inf_of_isSeparated π (K.isAffineOpen i) hW
  le _ := inf_le_right
  iSup_eq := by rw [← iSup_inf_eq, K.iSup_eq_top, top_inf_eq]

@[simp] theorem restrict_U (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W : V.Opens}
    (hW : IsAffineOpen W) (i : K.ι) : (K.restrict π hW).U i = K.U i ⊓ W := rfl

end Scheme.OrderedAffineCover

namespace Scheme.OrderedAffineCoverOf

variable (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W)

@[reducible] def moduleSections : ∀ O : V.Opens, Module R Γ(V, O) :=
  fun O => (Scheme.TwoAffineOpenCover.algebraOfHom π O).toModule

abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, Γ(V, K.inter s)

def res {O O' : V.Opens} (h : O ≤ O') :
    letI := moduleSections π
    (Γ(V, O') : Type u) →ₗ[R] (Γ(V, O) : Type u) :=
  (OModulePresheaf.unit π).res h

theorem res_apply {O O' : V.Opens} (h : O ≤ O') (x : Γ(V, O')) :
    res π h x = (V.presheaf.map (homOfLE h).op).hom x := rfl

def d (i : ℕ) :
    letI := moduleSections π
    K.cochain i →ₗ[R] K.cochain (i + 1) :=
  letI := moduleSections π
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((res π (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

theorem d_apply (i : ℕ) (f : K.cochain i) (s : K.Idx (i + 1)) :
    letI := moduleSections π
    K.d π i f s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (V.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (f (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, res_apply]

def aug :
    letI := moduleSections π
    (Γ(V, W) : Type u) →ₗ[R] K.cochain 0 :=
  letI := moduleSections π
  LinearMap.pi fun s => res π (K.inter_le_base s)

theorem aug_apply (w : Γ(V, W)) (s : K.Idx 0) :
    letI := moduleSections π
    K.aug π w s = (V.presheaf.map (homOfLE (K.inter_le_base s)).op).hom w := rfl

abbrev H0 : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π 0)

abbrev HSucc (i : ℕ) : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π (i + 1)) ⧸ (LinearMap.range (K.d π i)).comap (LinearMap.ker (K.d π (i + 1))).subtype

end Scheme.OrderedAffineCoverOf

theorem Scheme.OrderedAffineCover.d_toCoverOf (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover) (i : ℕ) :
    K.toCoverOf.d π i = (OModulePresheaf.unit π).d K i := rfl

end AlgebraicGeometry

end


