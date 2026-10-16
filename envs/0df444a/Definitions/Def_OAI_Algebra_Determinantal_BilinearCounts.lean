-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
-- name    : OAI_Algebra_Determinantal_BilinearCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:07:00.499633+00:00
-- url     : https://prove2.me/theorems/448f93be-7229-4624-807d-00d8145a085c
-- title:
--   Affine charts and equation reordering for the bilinear kernel system of a matrix pencil
-- statement:
--   This module provides the affine charts in which the multihomogeneous kernel system of a matrix pencil is compared with the analytic kernel-lift system of a bordered matrix family. Fix a finite set $\kappa$ and $n\in\mathbb N$, and put $\hat\kappa=\kappa\sqcup\{\star\}$. The polynomial system lives in the variables $s$ and $z_k$ ($k\in\hat\kappa$) of group $0$, $u_0,\dots,u_n$ of the right group and $v_0,\dots,v_n$ of the left group; for matrices $A_0,A_k$ it consists of the right equations $R_i=\sum_jL_{ij}u_j$ ($0\le i\le n$), left equations $C_j=\sum_iL_{ij}v_i$ at the $n$ columns other than a pivot column, and polar equations $P_k=v^{\mathsf T}B_ku$ ($k\in\kappa$), where $L_{ij}=(A_0)_{ij}s+\sum_{k\in\hat\kappa}(A_k)_{ij}z_k$. For $i\in\{0,\dots,n\}$ let $\sigma_i(j)$ denote the $j$-th element (counting from $0$) of $\{0,\dots,n\}\setminus\{i\}$ in increasing order.
--
--   1. **Chart space.** $\mathcal C=(\mathbb C\times\mathbb C^{\kappa})\times(\mathbb C^{n}\times\mathbb C^{n})$, of dimension $2n+1+|\kappa|$, which equals the number of equations.
--
--   2. **Splitting off the extra coordinate.** The linear isomorphism $\mathbb C^{\hat\kappa}\to\mathbb C\times\mathbb C^{\kappa}$, $z\mapsto\bigl(z(\star),(z(k))_{k\in\kappa}\bigr)$.
--
--   3. **Normalized vectors.** For $i\in\{0,\dots,n\}$ and $p\in\mathbb C^{n}$, $\nu_i(p)\in\mathbb C^{n+1}$ is the vector with $\nu_i(p)_i=1$ and $\nu_i(p)_{\sigma_i(j)}=p_j$ for $0\le j<n$.
--
--   4. **Charts and base variables.** For $i,r\in\{0,\dots,n\}$ and $\bigl((z_\star,z_\kappa),(p,q)\bigr)\in\mathcal C$, the chart point has $s=1$, $z\in\mathbb C^{\hat\kappa}$ reassembled from $(z_\star,z_\kappa)$, $u=\nu_i(p)$ and $v=\nu_r(q)$. The base variables of this chart are $s$, $u_i$ and $v_r$, one per group, all equal to $1$ on the chart.
--
--   5. **Output reordering.** For a pivot row $r$, the linear isomorphism from $\mathbb C^{\text{equations}}$ onto $\mathcal C$ sending a vector $y$ of equation values to
--   $$
--   \Bigl(\bigl(y_{R_r},\,(y_{P_k})_{k\in\kappa}\bigr),\ \bigl((y_{R_{\sigma_r(j)}})_{0\le j<n},\,(y_{C_j})_{0\le j<n}\bigr)\Bigr),
--   $$
--   where $C_j$ is the $j$-th left equation. It is a permutation of coordinates, also regarded as a continuous linear equivalence.
--
--   6. **Affine pencil.** For $A_0$ and $A_v$ ($v\in\sigma$, $\sigma$ finite) in $\mathbb C^{(n+1)\times(n+1)}$ and $y\in\mathbb C^{\sigma}$, $A(y)=A_0+\sum_{v\in\sigma}y_v\,A_v$.
--
--   In the chart given by a column pivot $i$ (the pivot of the system) and a row pivot $r$, the reordered values of the polynomial system coincide with the matrix kernel system of the bordered matrix family obtained from the pencil by pivoting at row $r$ and column $i$, whenever the pencil agrees with the family on the slice and the polar matrices $B_k$ are the directional derivatives of the family; chart points with different pencil coordinates are block-separated. This transfers the bound $2^{|\kappa|}\binom{2n+1}{|\kappa|+1}$ for simple solutions of the bilinear system to the simple zeros of the polar pair $\bigl(\det A(y),\ (D\det A(y)\,h_k)_{k\in\kappa}\bigr)$ restricted to an affine slice $y=b+\Lambda(z)$, $z\in\mathbb C^{\hat\kappa}$, with $\Lambda$ linear.
--
--   **Formalization Note** The definitions are `KernelBilinear.ChartSpace`, `optionProduct`, `norm` (the normalized vector of item 3, unrelated to a norm), `chart`, `base`, `outputLinear`, `output` and `affine`; $\hat\kappa$ is `Option κ` with $\star$ = `none`, and $\sigma_i(j)$ is `i.succAbove j`. The lemmas `optionProduct_apply`, `optionProduct_symm_apply`, `pivot_symm`, `pivot_symm_succAbove`, `norm_pivot` and `norm_succAbove` are `simp` evaluation rules.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/BilinearCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/BilinearCounts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts

namespace OAI

namespace PermanentBorder.PolarAnalysis
open Matrix Schur Filter
open scoped Topology
variable {κ J T : Type*} [Fintype κ] [Finite J]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.KernelBilinear
open MvPolynomial PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
abbrev ChartSpace (κ : Type) (n : ℕ) := (ℂ × (κ → ℂ)) × ((Fin n → ℂ) × (Fin n → ℂ))
noncomputable def optionProduct : (Option κ → ℂ) ≃L[ℂ] (ℂ × (κ → ℂ)) :=
  (LinearEquiv.piOptionEquivProd ℂ).toContinuousLinearEquiv
@[simp] lemma optionProduct_apply (z : Option κ → ℂ) : optionProduct z = (z none,fun i => z (some i)) := rfl
@[simp] lemma optionProduct_symm_apply (z : ℂ × (κ → ℂ)) (i : Option κ) :
    optionProduct.symm z i = i.elim z.1 z.2 := by cases i <;> rfl

@[simp] lemma pivot_symm (i : Fin (n+1)) : (pivotEquiv i).symm i = .inl () :=
  (pivotEquiv i).symm_apply_apply (.inl ())
@[simp] lemma pivot_symm_succAbove (i : Fin (n+1)) (j : Fin n) :
    (pivotEquiv i).symm (i.succAbove j) = .inr j :=
  (pivotEquiv i).symm_apply_apply (.inr j)

noncomputable def norm (i : Fin (n+1)) (z : Fin n → ℂ) : Fin (n+1) → ℂ :=
  normalized z ∘ (pivotEquiv i).symm
@[simp] lemma norm_pivot (i : Fin (n+1)) (z : Fin n → ℂ) : norm i z i = 1 := by
  change normalized z ((pivotEquiv i).symm (pivotEquiv i (.inl ()))) = 1
  simp [normalized]
@[simp] lemma norm_succAbove (i : Fin (n+1)) (z : Fin n → ℂ) (j : Fin n) :
    norm i z (i.succAbove j) = z j := by
  change normalized z ((pivotEquiv i).symm (pivotEquiv i (.inr j))) = z j
  simp [normalized]

noncomputable def chart (i r : Fin (n+1)) (z : ChartSpace κ n) : Variables κ n → ℂ :=
  coordinates (optionProduct.symm z.1) (norm i z.2.1) (norm r z.2.2)
noncomputable def base (i r : Fin (n+1)) : Groups → Variables κ n
  | none => ⟨none,none⟩
  | some false => ⟨some false,i⟩
  | some true => ⟨some true,r⟩
noncomputable def outputLinear (r : Fin (n+1)) : (Equations κ n → ℂ) ≃ₗ[ℂ] ChartSpace κ n where
  toFun y := ((y (.inl r), fun k => y (.inr (.inr k))),
    (fun j => y (.inl (r.succAbove j)), fun j => y (.inr (.inl j))))
  invFun z := Sum.elim
    (fun i => ((pivotEquiv r).symm i).elim (fun _ => z.1.1) z.2.1)
    (Sum.elim z.2.2 z.1.2)
  left_inv y := by
    funext i
    rcases i with i | j | k
    · obtain ⟨a,rfl⟩ := (pivotEquiv r).surjective i
      rcases a with u | a
      · cases u; simp
      · simp
    · rfl
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · change ((pivotEquiv r).symm (pivotEquiv r (.inl ()))).elim _ _ = _
        simp
      · rfl
    · apply Prod.ext
      · funext j
        change ((pivotEquiv r).symm (pivotEquiv r (.inr j))).elim _ _ = _
        simp
      · rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def output (r : Fin (n+1)) : (Equations κ n → ℂ) ≃L[ℂ] ChartSpace κ n :=
  (outputLinear r).toContinuousLinearEquiv

end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}

section Bridge
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

end Bridge
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ J : Type} [Fintype κ] [Fintype J] {n : ℕ}
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {σ κ J : Type} [Fintype σ] [Fintype κ] [Fintype J] {n : ℕ}

noncomputable def affine (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :=
  A₀ + ∑ v, y v • A v

end PermanentBorder.KernelBilinear

end OAI


