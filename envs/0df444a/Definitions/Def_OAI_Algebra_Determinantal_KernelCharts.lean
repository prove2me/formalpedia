-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
-- name    : OAI_Algebra_Determinantal_KernelCharts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:02:26.796815+00:00
-- url     : https://prove2.me/theorems/119a931e-7b22-453c-a8f6-d7b20deb30b6
-- title:
--   Bilinear kernel system of an affine matrix pencil, coefficient collapse and Schur complements
-- statement:
--   This module encodes "a matrix of an affine pencil has a right kernel vector $u$ and a left kernel vector $v$ satisfying prescribed polar constraints" as a square multihomogeneous bilinear polynomial system, and introduces Schur-complement notation for bordered matrices. Fix a finite set $\kappa$ and $n\in\mathbb N$; matrices are $(n+1)\times(n+1)$ with indices $0,\dots,n$, and $\hat\kappa=\kappa\sqcup\{\star\}$.
--
--   1. **Variable groups.** There are three groups of complex variables: group $0$ with the $|\kappa|+2$ variables $s$ and $z_k$ ($k\in\hat\kappa$), the right group with $u_0,\dots,u_n$, and the left group with $v_0,\dots,v_n$. The dimension vector is $(|\kappa|+1,\,n,\,n)$: each group has one more variable than its dimension, so the variables are multihomogeneous coordinates on $\mathbb P^{|\kappa|+1}\times\mathbb P^{n}\times\mathbb P^{n}$. A fixed bijection identifies them, group by group, with the block variables of this dimension vector.
--
--   2. **Homogenized pencil.** For matrices $A_0$ and $A_k$ ($k\in\hat\kappa$) in $\mathbb C^{(n+1)\times(n+1)}$, $L$ is the matrix of linear forms
--   $$
--   L_{ij}=(A_0)_{ij}\,s+\sum_{k\in\hat\kappa}(A_k)_{ij}\,z_k .
--   $$
--
--   3. **Kernel and polar equations.** The right equations $R_i=\sum_jL_{ij}u_j$ (the entries of $Lu$), the left equations $C_j=\sum_iL_{ij}v_i$ (the entries of $v^{\mathsf T}L$) and, for a matrix $B$, the polar equation $\sum_{i,j}B_{ij}\,u_j\,v_i=v^{\mathsf T}Bu$.
--
--   4. **The system.** Equations are indexed by $\{0,\dots,n\}\sqcup\{0,\dots,n-1\}\sqcup\kappa$. Given matrices $B_k$ ($k\in\kappa$) and a pivot column $p\in\{0,\dots,n\}$, the system consists of the $n+1$ right equations $R_0,\dots,R_n$, the $n$ left equations $C_j$ for the columns $j\ne p$ (in increasing order), and the $|\kappa|$ polar equations $v^{\mathsf T}B_ku$. There are $2n+1+|\kappa|$ equations, the sum of the dimensions. Two group labels record the bidegree of each equation: right equations are bilinear in (group $0$, right group), left equations in (group $0$, left group), and polar equations in (right group, left group); each equation is multihomogeneous of multidegree $\mathbf e_{\text{first}}+\mathbf e_{\text{second}}$.
--
--   5. **Affine coordinates.** For $z\in\mathbb C^{\hat\kappa}$ and $u,v\in\mathbb C^{n+1}$, the point with $s=1$, $z_k=z(k)$ and the given $u,v$. At this point $L$ evaluates to $A_0+\sum_{k}z(k)A_k$, so $R_i$ evaluates to $\sum_j\bigl((A_0)_{ij}+\sum_k(A_k)_{ij}z(k)\bigr)u_j$, $C_j$ to $\sum_i\bigl((A_0)_{ij}+\sum_k(A_k)_{ij}z(k)\bigr)v_i$, and the polar equation to $v^{\mathsf T}Bu$.
--
--   6. **Coefficient collapse.** For a variable index $i\in\sigma$, the ring homomorphism $\mathbb N[X_j:j\in\sigma]\to\mathbb N[X]$ with $X_i\mapsto X$ and $X_j\mapsto1$ for $j\ne i$.
--
--   7. **Schur-complement notation.** For a finite set $\iota$, $a\in\mathbb C$, $\beta,\gamma\in\mathbb C^{\iota}$ and $N\in\mathbb C^{\iota\times\iota}$: the bordered matrix indexed by $\{\ast\}\sqcup\iota$,
--   $$
--   \begin{pmatrix}a&\beta^{\mathsf T}\\ \gamma&N\end{pmatrix},
--   $$
--   the right and left kernel candidates $-N^{-1}\gamma$ and $-\beta^{\mathsf T}N^{-1}$, the Schur complement $a-\beta^{\mathsf T}N^{-1}\gamma$, and, for $u\in\mathbb C^{\iota}$, the normalized vector $(1,u)\in\mathbb C^{\{\ast\}\sqcup\iota}$.
--
--   The multidegree data make the bilinear counting bound applicable: the number of simple solutions is controlled by the coefficient of $X_0^{|\kappa|+1}X_1^{n}X_2^{n}$ in $(X_0+X_1)^{n+1}(X_0+X_2)^{n}(X_1+X_2)^{|\kappa|}$ (with $X_0,X_1,X_2$ for group $0$, the right and the left group), and collapsing onto $X_0$ bounds this coefficient by $2^{|\kappa|}\binom{2n+1}{|\kappa|+1}$. When $N$ is invertible, the bordered matrix maps $(1,-N^{-1}\gamma)$ to the vector with the Schur complement in the corner and zeros elsewhere, $(1,-\beta^{\mathsf T}N^{-1})$ is mapped likewise from the left, and the determinant of the bordered matrix equals $\det N$ times the Schur complement; this links kernel vectors with the vanishing of the determinant.
--
--   **Formalization Note** Groups are `Option Bool` (`none` is group $0$, `some false` the right group, `some true` the left group); $\hat\kappa$ is `Option κ` with $\star$ = `none`, and group-$0$ variables are indexed by `Option (Option κ)` with $s$ = `none` and $z_k$ = `some k`. The definitions are `Groups`, `Var`, `Variables`, `Equations`, `dimensions`, `variablesEquiv`, `linearMatrix`, `rightEquation`, `leftEquation`, `polarEquation`, `system` (left equations at the columns `pivot.succAbove j`), `firstGroup`, `secondGroup`, `coordinates`, `Multigraded.collapse`, and in `PolarAnalysis.Schur` the objects `block`, `right`, `left`, `scalar`, `normalized`. The inverse is Mathlib's matrix inverse, which is $0$ for a singular matrix. The `eval_*` lemmas are the evaluation formulas of item 5.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/KernelCharts.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/KernelCharts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

abbrev Groups := Option Bool
abbrev Var (κ : Type) (n : ℕ) : Groups → Type _ :=
  Option.elim' (Option (Option κ)) (fun _ => Fin (n+1))
instance varFintype (κ : Type) [Fintype κ] (n : ℕ) : (j : Groups) → Fintype (Var κ n j)
  | none => inferInstanceAs (Fintype (Option (Option κ)))
  | some _ => inferInstanceAs (Fintype (Fin (n+1)))
abbrev Variables (κ : Type) (n : ℕ) := Σ j : Groups, Var κ n j
abbrev Equations (κ : Type) (n : ℕ) := Fin (n+1) ⊕ (Fin n ⊕ κ)

variable {κ : Type} [Fintype κ] {n : ℕ}

noncomputable def dimensions (κ : Type) [Fintype κ] (n : ℕ) : Groups →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Option.elim' (Fintype.card κ+1) (fun _ => n))

@[simp] lemma dimensions_none : dimensions κ n none = Fintype.card κ+1 := rfl
@[simp] lemma dimensions_some (b : Bool) : dimensions κ n (some b) = n := rfl

lemma var_card (j : Groups) : Fintype.card (Var κ n j) = dimensions κ n j + 1 := by
  cases j with
  | none =>
    change Fintype.card (Option (Option κ)) = Fintype.card κ + 1 + 1
    exact Fintype.card_option.trans (congrArg (fun k => k+1) Fintype.card_option)
  | some b =>
    change Fintype.card (Fin (n+1)) = n+1
    exact Fintype.card_fin _

noncomputable def variablesEquiv : Variables κ n ≃
    Multigraded.BlockVariables (dimensions κ n) :=
  Equiv.sigmaCongrRight (fun j => (Fintype.equivFin (Var κ n j)).trans
    (finCongr (var_card j)))

@[simp] lemma variablesEquiv_group (s : Variables κ n) :
    (variablesEquiv s).1 = s.1 := rfl

noncomputable def linearMatrix (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i j : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  C (A₀ i j) * X ⟨none,none⟩ + ∑ k, C (A k i j) * X ⟨none,some k⟩

noncomputable def rightEquation (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  ∑ j, linearMatrix A₀ A i j * X ⟨some false,j⟩

noncomputable def leftEquation (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (j : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  ∑ i, linearMatrix A₀ A i j * X ⟨some true,i⟩

noncomputable def polarEquation (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    MvPolynomial (Variables κ n) ℂ :=
  ∑ i, ∑ j, C (B i j) * X ⟨some false,j⟩ * X ⟨some true,i⟩

noncomputable def system (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (pivot : Fin (n+1)) :
    Equations κ n → MvPolynomial (Variables κ n) ℂ :=
  Sum.elim (rightEquation A₀ A)
    (Sum.elim (fun j => leftEquation A₀ A (pivot.succAbove j)) (fun k => polarEquation (B k)))

def firstGroup : Equations κ n → Groups :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (fun _ => some false))
def secondGroup : Equations κ n → Groups :=
  Sum.elim (fun _ => some false) (Sum.elim (fun _ => some true) (fun _ => some true))

noncomputable def coordinates (z : Option κ → ℂ)
    (u v : Fin (n+1) → ℂ) : Variables κ n → ℂ :=
  fun s => match s with
    | ⟨none,t⟩ => t.elim 1 z
    | ⟨some false,i⟩ => u i
    | ⟨some true,i⟩ => v i

@[simp] lemma eval_linearMatrix (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (i j : Fin (n+1)) :
    eval (coordinates z u v) (linearMatrix A₀ A i j) = A₀ i j + ∑ k, A k i j * z k := by
  simp [linearMatrix, coordinates]

@[simp] lemma eval_right (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    eval (coordinates z u v) (rightEquation A₀ A i) =
      ∑ j, (A₀ i j + ∑ k, A k i j * z k) * u j := by
  simp [rightEquation, coordinates]

@[simp] lemma eval_left (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (j : Fin (n+1)) :
    eval (coordinates z u v) (leftEquation A₀ A j) =
      ∑ i, (A₀ i j + ∑ k, A k i j * z k) * v i := by
  simp [leftEquation, coordinates]

omit [Fintype κ] in
@[simp] lemma eval_polar (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) :
    eval (coordinates z u v) (polarEquation B) = ∑ i, ∑ j, B i j * u j * v i := by
  simp [polarEquation, coordinates]

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
noncomputable def collapse (i : σ) : MvPolynomial σ ℕ →+* Polynomial ℕ :=
  eval₂Hom Polynomial.C (fun j => if j = i then Polynomial.X else 1)

end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def block (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  fromBlocks (Matrix.of fun _ _ => a) (Matrix.of fun _ j => β j) (Matrix.of fun i _ => γ i) E
noncomputable def right (γ : ι → ℂ) (E : Matrix ι ι ℂ) : ι → ℂ := -(E⁻¹ *ᵥ γ)
noncomputable def left (β : ι → ℂ) (E : Matrix ι ι ℂ) : ι → ℂ := -(β ᵥ* E⁻¹)
noncomputable def scalar (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) : ℂ :=
  a - β ⬝ᵥ (E⁻¹ *ᵥ γ)
noncomputable def normalized (u : ι → ℂ) : Unit ⊕ ι → ℂ := Sum.elim (fun _ => 1) u

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI


