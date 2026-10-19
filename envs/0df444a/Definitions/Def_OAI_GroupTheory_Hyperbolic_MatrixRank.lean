-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
-- name    : OAI_GroupTheory_Hyperbolic_MatrixRank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:32:13.354362+00:00
-- url     : https://prove2.me/theorems/d0e3e352-2cc8-4532-9471-fb642e4ab5ae
-- title:
--   Regular-representation block matrices and Cartesian label blocks
-- statement:
--   Finite linear-algebra and combinatorial data used to build a torsion-free hyperbolic group that is not residually finite.
--
--   1. **Regular representation.** For a finite group $F$ and a semiring $R$, $\mathrm{reg}(g)$ is the $F\times F$ permutation matrix with $\mathrm{reg}(g)_{a,b}=[a=gb]$. It is a monoid homomorphism, $\mathrm{reg}(g)^{\top}=\mathrm{reg}(g^{-1})$, and its trace is $|F|$ for $g=1$ and $0$ otherwise.
--   2. **Block matrices.** A matrix of matrices $A_{ij}$ is flattened to a matrix indexed by pairs, $(i,a),(j,b)\mapsto (A_{ij})_{ab}$. For $g:\iota\times\iota\to F$ the quotient matrix is the flattening of $(\mathrm{reg}(g(u,v)))_{u,v}$. The family $g$ has *surviving rectangles* if
--   $$
--   g(u,v)\,g(u',v)^{-1}\,g(u',v')\,g(u,v')^{-1}\ne1\qquad(u\ne u',\ v\ne v').
--   $$
--   Block-diagonal sums $\operatorname{diag}(Y_I)$ and weighted tensors $f(x)f(y)Z_{x',y'}$ are also defined.
--   3. **Grid Lagrange basis.** For a finite set $S$ of scalars and $a\in S^T$, $L_a(x)=\prod_t\prod_{w\in S\setminus\{a_t\}}\frac{x_t-w}{a_t-w}$, so $L_a(a)=1$; along the affine line $x\mapsto b+xv$ it is a polynomial in $x$. The line through $a$ with direction $v\ne0$ is parametrized injectively, and the punctured line omits the parameter $0$; `lineIncidence` collects the labels whose punctured line contains a given point.
--   4. **Cartesian blocks.** For $r>0$ and $d\ge4r^2$ one can write $d=rn_1+(r+1)n_2$ with $n_1,n_2\ge r$ and $n_2<2r$. A Cartesian block is a finite set of labels with a bijection to $\mathbb Z/s\times\mathbb Z/t$ where $s,t\ge r$. Every finite set of at least $4r^2$ labels splits into two disjoint Cartesian blocks covering it. A block satisfies its relations for $g:I\times[r]^2\to G$ when there are $L,R$ with
--   $$
--   g(i,u,v)=L\bigl(u,\ c_1(i)+v\bigr)^{-1}R\bigl(v,\ c_2(i)+u\bigr),
--   $$
--   where $(c_1(i),c_2(i))$ are the block coordinates of $i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- The left regular permutation representation over any coefficient semiring. -/
def regularMatrix {F R : Type*} [Group F] [Fintype F] [DecidableEq F] [Semiring R] :
    F →* Matrix F F R := Matrix.permMatrixHom.comp (MulAction.toPermHom F F)

@[simp] theorem regularMatrix_apply {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g a b : F) :
    regularMatrix (R := R) g a b = if a = g * b then 1 else 0 := by
  simp [regularMatrix, Matrix.permMatrixHom, Equiv.Perm.permMatrix,
    PEquiv.toMatrix, Equiv.toPEquiv_apply, inv_mul_eq_iff_eq_mul]

@[simp] theorem regularMatrix_transpose {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g : F) :
    (regularMatrix (R := R) g).transpose = regularMatrix g⁻¹ := by
  ext a b
  simp [eq_inv_mul_iff_mul_eq, eq_comm]

@[simp] theorem regularMatrix_trace {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g : F) :
    (regularMatrix (R := R) g).trace = if g = 1 then (Fintype.card F : R) else 0 := by
  by_cases hg : g = 1
  · subst g; simp
  · have hfix : ∀ a : F, a ≠ g * a := by
      intro a ha
      exact hg (mul_right_cancel (show g * a = 1 * a by simpa using ha.symm))
    simp [Matrix.trace, hfix, hg]

/-- Flatten a rectangular matrix of blocks, with the block index first. -/
def flattenMatrix {ι κ α β R : Type*} (A : Matrix ι κ (Matrix α β R)) :
    Matrix (ι × α) (κ × β) R := fun i j => A i.1 j.1 i.2 j.2

@[simp] theorem flattenMatrix_apply {ι κ α β R : Type*}
    (A : Matrix ι κ (Matrix α β R)) (i : ι × α) (j : κ × β) :
    flattenMatrix A i j = A i.1 j.1 i.2 j.2 := rfl

/-- The block regular-representation matrix attached to one line label. -/
def quotientMatrix {ι F R : Type*} [Group F] [Fintype F] [DecidableEq F]
    [Semiring R] (g : ι → ι → F) : Matrix (ι × F) (ι × F) R :=
    flattenMatrix (Matrix.of fun u v => regularMatrix (g u v))

/-- Nondegenerate rectangular words survive in the finite group. -/
def RectanglesSurvive {ι F : Type*} [Group F] (g : ι → ι → F) : Prop :=
  ∀ u u' v v', u ≠ u' → v ≠ v' →
    g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹ ≠ 1

/-- Block direct sum with the line-label index first. -/
def diagonalBlocks {I ι κ K : Type*} [DecidableEq I] [Zero K]
    (Y : I → Matrix ι κ K) : Matrix (I × ι) (I × κ) K :=
    Matrix.of fun x y => if x.1 = y.1 then Y x.1 x.2 y.2 else 0

/-- The rank-one scalar matrix `f fᵀ` tensored with a matrix. -/
def weightedMatrix {I ι κ K : Type*} [Mul K] (f : I → K) (Z : Matrix ι κ K) :
    Matrix (I × ι) (I × κ) K := Matrix.of fun x y => f x.1 * f y.1 * Z x.2 y.2

def gridLagrange {T K : Type*} [Fintype T] [Field K] [DecidableEq K]
    (S : Finset K) (a x : T → K) : K :=
    ∏ t, ∏ w ∈ S.erase (a t), (x t - w) / (a t - w)

@[simp] theorem gridLagrange_self {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a : T → K) : gridLagrange S a a = 1 := by
  apply Finset.prod_eq_one
  intro t _
  apply Finset.prod_eq_one
  intro w hw
  exact div_self (sub_ne_zero.mpr (Finset.mem_erase.mp hw).1.symm)

/-- Restriction of the grid Lagrange basis along the parametrized affine line. -/
noncomputable def gridLagrangeLine {T K : Type*} [Fintype T] [Field K] [DecidableEq K]
    (S : Finset K) (a b v : T → K) : Polynomial K :=
    ∏ t, ∏ w ∈ S.erase (a t),
      (Polynomial.C (b t - w) + Polynomial.X * Polynomial.C (v t)) *
        Polynomial.C ((a t - w)⁻¹)

@[simp] theorem gridLagrangeLine_eval {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a b v : T → K) (x : K) :
    (gridLagrangeLine S a b v).eval x = gridLagrange S a (fun t => b t + x * v t) := by
  simp only [gridLagrangeLine, gridLagrange, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    div_eq_mul_inv]
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro w _
  ring

/-- Standard affine parametrization, with the marked point at parameter zero. -/
def affineLineMap {T K : Type*} [Field K] (a v : T → K) (x : K) : T → K :=
  fun t => a t + x * v t

theorem affineLineMap_injective {T K : Type*} [Field K] (a v : T → K)
    (hv : v ≠ 0) : Function.Injective (affineLineMap a v) := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hv
  intro x y hxy
  have h := congrFun hxy t
  exact mul_right_cancel₀ ht (add_left_cancel h)

/-- The geometric affine line punctured only at its own marked point. -/
noncomputable def puncturedLine {T K : Type*} [Fintype T] [Field K] [Fintype K]
    (a v : T → K) : Finset (T → K) := by
  classical
  exact (Finset.univ.erase 0).image (affineLineMap a v)

noncomputable def lineIncidence {T I K : Type*} [Fintype T] [Fintype I]
    [Field K] [Fintype K] (a v : I → T → K) (z : T → K) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => z ∈ puncturedLine (a i) (v i))

theorem two_block_sizes (r d : ℕ) (hr : 0 < r) (hd : 4 * r ^ 2 ≤ d) :
    ∃ n₁ n₂ : ℕ, r ≤ n₁ ∧ r ≤ n₂ ∧ n₂ < 2 * r ∧
      d = r * n₁ + (r + 1) * n₂ := by
  have hmod : d % r < r := Nat.mod_lt d hr
  have hquot : 4 * r ≤ d / r := (Nat.le_div_iff_mul_le hr).mpr (by nlinarith)
  have hsub : r + 1 + d % r ≤ d / r := by omega
  refine ⟨d / r - (r + 1 + d % r), r + d % r, by omega, by omega, by omega, ?_⟩
  have hdecomp := Nat.div_add_mod d r
  have hdiff := Nat.sub_add_cancel hsub
  nlinarith

structure CartesianBlock (I : Type*) (r : ℕ) where
  s : ℕ
  t : ℕ
  hs : r ≤ s
  ht : r ≤ t
  spos : 0 < s
  tpos : 0 < t
  labels : Finset I
  coordinates : labels ≃ ZMod s × ZMod t

instance {I : Type*} {r : ℕ} (b : CartesianBlock I r) : NeZero b.s := ⟨b.spos.ne'⟩
instance {I : Type*} {r : ℕ} (b : CartesianBlock I r) : NeZero b.t := ⟨b.tpos.ne'⟩

/-- Opposite-index shifts are bijections of the block coordinates. -/
def CartesianBlock.shifted {I : Type*} {r : ℕ} (b : CartesianBlock I r)
    (u v : Fin r) : b.labels ≃ ZMod b.s × ZMod b.t :=
  b.coordinates.trans (Equiv.prodCongr (Equiv.addRight (v.val : ZMod b.s))
    (Equiv.addRight (u.val : ZMod b.t)))

/-- Every sufficiently large finite set has the two Cartesian blocks required by
the construction; the coordinate bijections are chosen without deleting labels. -/
theorem exists_two_cartesian_blocks {I : Type*} [DecidableEq I] (r : ℕ) (hr : 0 < r)
    (A : Finset I) (hA : 4 * r ^ 2 ≤ A.card) :
    ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = A := by
  classical
  obtain ⟨n₁,n₂,hn₁,hn₂,_,heq⟩ := two_block_sizes r A.card hr hA
  obtain ⟨A₀,hA₀,hcard⟩ := Finset.exists_subset_card_eq (show r * n₁ ≤ A.card by omega)
  let A₁ := A \ A₀
  have hcard₁ : A₁.card = (r + 1) * n₂ := by rw [Finset.card_sdiff_of_subset hA₀, hcard, heq]; omega
  let : NeZero r := ⟨hr.ne'⟩
  let : NeZero n₁ := ⟨(hr.trans_le hn₁).ne'⟩
  let : NeZero n₂ := ⟨(hr.trans_le hn₂).ne'⟩
  let b₀ : CartesianBlock I r :=
    {s := r, t := n₁, hs := le_rfl, ht := hn₁, spos := hr, tpos := hr.trans_le hn₁,
     labels := A₀, coordinates := Fintype.equivOfCardEq (by simpa using hcard)}
  let b₁ : CartesianBlock I r :=
    {s := r+1, t := n₂, hs := Nat.le_succ r, ht := hn₂, spos := Nat.succ_pos r,
     tpos := hr.trans_le hn₂,
     labels := A₁, coordinates := Fintype.equivOfCardEq (by simpa using hcard₁)}
  refine ⟨b₀,b₁,?_,?_⟩
  · exact Finset.disjoint_sdiff
  · exact Finset.union_sdiff_of_subset hA₀

/-- The exact defining relation of a single block, retaining the order `L⁻¹R`. -/
def CartesianBlock.Relations {I G : Type*} [Group G] {r : ℕ}
    (b : CartesianBlock I r) (g : I → Fin r → Fin r → G) : Prop :=
    ∃ (L : Fin r → ZMod b.s → G) (R : Fin r → ZMod b.t → G),
      ∀ (i : b.labels) u v, g i u v =
        (L u ((b.coordinates i).1 + (v.val : ZMod b.s)))⁻¹ *
         R v ((b.coordinates i).2 + (u.val : ZMod b.t))

end Release075

end OAI


