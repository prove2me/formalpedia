-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_Multigraded
-- name    : OAI_Algebra_Determinantal_Multigraded
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:27:46.788988+00:00
-- url     : https://prove2.me/theorems/c7cc823c-29a0-483a-adb3-b441ff2ad650
-- title:
--   Graded pieces of polynomial quotients, factor-splitting bounds and block multigradings
-- statement:
--   This module sets up the graded linear algebra used to bound the dimensions of graded pieces of quotients of polynomial rings. Throughout, $K$ is a field, $K[x]=K[x_v : v\in\sigma]$ is the polynomial ring in variables indexed by a set $\sigma$, $G$ is an additive abelian group and $w:\sigma\to G$ is a weight function. A monomial $x^m=\prod_v x_v^{m_v}$ has weight $w(m)=\sum_v m_v\,w(v)\in G$, and a polynomial is *$w$-homogeneous of degree $d$* if every monomial occurring in it with nonzero coefficient has weight $d$.
--
--   1. **Graded pieces.** For $d\in G$, $P_d\subseteq K[x]$ is the $K$-subspace of $w$-homogeneous polynomials of degree $d$ (it contains $0$).
--
--   2. **Graded pieces of a quotient.** For an ideal $I\subseteq K[x]$ and $d\in G$,
--   $$
--   Q_d(I)=P_d\,/\,(I\cap P_d),
--   $$
--   a $K$-vector space. When $I$ is $w$-homogeneous, $Q_d(I)$ is the degree-$d$ part of $K[x]/I$.
--
--   3. **Component-closed ideals.** An ideal $I$ is component-closed if for every $p\in I$ and every $d\in G$ the $w$-homogeneous component of $p$ of degree $d$ again lies in $I$; that is, $I$ is $w$-homogeneous.
--
--   4. **Induced maps.** If $I\subseteq J$, the identity of $P_d$ induces the $K$-linear map $Q_d(I)\to Q_d(J)$, $[p]\mapsto[p]$. If $a$ is $w$-homogeneous of degree $e$, multiplication by $a$ is a $K$-linear map $P_{d-e}\to P_d$, $p\mapsto ap$; if moreover $ap\in J$ for every $p\in I$, it induces the $K$-linear map $Q_{d-e}(I)\to Q_d(J)$, $[p]\mapsto[ap]$.
--
--   5. **Factor pairs and product ideals.** A factor pair $q=(a,b,e_a,e_b)$ consists of polynomials $a,b$ and degrees $e_a,e_b\in G$ such that $a$ is $w$-homogeneous of degree $e_a$ and $b$ is $w$-homogeneous of degree $e_b$. The product ideal of a finite list $q_1,\dots,q_m$ of factor pairs is $(a_1b_1,\dots,a_mb_m)$; for the empty list it is the zero ideal.
--
--   6. **Split bound.** For an ideal $I$, a degree $d\in G$ and a list $q_1,\dots,q_m$ of factor pairs, the natural number $\mathrm{SB}(I,d;q_1,\dots,q_m)$ is defined by recursion on the list: $\mathrm{SB}(I,d;\varnothing)=\dim_K Q_d(I)$ and
--   $$
--   \mathrm{SB}(I,d;q_1,\dots,q_m)=\mathrm{SB}\bigl(I+(a_1),\,d;\,q_2,\dots,q_m\bigr)+\mathrm{SB}\bigl(I+(b_1),\,d-e_{a_1};\,q_2,\dots,q_m\bigr).
--   $$
--   Unwinding the recursion, $\mathrm{SB}$ is the sum, over the $2^m$ ways of choosing one factor from each pair, of $\dim_K Q_{d'}(I+\text{(chosen factors)})$, where $d'$ is $d$ minus the sum of the degrees $e_{a_k}$ over those pairs $k$ in which $b_k$ was chosen.
--
--   7. **Block multigrading.** Let $\iota$ be a finite set of blocks and $g:\sigma\to\iota$ an assignment of variables to blocks. The block weight gives $x_v$ the weight $\mathbf e_{g(v)}\in\mathbb Z^{\iota}$, the standard unit vector of its block. The weight of $x^m$ is then its multidegree, whose $j$-th entry is the block exponent $\deg_j(m)=\sum_{v:\,g(v)=j}m_v$, and block-homogeneous polynomials are exactly the polynomials that are multihomogeneous with respect to the partition of the variables into blocks. The entries of the multidegree add up to the total degree $\sum_v m_v$, and when $\sigma$ is finite every multidegree contains only finitely many monomials, so every piece $P_d$ is finite-dimensional.
--
--   8. **Embedding into the quotient ring.** For the block grading, the $K$-linear map $Q_d(I)\to K[x]/I$, $[p]\mapsto p+I$.
--
--   These objects support the subadditivity estimate $\dim_K Q_d\bigl(I+(a_1b_1,\dots,a_mb_m)\bigr)\le\mathrm{SB}(I,d;q_1,\dots,q_m)$ for component-closed ideals $I$ whose graded pieces are finite-dimensional. Applied to products of linear forms in a block-multigraded polynomial ring, it yields multihomogeneous Bézout-type upper bounds for the number of points cut out by bilinear systems; the block grading and the embedding into $K[x]/I$ are used to evaluate graded pieces of quotients by linear relations within a block.
--
--   **Formalization Note** The objects are `Piece`, `componentQuotient`, `ComponentClosed`, `componentMap`, `mulPiece`, `componentMul`, `FactorPair`, `productIdeal`, `splitBound`, `blockWeight` (values in `ι → ℤ`), `blockExponent` and `componentEmbed`. The quotient $Q_d(I)$ is the quotient of the submodule `Piece w d` by the preimage of $I$ under its inclusion, so no homogeneity of $I$ is assumed in the definition. Dimensions are `Module.finrank`, which is $0$ for an infinite-dimensional space. The lemmas `sum_blockWeight` and `finite_block_degree`, the instance `blockPiece_finite` and the `simp` lemmas `componentMap_mk`, `mulPiece_val`, `componentMul_mk` record the facts stated in items 4 and 7.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/Multigraded.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Multigraded.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

abbrev Piece (d : G) := weightedHomogeneousSubmodule K w d

abbrev componentQuotient (I : Ideal (MvPolynomial σ K)) (d : G) :=
  Piece (K := K) w d ⧸
    (I.restrictScalars K).comap (Piece (K := K) w d).subtype

def ComponentClosed (I : Ideal (MvPolynomial σ K)) : Prop :=
  ∀ p ∈ I, ∀ d, weightedHomogeneousComponent w d p ∈ I

noncomputable def componentMap {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (d : G) :
    componentQuotient w I d →ₗ[K] componentQuotient w J d :=
  Submodule.mapQ _ _ LinearMap.id (fun _ hx => h hx)

@[simp] lemma componentMap_mk {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J)
    (d : G) (p : Piece (K := K) w d) :
    componentMap w h d (Submodule.Quotient.mk p) = Submodule.Quotient.mk p := rfl

noncomputable def mulPiece {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G) :
    Piece (K := K) w (d-e) →ₗ[K] Piece (K := K) w d :=
  ((LinearMap.mulLeft K a).comp (Piece (K := K) w (d-e)).subtype).codRestrict _
    (fun p => by
      change IsWeightedHomogeneous w (a * p.val) d
      simpa only [add_sub_cancel] using ha.mul p.property)

@[simp] lemma mulPiece_val {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G) (p : Piece (K := K) w (d-e)) :
    (mulPiece w ha d p).val = a*p.val := rfl

noncomputable def componentMul {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (I J : Ideal (MvPolynomial σ K))
    (h : ∀ p ∈ I, a*p ∈ J) (d : G) :
    componentQuotient w I (d-e) →ₗ[K] componentQuotient w J d :=
  Submodule.mapQ _ _ (mulPiece w ha d) (fun p hp => h p.val hp)

@[simp] lemma componentMul_mk {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (I J : Ideal (MvPolynomial σ K))
    (h : ∀ p ∈ I, a*p ∈ J) (d : G) (p : Piece (K := K) w (d-e)) :
    componentMul w ha I J h d (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (mulPiece w ha d p) := rfl

structure FactorPair where
  left : MvPolynomial σ K
  right : MvPolynomial σ K
  leftDegree : G
  rightDegree : G
  left_homogeneous : left.IsWeightedHomogeneous w leftDegree
  right_homogeneous : right.IsWeightedHomogeneous w rightDegree

noncomputable def productIdeal : List (FactorPair (K := K) w) → Ideal (MvPolynomial σ K)
  | [] => ⊥
  | q :: qs => Ideal.span {q.left*q.right} ⊔ productIdeal qs

noncomputable def splitBound (I : Ideal (MvPolynomial σ K)) (d : G) :
    List (FactorPair (K := K) w) → ℕ
  | [] => Module.finrank K (componentQuotient w I d)
  | q :: qs => splitBound (I ⊔ Ideal.span {q.left}) d qs +
      splitBound (I ⊔ Ideal.span {q.right}) (d-q.leftDegree) qs

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section Blocks
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

noncomputable def blockWeight (group : σ → ι) (v : σ) : ι → ℤ :=
  Pi.single (group v) 1

lemma sum_blockWeight (group : σ → ι) (m : σ →₀ ℕ) :
    ∑ j, Finsupp.weight (blockWeight group) m j = (m.degree : ℤ) := by
  classical
  rw [Finsupp.weight_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_comm]
  simp only [blockWeight, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Finsupp.degree_eq_weight_one, Finsupp.weight_eq_sum]
  simp

lemma finite_block_degree (group : σ → ι) (d : ι → ℤ) :
    Set.Finite {m : σ →₀ ℕ | Finsupp.weight (blockWeight group) m = d} := by
  apply (Finsupp.finite_of_degree_le (∑ j, d j).toNat).subset
  intro m hm
  have hs := sum_blockWeight group m
  rw [hm] at hs
  change m.degree ≤ (∑ j, d j).toNat
  rw [hs]
  simp

instance blockPiece_finite (group : σ → ι) (d : ι → ℤ) :
    Module.Finite K (Piece (K := K) (blockWeight group) d) := by
  rw [Piece, weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_block_degree group d).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K
    {m | Finsupp.weight (blockWeight group) m = d})

end Blocks
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearLeaves
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

noncomputable def blockExponent (group : σ → ι) (m : σ →₀ ℕ) (j : ι) : ℕ :=
  ∑ v ∈ Finset.univ.filter (group · = j), m v

noncomputable def componentEmbed (group : σ → ι) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) : componentQuotient (blockWeight group) I d →ₗ[K]
      (MvPolynomial σ K ⧸ I) :=
  Submodule.liftQ _ ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
    (Piece (K := K) (blockWeight group) d).subtype) (by
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp)

end LinearLeaves
end PermanentBorder.Multigraded

end OAI


