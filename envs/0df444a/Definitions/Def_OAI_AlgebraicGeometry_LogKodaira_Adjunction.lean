-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
-- name    : OAI_AlgebraicGeometry_LogKodaira_Adjunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:45:19.397404+00:00
-- url     : https://prove2.me/theorems/d7ba0d92-d46f-460d-aeb4-b3d3641021d1
-- title:
--   Determinant lines of a split short exact sequence: $\bigwedge^{n}M\otimes\bigwedge^{r}P\cong\bigwedge^{n+r}N$ via adapted bases
-- statement:
--   This file develops the linear algebra of determinant lines behind adjunction isomorphisms of canonical modules. Throughout, $R$ is a commutative ring and $M,N,P$ are $R$-modules. For a basis $b=(b_1,\dots,b_n)$ of $M$ and vectors $v_1,\dots,v_n\in M$, $\det_b(v)$ denotes the determinant of the $n\times n$ matrix whose $j$-th column is the coordinate vector of $v_j$ in the basis $b$.
--
--   1. **Base-changed differentials.** For ring homomorphisms $R\to A\to B$, the $B$-module $B\otimes_A\Omega_{A/R}$, the Kähler differentials of $A$ over $R$ extended to $B$.
--   2. **Expansion of alternating maps.** If $b$ is a basis of $M$ with $n$ elements and $\varphi\colon M^n\to N$ is an alternating $R$-multilinear map, then $\varphi(v_1,\dots,v_n)=\det_b(v)\,\varphi(b_1,\dots,b_n)$ for all $v_1,\dots,v_n\in M$.
--   3. **Determinant coordinate.** For a basis $b$ of $M$ with $n$ elements, $\delta_b\colon\bigwedge^n_R M\to R$ is the $R$-linear isomorphism with $\delta_b(v_1\wedge\cdots\wedge v_n)=\det_b(v)$; its inverse is $\lambda\mapsto\lambda\,b_1\wedge\cdots\wedge b_n$.
--   4. **Splitting a short exact sequence.** Let $f\colon M\to N$ be injective, let $q\colon N\to P$ satisfy $\operatorname{im}f=\ker q$, and let $s\colon P\to N$ be a section of $q$, i.e. $q\circ s=\mathrm{id}_P$. Then $(x,y)\mapsto f(x)+s(y)$ is an $R$-linear isomorphism $M\times P\cong N$; the second component of its inverse is $q$, and its inverse sends $f(x)$ to $(x,0)$.
--   5. **Adapted basis.** If moreover $b$ is a basis of $M$ with $n$ elements and $c$ a basis of $P$ with $r$ elements, the image of the product basis under the isomorphism of item 4 is the basis $f(b_1),\dots,f(b_n),s(c_1),\dots,s(c_r)$ of $N$. Its determinant is block triangular: for all $v_1,\dots,v_n\in M$ and $z_1,\dots,z_r\in N$,
--   $$\det\nolimits_{\mathrm{adapted}}\big(f(v_1),\dots,f(v_n),z_1,\dots,z_r\big)=\det\nolimits_b(v)\cdot\det\nolimits_c\big(q(z_1),\dots,q(z_r)\big).$$
--   6. **Split determinant isomorphism.** In the same situation, the $R$-linear isomorphism $\bigwedge^n_R M\otimes_R\bigwedge^r_R P\cong\bigwedge^{n+r}_R N$ obtained by composing $\delta_b\otimes\delta_c$, the multiplication $R\otimes_R R\cong R$ and the inverse of the determinant coordinate of the adapted basis (listed in the order above). It satisfies
--   $$\big(v_1\wedge\cdots\wedge v_n\big)\otimes\big(q(z_1)\wedge\cdots\wedge q(z_r)\big)\longmapsto f(v_1)\wedge\cdots\wedge f(v_n)\wedge z_1\wedge\cdots\wedge z_r .$$
--   7. **Determinant isomorphism of a short exact sequence.** Let $0\to M\xrightarrow{f}N\xrightarrow{q}P\to0$ be a short exact sequence of $R$-modules ($f$ injective, $\operatorname{im}f=\ker q$, $q$ surjective) with $P$ projective, and let $b$ and $c$ be bases of $M$ and $P$ with $n$ and $r$ elements. Then there exists an $R$-linear isomorphism $e\colon\bigwedge^n_R M\otimes_R\bigwedge^r_R P\to\bigwedge^{n+r}_R N$ such that, for all $v_1,\dots,v_n\in M$ and $z_1,\dots,z_r\in N$,
--   $$e\Big(\big(v_1\wedge\cdots\wedge v_n\big)\otimes\big(q(z_1)\wedge\cdots\wedge q(z_r)\big)\Big)=f(v_1)\wedge\cdots\wedge f(v_n)\wedge z_1\wedge\cdots\wedge z_r .$$
--
--   Item 7 is the algebraic form of the adjunction formula $\det N\cong\det M\otimes\det P$ for a short exact sequence of free modules. For a formally smooth algebra $A\to B$ over $R$ it is applied to the exact sequence $0\to B\otimes_A\Omega_{A/R}\to\Omega_{B/R}\to\Omega_{B/A}\to0$, where it splits top-degree differential forms of $B$ into a part pulled back from the base $A$ and a relative part; this is how forms on the total space of a fibration are later restricted to the fibres.
--
--   **Formalization Note** The items are `BaseDifferentials` (1), `alternating_basis_formula` (2), `determinantCoordinate` with `determinantCoordinate_wedge` (3), `split_coprod_bijective` and `splitEquiv` with `splitEquiv_apply`, `splitEquiv_symm_snd`, `splitEquiv_symm_f` (4), `adaptedBasis` and `adaptedBasis_det` (5), `splitDeterminantEquiv` and `splitDeterminantEquiv_wedge` (6), and the theorem `exact_canonical_adjunction` (7). Bases are indexed by `Fin n` and `Fin r`, the adapted basis by the sum type `Fin n ⊕ Fin r` (reindexed to `Fin (n + r)` in item 6), and the concatenated family is `Fin.append`. In item 7 projectivity of $P$ is a separate instance hypothesis (it also follows from the existence of the basis $c$); it is used to choose a section $s$ of $q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/Adjunction.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/Adjunction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LogKodairaFiberNegative mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
open scoped TensorProduct
namespace ReverseLogKodaira.CanonicalAdjunction

abbrev BaseDifferentials (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] := B ⊗[A] KaehlerDifferential R A

section DeterminantLine
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

lemma alternating_basis_formula (b : Module.Basis (Fin n) R M)
    (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) :
    f v = b.det v • f b := by
  have h : f = b.det.smulRight (f b) := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change f (b ∘ σ) = (b.det.smulRight (f b)) (b ∘ σ)
    simp [AlternatingMap.map_perm, Module.Basis.det_self]
  exact DFunLike.congr_fun h v

 
def determinantCoordinate (b : Module.Basis (Fin n) R M) : ⋀[R]^n M ≃ₗ[R] R where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv b.det
  invFun c := c • exteriorPower.ιMulti R n b
  left_inv := by
    intro x
    have h : ((LinearMap.id : ⋀[R]^n M →ₗ[R] ⋀[R]^n M)) =
        (LinearMap.toSpanSingleton R (⋀[R]^n M) (exteriorPower.ιMulti R n b)).comp
          (exteriorPower.alternatingMapLinearEquiv b.det) := by
      apply LinearMap.ext_on (exteriorPower.ιMulti_span R n M)
      rintro _ ⟨v, rfl⟩
      simpa using alternating_basis_formula b (exteriorPower.ιMulti R n) v
    exact (LinearMap.congr_fun h x).symm
  right_inv := by
    intro c
    simp [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self]

@[simp] lemma determinantCoordinate_wedge (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    determinantCoordinate b (exteriorPower.ιMulti R n v) = b.det v := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v

end DeterminantLine

section SplitSequence
variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
variable (f : M →ₗ[R] N) (q : N →ₗ[R] P) (s : P →ₗ[R] N)
  (hf : Function.Injective f) (he : Function.Exact f q) (hs : q ∘ₗ s = LinearMap.id)

include hf he hs
lemma split_coprod_bijective : Function.Bijective (f.coprod s) := by
  have hqs (y : P) : q (s y) = y := LinearMap.congr_fun hs y
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    rintro ⟨x, y⟩ hxy
    change f x + s y = 0 at hxy
    have hy : y = 0 := by
      have h := congrArg q hxy
      simpa [he.apply_apply_eq_zero, hqs] using h
    have hx : x = 0 := by
      apply hf
      simpa [hy] using hxy
    simp [hx, hy]
  · intro z
    have hz : q (z - s (q z)) = 0 := by simp [hqs]
    obtain ⟨x, hx⟩ := (he (z - s (q z))).mp hz
    refine ⟨(x, q z), ?_⟩
    simp [hx]

 
def splitEquiv : (M × P) ≃ₗ[R] N :=
  LinearEquiv.ofBijective (f.coprod s) (split_coprod_bijective f q s hf he hs)

@[simp] lemma splitEquiv_apply (x : M × P) :
    splitEquiv f q s hf he hs x = f x.1 + s x.2 := rfl

lemma splitEquiv_symm_snd (z : N) :
    ((splitEquiv f q s hf he hs).symm z).2 = q z := by
  have hqs (y : P) : q (s y) = y := LinearMap.congr_fun hs y
  have h := congrArg q ((splitEquiv f q s hf he hs).apply_symm_apply z)
  simpa only [splitEquiv_apply, map_add, he.apply_apply_eq_zero, hqs, zero_add] using h

lemma splitEquiv_symm_f (x : M) :
    (splitEquiv f q s hf he hs).symm (f x) = (x, 0) := by
  apply (splitEquiv f q s hf he hs).injective
  simp

variable {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P)

 
def adaptedBasis : Module.Basis (Fin n ⊕ Fin r) R N :=
  (b.prod c).map (splitEquiv f q s hf he hs)

lemma adaptedBasis_det (v : Fin n → M) (z : Fin r → N) :
    (adaptedBasis f q s hf he hs b c).det (Sum.elim (f ∘ v) z) =
      b.det v * c.det (q ∘ z) := by
  rw [adaptedBasis, Module.Basis.det_map, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix : (b.prod c).toMatrix
      ((splitEquiv f q s hf he hs).symm ∘ Sum.elim (f ∘ v) z) =
      Matrix.fromBlocks (b.toMatrix v)
        (b.toMatrix fun j => ((splitEquiv f q s hf he hs).symm (z j)).1)
        0 (c.toMatrix (q ∘ z)) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [Module.Basis.toMatrix_apply, splitEquiv_symm_f]
      | inr j => simp [Module.Basis.toMatrix_apply]
    | inr i =>
      cases j with
      | inl j => simp [Module.Basis.toMatrix_apply, splitEquiv_symm_f]
      | inr j => simp [Module.Basis.toMatrix_apply, splitEquiv_symm_snd]
  rw [hmatrix, Matrix.det_fromBlocks_zero₂₁]

 
def splitDeterminantEquiv :
    (⋀[R]^n M) ⊗[R] (⋀[R]^r P) ≃ₗ[R] ⋀[R]^(n + r) N :=
  ((TensorProduct.congr (determinantCoordinate b) (determinantCoordinate c)).trans
    (TensorProduct.lid R R)).trans
      (determinantCoordinate
        ((adaptedBasis f q s hf he hs b c).reindex finSumFinEquiv)).symm

lemma splitDeterminantEquiv_wedge (v : Fin n → M) (z : Fin r → N) :
    splitDeterminantEquiv f q s hf he hs b c
      (exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z)) =
      exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) := by
  apply (determinantCoordinate
    ((adaptedBasis f q s hf he hs b c).reindex finSumFinEquiv)).injective
  have happend : Fin.append (f ∘ v) z ∘ finSumFinEquiv = Sum.elim (f ∘ v) z := by
    funext i
    cases i <;> simp
  simp only [splitDeterminantEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, determinantCoordinate_wedge, TensorProduct.lid_tmul,
    smul_eq_mul, LinearEquiv.apply_symm_apply, Module.Basis.det_reindex, happend]
  exact (adaptedBasis_det f q s hf he hs b c v z).symm

end SplitSequence

 

theorem exact_canonical_adjunction
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (f : M →ₗ[R] N) (q : N →ₗ[R] P)
    (hf : Function.Injective f) (he : Function.Exact f q) (hq : Function.Surjective q)
    {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P) :
    ∃ e : (⋀[R]^n M) ⊗[R] (⋀[R]^r P) ≃ₗ[R] ⋀[R]^(n + r) N,
      ∀ (v : Fin n → M) (z : Fin r → N),
        e (exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z)) =
          exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  exact ⟨splitDeterminantEquiv f q s hf he hs b c,
    splitDeterminantEquiv_wedge f q s hf he hs b c⟩

 

end ReverseLogKodaira.CanonicalAdjunction

end
end

end OAI


