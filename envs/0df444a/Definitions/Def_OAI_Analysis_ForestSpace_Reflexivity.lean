-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
-- name    : OAI_Analysis_ForestSpace_Reflexivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:02:41.135605+00:00
-- url     : https://prove2.me/theorems/53251a6a-925e-45cc-a841-d41d27dec993
-- title:
--   Reflexivity of Hilbert spaces, of $\ell_2$-sums, and of segment-norm completions with bounded segments
-- statement:
--   A real normed space $E$ is *reflexive* if the canonical embedding $E\to E^{**}$ into its bidual is surjective. The file collects the following results.
--
--   1. **Transfer and Hilbert spaces.** If $E\cong F$ via a continuous linear isomorphism and $F$ is reflexive, then $E$ is reflexive. Every real Hilbert space, that is, every complete real inner product space, is reflexive.
--   2. **Duality for $\ell_2$-sums.** Let $(E_i)_{i\in I}$ be real normed spaces indexed by an arbitrary set $I$, and let $\ell_2(E_i)$ be their $\ell_2$-sum. For $x\in E_i$, $\delta_i x$ denotes the element with $x$ in coordinate $i$ and $0$ elsewhere. The pairing
--   $$
--   \Lambda:\ell_2(E_i^*)\to\ell_2(E_i)^*,\qquad \Lambda(a)(x)=\sum_{i\in I}a_i(x_i),
--   $$
--   is a continuous linear map with $\Lambda(a)(\delta_i x)=a_i(x)$ and $\Lambda(\delta_i\varphi)(x)=\varphi(x_i)$. For $\varphi\in\ell_2(E_i)^*$, let $\varphi_i=\varphi\circ\delta_i\in E_i^*$. The file proves the following. First, if $\|u_i\|\le1$ for all $i$, then $\bigl\|\sum_{i\in S}a_i\,\delta_i u_i\bigr\|\le\bigl(\sum_{i\in S}a_i^2\bigr)^{1/2}$ for every finite $S\subseteq I$ and all real $a_i$. Second, the series $\sum_i\|\varphi_i\|^2$ converges for every $\varphi$. Third, $\Lambda$ is surjective. Consequently, $\ell_2(E_i)$ is reflexive whenever every $E_i$ is reflexive.
--   3. **Identifying a completion.** Let $E$ be a real normed space and $F$ a real Banach space. Let $f:E\to F$ be a continuous linear map with dense range such that $\|x\|\le K\|f(x)\|$ for all $x\in E$, for some $K\ge0$. Then the completion of $E$ is isomorphic to $F$ via a continuous linear isomorphism. In addition, a linear map $f:E\to\ell_2(G_i)$, not assumed continuous, has dense range as soon as the closure of its range contains every single-coordinate vector $\delta_i x$.
--   4. **Comparison with $\ell_2(V)$.** Let $V$ be a partial order, let $T(V)$ be the finitely supported real functions on $V$ with the disjoint-segment norm $\rho$, and let $J(V)$ be its completion. The formal identity $T(V)\to\ell_2(V)$, $u\mapsto(u(v))_{v\in V}$, satisfies $\|u\|_{\ell_2}^2=\sum_{v\in\operatorname{supp}u}u(v)^2$ and $\|u\|_{\ell_2}\le\rho(u)$. So it is continuous of norm at most $1$, and it has dense range. Also $\sum_{v\in S}u(v)^2\le\sum_{v\in\operatorname{supp}u}u(v)^2$ for every finite $S\subseteq V$. If $C\in\mathbb{N}$ and every segment of $V$ has at most $C$ elements, then
--   $$
--   \|u\|_{\ell_2}\le\rho(u)\le\sqrt{C}\,\|u\|_{\ell_2}\qquad(u\in T(V)),
--   $$
--   and $J(V)$ is reflexive.
--   5. **Components of the finite-height forest.** Let $\mathcal V=\bigsqcup_{h\ge1}\mathbb{N}^{\le h}$ be the forest of pairs $(h,s)$ with $h\ge1$ and $|s|\le h$. For $h\in\mathbb{N}$, let $\mathcal V_h$ be the set of its vertices of height $h$, with the induced order. It is the tree $\mathbb{N}^{\le h}$ when $h\ge1$ and is empty when $h=0$. Every segment of $\mathcal V_h$ has at most $h+1$ elements, and therefore $J(\mathcal V_h)$ is reflexive for every $h\in\mathbb{N}$.
--
--   These results reduce the reflexivity of the segment-norm completion over the finite-height forest to Hilbert-space facts. When segments have uniformly bounded size, the two norms in item 4 are equivalent, so item 3 makes $J(V)$ a copy of $\ell_2(V)$. Each component $J(\mathcal V_h)$ is thus isomorphic to a Hilbert space, with constants depending on $h$, and an $\ell_2$-sum of reflexive spaces is reflexive.
--
--   **Formalization Note** Reflexivity is the predicate `Reflexive E`, defined as surjectivity of `NormedSpace.inclusionInDoubleDual ℝ E`. The $\ell_2$-sums are Mathlib's `lp E 2`. The map $\Lambda$ is `l2DualMap`, built from `lp.dualPairing`, and its value is a `tsum`. The functional $\varphi_i$ is `l2Restriction`, the formal identity is `rawL2` (`rawL2Linear` before continuity is proved), and $\mathcal V_h$ is `Component h`, a subtype of `Vertex`. In item 3 the constant is `K : NNReal`, and the isomorphism is returned as `Nonempty (UniformSpace.Completion E ≃L[ℝ] F)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Reflexivity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Reflexivity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Reflexivity

 theorem reflexive_of_equiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (hF : Reflexive F) : Reflexive E := by
  intro Φ
  let Ψ := Φ.comp (ContinuousLinearMap.precomp ℝ e.toContinuousLinearMap)
  obtain ⟨y,hy⟩ := hF Ψ
  refine ⟨e.symm y,?_⟩
  ext φ
  have hh := congrArg (fun z : StrongDual ℝ (StrongDual ℝ F) => z (φ.comp e.symm.toContinuousLinearMap)) hy
  have he : (φ.comp e.symm.toContinuousLinearMap).comp e.toContinuousLinearMap = φ := by
    ext x
    simp
  change φ (e.symm y) = Φ ((φ.comp e.symm.toContinuousLinearMap).comp e.toContinuousLinearMap) at hh
  rw [he] at hh
  exact hh

 theorem reflexive_hilbert (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] : Reflexive H := by
  intro Φ
  let R : H ≃L[ℝ] StrongDual ℝ H := (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv
  let x := R.symm (Φ.comp R.toContinuousLinearMap)
  refine ⟨x,?_⟩
  ext φ
  obtain ⟨y,rfl⟩ := R.surjective φ
  change @inner ℝ H _ y x = Φ (R y)
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

section L2Dual
variable {I : Type} (E : I → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

noncomputable def l2DualMap : lp (fun i => StrongDual ℝ (E i)) 2 →L[ℝ] StrongDual ℝ (lp E 2) :=
  lp.dualPairing 2 2 (fun i => ContinuousLinearMap.id ℝ (StrongDual ℝ (E i)))
    (K := 1) (fun _ => ContinuousLinearMap.norm_id_le)

@[simp] theorem l2DualMap_apply (a : lp (fun i => StrongDual ℝ (E i)) 2) (x : lp E 2) :
    l2DualMap E a x = ∑' i, a i (x i) := rfl

@[simp] theorem l2DualMap_single_right (a : lp (fun i => StrongDual ℝ (E i)) 2)
    (i : I) (x : E i) : l2DualMap E a (lp.single 2 i x) = a i x := by
  rw [l2DualMap_apply,tsum_eq_single i]
  · simp
  · intro j hj
    simp [Pi.single_eq_of_ne hj]

@[simp] theorem l2DualMap_single_left (i : I) (φ : StrongDual ℝ (E i)) (x : lp E 2) :
    l2DualMap E (lp.single 2 i φ) x = φ (x i) := by
  rw [l2DualMap_apply,tsum_eq_single i]
  · simp
  · intro j hj
    simp [Pi.single_eq_of_ne hj]

noncomputable def l2Restriction (φ : StrongDual ℝ (lp E 2)) (i : I) : StrongDual ℝ (E i) :=
  φ.comp (lp.singleContinuousLinearMap ℝ E 2 i)

 theorem l2_norm_sum_unit_le (u : ∀ i, E i) (hu : ∀ i, ‖u i‖ ≤ 1)
    (S : Finset I) (a : I → ℝ) :
    ‖∑ i ∈ S, a i • lp.single 2 i (u i)‖ ≤ Real.sqrt (∑ i ∈ S, a i ^ 2) := by
  have he := lp.norm_sum_single (p := 2) (by norm_num) (fun i => a i • u i) S
  have he' : ‖∑ i ∈ S, a i • lp.single 2 i (u i)‖^2 =
      ∑ i ∈ S, (|a i| * ‖u i‖)^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,lp.single_smul,norm_smul,
      Real.norm_eq_abs] using he
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),he']
  apply Finset.sum_le_sum
  intro i hi
  have hh := mul_le_mul_of_nonneg_left (hu i) (abs_nonneg (a i))
  have hh' : (|a i| * ‖u i‖)^2 ≤ |a i|^2 :=
    (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)).mpr (by simpa using hh)
  simpa only [sq_abs] using hh'

 theorem l2_restriction_summable (φ : StrongDual ℝ (lp E 2)) :
    Summable (fun i => ‖l2Restriction E φ i‖^2) := by
  have hc : ∀ i, ∃ u : E i, ‖u‖ ≤ 1 ∧ ‖l2Restriction E φ i‖/2 ≤ ‖l2Restriction E φ i u‖ := by
    intro i
    by_cases hz : ‖l2Restriction E φ i‖ = 0
    · exact ⟨0,by simp,by simp [hz]⟩
    · have hp : 0 < ‖l2Restriction E φ i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      obtain ⟨u,hu,hφ⟩ := (l2Restriction E φ i).exists_lt_apply_of_lt_opNorm (half_lt_self hp)
      exact ⟨u,hu.le,hφ.le⟩
  choose u hu hφ using hc
  have hb := dual_vectors_squares_le (fun i => lp.single 2 i (u i)) (l2_norm_sum_unit_le E u hu) φ
  apply summable_of_sum_le (fun _ => sq_nonneg _) (c := 4*‖φ‖^2)
  intro S
  calc
    (∑ i ∈ S, ‖l2Restriction E φ i‖^2) ≤ ∑ i ∈ S, 4*(φ (lp.single 2 i (u i)))^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := hφ i
      change ‖l2Restriction E φ i‖/2 ≤ |φ (lp.single 2 i (u i))| at hh
      have h0 := norm_nonneg (l2Restriction E φ i)
      have h1 := abs_nonneg (φ (lp.single 2 i (u i)))
      nlinarith [sq_abs (φ (lp.single 2 i (u i)))]
    _ = 4*∑ i ∈ S, (φ (lp.single 2 i (u i)))^2 := by rw [Finset.mul_sum]
    _ ≤ 4*‖φ‖^2 := mul_le_mul_of_nonneg_left (hb S) (by norm_num)

 theorem l2DualMap_surjective : Function.Surjective (l2DualMap E) := by
  intro φ
  let a : lp (fun i => StrongDual ℝ (E i)) 2 := ⟨l2Restriction E φ, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using l2_restriction_summable E φ)⟩
  refine ⟨a,?_⟩
  apply lp.ext_continuousLinearMap (by norm_num)
  intro i
  ext x
  exact l2DualMap_single_right E a i x

 theorem reflexive_l2 (hE : ∀ i, Reflexive (E i)) : Reflexive (lp E 2) := by
  intro Φ
  obtain ⟨g,hg⟩ := l2DualMap_surjective (fun i => StrongDual ℝ (E i)) (Φ.comp (l2DualMap E))
  choose u hu using (fun i => hE i (g i))
  have hn : ∀ i, ‖u i‖ = ‖g i‖ := by
    intro i
    rw [← hu i]
    exact (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map (u i) |>.symm
  let x : lp E 2 := ⟨u,memℓp_gen (by
    simpa only [hn] using (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp g))⟩
  refine ⟨x,?_⟩
  ext φ
  obtain ⟨a,rfl⟩ := l2DualMap_surjective E φ
  have hh := congrArg (fun z : StrongDual ℝ (lp (fun i => StrongDual ℝ (E i)) 2) => z a) hg
  simp only [ContinuousLinearMap.comp_apply,l2DualMap_apply] at hh ⊢
  rw [← hh]
  apply tsum_congr
  intro i
  rw [← hu i]
  rfl

end L2Dual
end Reflexivity

section CompletionIsomorphism
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

 theorem completion_equiv_of_bounds (f : E →L[ℝ] F) (K : NNReal)
    (hK : ∀ x, ‖x‖ ≤ K*‖f x‖) (hd : DenseRange f) :
    Nonempty (UniformSpace.Completion E ≃L[ℝ] F) := by
  let L : UniformSpace.Completion E →L[ℝ] F := f.extend UniformSpace.Completion.toComplL
  have he : ∀ x : E, L (x : UniformSpace.Completion E) = f x := by
    intro x
    exact f.extend_eq UniformSpace.Completion.denseRange_coe
      (UniformSpace.Completion.isUniformInducing_coe E) x
  have hL : ∀ x, ‖x‖ ≤ K*‖L x‖ := by
    intro x
    refine UniformSpace.Completion.induction_on x
      (isClosed_le continuous_norm (continuous_const.mul L.continuous.norm)) ?_
    intro x
    simpa only [he,UniformSpace.Completion.norm_coe] using hK x
  have ha := L.antilipschitz_of_bound hL
  have hs : Function.Surjective L := by
    intro y
    apply closure_minimal (t := Set.range L) ?_ (ha.isClosed_range L.uniformContinuous) (hd y)
    rintro _ ⟨x,rfl⟩
    exact ⟨(x : UniformSpace.Completion E),he x⟩
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr ha.injective)
    (LinearMap.range_eq_top.mpr hs)⟩

 theorem denseRange_lp_of_singles {I : Type} (G : I → Type)
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
    (f : E →ₗ[ℝ] lp G 2)
    (hs : ∀ i (x : G i), lp.single 2 i x ∈ f.range.topologicalClosure) : DenseRange f := by
  intro x
  have hh : x ∈ f.range.topologicalClosure := by
    apply (Submodule.isClosed_topologicalClosure f.range).mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x)
    exact Filter.Eventually.of_forall (fun S => Submodule.sum_mem _ (fun i hi => hs i (x i)))
  exact hh

end CompletionIsomorphism

section ComponentHilbert
variable {V : Type} [PartialOrder V]

noncomputable def rawL2Linear : TestVector V →ₗ[ℝ] lp (fun _ : V => ℝ) 2 where
  toFun u := ⟨(fun v => u v),memℓp_gen (by
    apply summable_of_ne_finset_zero (s := u.toFinsupp.support)
    intro v hv
    have hz : u v = 0 := Finsupp.notMem_support_iff.mp hv
    simp [hz])⟩
  map_add' u v := by ext w; rfl
  map_smul' a u := by ext w; rfl

omit [PartialOrder V] in
@[simp] theorem rawL2Linear_apply [PartialOrder V] (u : TestVector V) (v : V) : rawL2Linear u v = u v := rfl

omit [PartialOrder V] in
 theorem rawL2_norm_sq [PartialOrder V] (u : TestVector V) :
    ‖rawL2Linear u‖^2 = ∑ v ∈ u.toFinsupp.support, u v^2 := by
  have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (rawL2Linear u)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,rawL2Linear_apply,Real.norm_eq_abs,sq_abs] at he
  rw [he]
  apply tsum_eq_sum
  intro v hv
  have hz : u v = 0 := Finsupp.notMem_support_iff.mp hv
  simp [hz]

 theorem rawL2_norm_le (u : TestVector V) : ‖rawL2Linear u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [rawL2_norm_sq]
  exact coordinate_squares_le _ u

noncomputable def rawL2 : TestVector V →L[ℝ] lp (fun _ : V => ℝ) 2 :=
  rawL2Linear.mkContinuous 1 (by intro u; simpa only [one_mul] using rawL2_norm_le u)

@[simp] theorem rawL2_apply (u : TestVector V) : rawL2 u = rawL2Linear u := rfl

omit [PartialOrder V] in
 theorem sum_sq_le_support [PartialOrder V] (u : TestVector V) (S : Finset V) :
    ∑ v ∈ S, u v^2 ≤ ∑ v ∈ u.toFinsupp.support, u v^2 := by
  have he : (∑ v ∈ S ∪ u.toFinsupp.support, u v^2) = ∑ v ∈ u.toFinsupp.support, u v^2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro v hv hn
    have hz : u v = 0 := Finsupp.notMem_support_iff.mp hn
    simp [hz]
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => sq_nonneg _)

 theorem rho_le_card_bound (C : ℕ) (hC : ∀ S : Finset V, IsSegment S → S.card ≤ C)
    (u : TestVector V) : ‖u‖ ≤ Real.sqrt C * ‖rawL2 u‖ := by
  apply (TestVector.norm_le_iff_testBound u (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
  intro I inst S hS hd
  have hloc : ∀ i, (segSum u (S i))^2 ≤ C * ∑ v ∈ S i, u v^2 := by
    intro i
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (S i) (fun _ => (1:ℝ)) (fun v => u v)
    simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    apply hh.trans
    change (S i).card * (∑ v ∈ S i, u v^2) ≤ (C : ℝ) * _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC (S i) (hS i))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hsum : (∑ i, ∑ v ∈ S i, u v^2) ≤ ∑ v ∈ u.toFinsupp.support, u v^2 := by
    rw [← Finset.sum_biUnion (s := Finset.univ) (t := S) (by
      intro i hi j hj hij
      exact hd hij)]
    exact sum_sq_le_support u _
  have hm : (∑ i, (C : ℝ) * ∑ v ∈ S i, u v^2) ≤ (C : ℝ) * ∑ v ∈ u.toFinsupp.support, u v^2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg C)
  have hh := (Finset.sum_le_sum (s := Finset.univ) (fun i hi => hloc i)).trans hm
  simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg C),rawL2_apply,rawL2_norm_sq] using hh

 theorem rawL2_dense : DenseRange (rawL2 (V := V)) := by
  apply denseRange_lp_of_singles (fun _ : V => ℝ) rawL2Linear
  intro v a
  apply Submodule.le_topologicalClosure
  refine ⟨TestVector.single v a,?_⟩
  ext w
  simp [TestVector.single_apply,lp.single_apply,Pi.single_apply,eq_comm]

 theorem reflexive_J_of_segment_card_bound (C : ℕ)
    (hC : ∀ S : Finset V, IsSegment S → S.card ≤ C) : Reflexive (J V) := by
  obtain ⟨e⟩ := completion_equiv_of_bounds (rawL2 (V := V)) ⟨Real.sqrt C,Real.sqrt_nonneg _⟩
    (rho_le_card_bound C hC) rawL2_dense
  exact reflexive_of_equiv e (reflexive_hilbert _)

abbrev Component (h : ℕ) := {v : Vertex // v.height = h}

 theorem component_segment_card (h : ℕ) (S : Finset (Component h)) (hS : IsSegment S) :
    S.card ≤ h+1 := by
  let f : S → Fin (h+1) := fun v => ⟨v.val.val.word.letters.length, by
    have hh := v.val.val.bounded
    rw [v.val.property] at hh
    omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hl : a.val.val.word.letters.length = b.val.val.word.letters.length := congrArg Fin.val hab
    apply Subtype.ext
    apply Subtype.ext
    apply Vertex.ext (a.val.property.trans b.val.property.symm)
    apply Word.ext
    rcases hS.1 a a.property b b.property with h | h
    · exact h.2.eq_of_length hl
    · exact (h.2.eq_of_length hl.symm).symm
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hh

 theorem reflexive_component (h : ℕ) : Reflexive (J (Component h)) :=
  reflexive_J_of_segment_card_bound (h+1) (component_segment_card h)

end ComponentHilbert

end

end ForestSpace

end OAI


