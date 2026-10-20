-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_RealGraph
-- name    : OAI_Analysis_ModularRecovery_RealGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:17:23.180483+00:00
-- url     : https://prove2.me/theorems/4222ef81-9643-4826-b102-569d7680bdab
-- title:
--   Orbit graphs and their projections
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Hilbert pairs.** The Hilbert direct sum $H\oplus H$, with the pairing map, the inclusions of the two summands, and the diagonal action $a\oplus a$ of an operator.
--   2. **Orbit graph.** For vectors $\xi,z$ and $\varepsilon>0$, the closed subspace
--   $$
--   G_\varepsilon=\overline{\{(a\xi,\ \varepsilon\,az):a\in M\}}\subseteq H\oplus H ,
--   $$
--   which is invariant under $M'$ acting diagonally; its orthogonal projection commutes with that action.
--   3. **Graph blocks and approximant.** The $2\times2$ blocks of the projection onto $G_\varepsilon$, and the operator $(2\varepsilon)^{-1}(P_{21}+P_{12})$. It is self-adjoint and lies in $M'$. As $\varepsilon\to0$ it is used to show that a vector $z$ with $\langle\xi,az\rangle=\langle z,a\xi\rangle$ for $a\in M$ is a limit of $b\xi$ with $b\in M'$ self-adjoint.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/RealGraph.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/RealGraph.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAI_Analysis_ModularRecovery_Model
import Definitions.Def_OAI_Analysis_ModularRecovery_SpectralCalculus
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaResolvent
import Definitions.Def_OAI_Analysis_ModularRecovery_PolarCutoff
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaFundamental

namespace OAI

/-! Real Hilbert graphs and commutation with orthogonal projections. -/

universe u uE

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev HilbertPair (H : Type u) := WithLp 2 (H × H)

namespace HilbertPair

def pair (x y : H) : HilbertPair H := WithLp.toLp 2 (x,y)

def inl : H →L[ℂ] HilbertPair H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H H)

def inr : H →L[ℂ] HilbertPair H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H H)

omit [CompleteSpace H] in
@[simp] lemma inl_apply (x : H) : inl x = pair x 0 := rfl
omit [CompleteSpace H] in
@[simp] lemma inr_apply (x : H) : inr x = pair 0 x := rfl

omit [CompleteSpace H] in
@[simp] lemma fst_inl (x : H) : WithLp.fstL 2 ℂ H H (inl x) = x := rfl
omit [CompleteSpace H] in
@[simp] lemma snd_inl (x : H) : WithLp.sndL 2 ℂ H H (inl x) = 0 := rfl
omit [CompleteSpace H] in
@[simp] lemma fst_inr (x : H) : WithLp.fstL 2 ℂ H H (inr x) = 0 := rfl
omit [CompleteSpace H] in
@[simp] lemma snd_inr (x : H) : WithLp.sndL 2 ℂ H H (inr x) = x := rfl

omit [CompleteSpace H] in
@[simp] lemma inner_pair (x y z w : H) :
    inner ℂ (pair x y) (pair z w) = inner ℂ x z + inner ℂ y w := by
  exact WithLp.prod_inner_apply _ _

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma pair_add (x y z w : H) : pair (x+z) (y+w) = pair x y + pair z w := rfl
omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma norm_pair_le (x y : H) : ‖pair x y‖ ≤ ‖x‖ + ‖y‖ := by
  have he : pair x y = pair x 0 + pair 0 y := by rw [← pair_add, add_zero, zero_add]
  rw [he]
  simpa only [pair, WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] using norm_add_le (pair x 0) (pair 0 y)

omit [CompleteSpace H] in
lemma pair_eq_inl_add_inr (x y : H) : pair x y = inl x + inr y := by
  rw [inl_apply, inr_apply, ← pair_add, add_zero, zero_add]

def diag (a : H →L[ℂ] H) : HilbertPair H →L[ℂ] HilbertPair H :=
  (inl.comp a).comp (WithLp.fstL 2 ℂ H H) +
    (inr.comp a).comp (WithLp.sndL 2 ℂ H H)

omit [CompleteSpace H] in
@[simp] lemma diag_pair (a : H →L[ℂ] H) (x y : H) :
    diag a (pair x y) = pair (a x) (a y) := by
  simp only [diag, add_apply, ContinuousLinearMap.comp_apply, inl_apply, inr_apply]
  change pair (a x) 0 + pair 0 (a y) = pair (a x) (a y)
  rw [← pair_add, add_zero, zero_add]

omit [CompleteSpace H] in
@[simp] lemma fst_diag (a : H →L[ℂ] H) (v : HilbertPair H) :
    WithLp.fstL 2 ℂ H H (diag a v) = a (WithLp.fstL 2 ℂ H H v) := by
  rcases v with ⟨x,y⟩
  exact congrArg (WithLp.fstL 2 ℂ H H) (diag_pair a x y)

omit [CompleteSpace H] in
@[simp] lemma snd_diag (a : H →L[ℂ] H) (v : HilbertPair H) :
    WithLp.sndL 2 ℂ H H (diag a v) = a (WithLp.sndL 2 ℂ H H v) := by
  rcases v with ⟨x,y⟩
  exact congrArg (WithLp.sndL 2 ℂ H H) (diag_pair a x y)

lemma star_diag (a : H →L[ℂ] H) : star (diag a) = diag (star a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  change inner ℂ (pair y₁ y₂) (star (diag a) (pair x₁ x₂)) =
    inner ℂ (pair y₁ y₂) (diag (star a) (pair x₁ x₂))
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [diag_pair, inner_pair, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

lemma star_inl : inl.adjoint = WithLp.fstL 2 ℂ H H := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rcases x with ⟨x₁,x₂⟩
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [inl_apply, pair]

lemma star_inr : inr.adjoint = WithLp.sndL 2 ℂ H H := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rcases x with ⟨x₁,x₂⟩
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [inr_apply, pair]

end HilbertPair

def orbitGraphMap (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    M.toStarSubalgebra →ₗ[ℂ] HilbertPair H where
  toFun a := HilbertPair.pair ((a : H →L[ℂ] H) xi) ((eps : ℂ) • (a : H →L[ℂ] H) z)
  map_add' a b := by
    change HilbertPair.pair _ ((eps:ℂ) • ((a:H →L[ℂ] H) z + (b:H →L[ℂ] H) z)) = _
    rw [smul_add]
    rfl
  map_smul' c a := by
    change HilbertPair.pair (c • (a:H →L[ℂ] H) xi) ((eps:ℂ) • (c • (a:H →L[ℂ] H) z)) = _
    rw [smul_comm (eps:ℂ) c]
    rfl

def orbitGraph (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    Submodule ℂ (HilbertPair H) := (orbitGraphMap M xi z eps).range.topologicalClosure

lemma orbitGraph_core_mem (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    HilbertPair.pair (a xi) ((eps : ℂ) • a z) ∈ orbitGraph M xi z eps := by
  exact Submodule.le_topologicalClosure _ ⟨⟨a,ha⟩, rfl⟩

lemma orbitGraph_invariant (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    orbitGraph M xi z eps ∈ Module.End.invtSubmodule (HilbertPair.diag a) := by
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rintro x ⟨b,rfl⟩
  refine ⟨⟨a*(b : H →L[ℂ] H), mul_mem ha b.property⟩, ?_⟩
  change HilbertPair.pair _ _ = HilbertPair.diag a (HilbertPair.pair _ _)
  simp only [HilbertPair.diag_pair, mul_apply_eq_comp, map_smul]

lemma projection_commute_of_invariant {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (G : Submodule ℂ E)
    [G.HasOrthogonalProjection] (a : E →L[ℂ] E)
    (ha : G ∈ Module.End.invtSubmodule a)
    (hast : G ∈ Module.End.invtSubmodule (star a : E →L[ℂ] E)) : Commute G.starProjection a := by
  have h := G.isIdempotentElem_starProjection
  have hp := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff h).mp
    (by simpa only [Submodule.range_starProjection] using ha)
  have hpst := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff h).mp
    (by simpa only [Submodule.range_starProjection] using hast)
  change G.starProjection * a * G.starProjection = a * G.starProjection at hp
  change G.starProjection * star a * G.starProjection = star a * G.starProjection at hpst
  have hh := congrArg star hpst
  simp only [star_mul, star_star, (isSelfAdjoint_starProjection G).star_eq] at hh
  exact (hp.symm.trans ((mul_assoc _ _ _).trans hh)).symm

instance orbitGraph_hasProjection (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    (orbitGraph M xi z eps).HasOrthogonalProjection := by
  unfold orbitGraph
  infer_instance

lemma orbitGraph_projection_commute (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    Commute (orbitGraph M xi z eps).starProjection (HilbertPair.diag a) := by
  apply projection_commute_of_invariant
  · exact orbitGraph_invariant M xi z eps a ha
  · rw [HilbertPair.star_diag]
    exact orbitGraph_invariant M xi z eps (star a) (star_mem ha)

lemma orbitGraph_block_mem (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (i j : Bool) :
    (if i then WithLp.sndL 2 ℂ H H else WithLp.fstL 2 ℂ H H).comp
      ((orbitGraph M xi z eps).starProjection.comp
        (if j then HilbertPair.inr else HilbertPair.inl)) ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have hh := orbitGraph_projection_commute M xi z eps a ha
  apply ContinuousLinearMap.ext
  intro h
  have he := congrArg (fun A : HilbertPair H →L[ℂ] HilbertPair H =>
    A ((if j then HilbertPair.inr else HilbertPair.inl) h)) hh.eq
  have he' := congrArg
    (fun x : HilbertPair H => (if i then WithLp.sndL 2 ℂ H H else WithLp.fstL 2 ℂ H H) x) he
  cases i <;> cases j <;>
    simpa only [Bool.false_eq_true, ↓reduceIte, mul_apply_eq_comp,
      ContinuousLinearMap.comp_apply, HilbertPair.inl_apply, HilbertPair.inr_apply,
      HilbertPair.diag_pair, HilbertPair.fst_diag, HilbertPair.snd_diag, map_zero] using he'.symm

def graphBlock (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) (i j : Bool) : H →L[ℂ] H :=
  (if i then WithLp.sndL 2 ℂ H H else WithLp.fstL 2 ℂ H H).comp
    ((orbitGraph M xi z eps).starProjection.comp
      (if j then HilbertPair.inr else HilbertPair.inl))

lemma graphBlock_mem (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) (i j : Bool) :
    graphBlock M xi z eps i j ∈ M.commutant := orbitGraph_block_mem M xi z eps i j

lemma graphBlock_star (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) (i j : Bool) :
    star (graphBlock M xi z eps i j) = graphBlock M xi z eps j i := by
  have hp : (orbitGraph M xi z eps).starProjection.adjoint =
      (orbitGraph M xi z eps).starProjection := (isSelfAdjoint_starProjection _).star_eq
  cases i <;> cases j <;>
    simp only [graphBlock, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ← HilbertPair.star_inl, ← HilbertPair.star_inr,
      ContinuousLinearMap.adjoint_adjoint, hp, ContinuousLinearMap.comp_assoc]

lemma orbitGraph_rot_mem_orthogonal (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi))
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    HilbertPair.pair (-(eps:ℂ) • a z) (a xi) ∈ (orbitGraph M xi z eps)ᗮ := by
  rw [orbitGraph, Submodule.orthogonal_closure]
  rintro x ⟨b,rfl⟩
  change inner ℂ (HilbertPair.pair ((b:H →L[ℂ] H) xi) ((eps:ℂ) • (b:H →L[ℂ] H) z))
    (HilbertPair.pair (-(eps:ℂ) • a z) (a xi)) = 0
  rw [HilbertPair.inner_pair, inner_smul_right, inner_smul_left]
  simp only [Complex.conj_ofReal]
  have hs : inner ℂ ((b:H →L[ℂ] H) xi) (a z) =
      inner ℂ ((b:H →L[ℂ] H) z) (a xi) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right]
    exact hz (star (b:H →L[ℂ] H) * a) (mul_mem (star_mem b.property) ha)
  rw [hs]
  ring

lemma projection_distance_le {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (G : Submodule ℂ E) [G.HasOrthogonalProjection]
    (x y : E) (hy : y ∈ G) : ‖G.starProjection x-x‖ ≤ ‖x-y‖ := by
  rw [norm_sub_rev, Submodule.starProjection_minimal]
  exact ciInf_le (show BddBelow (range (fun v : G => ‖x-(v:E)‖)) from
    ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩) (⟨y,hy⟩ : G)

lemma projection_norm_le_distance_orthogonal {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (G : Submodule ℂ E) [G.HasOrthogonalProjection]
    (x y : E) (hy : y ∈ Gᗮ) : ‖G.starProjection x‖ ≤ ‖x-y‖ := by
  have hh := projection_distance_le Gᗮ x y hy
  rw [G.starProjection_orthogonal_val] at hh
  simpa only [sub_sub_cancel_left, norm_neg] using hh

lemma orbitGraph_projection_inl_tendsto (M : VonNeumannAlgebra H) (xi z : H)
    (hcyc : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h})
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0)) (h : H) :
    Tendsto (fun n => (orbitGraph M xi z (eps n)).starProjection (HilbertPair.inl h))
      atTop (𝓝 (HilbertPair.inl h)) := by
  apply Metric.tendsto_atTop.mpr
  intro d hd
  obtain ⟨v,⟨a,ha,rfl⟩,hv⟩ := hcyc.exists_dist_lt h (show 0 < d/2 by positivity)
  have ht : Tendsto (fun n => ‖(eps n : ℂ) • a z‖) atTop (𝓝 0) := by
    have hh := (Complex.continuous_ofReal.tendsto _ |>.comp heps).smul_const (a z)
    convert hh.norm using 1 <;> simp
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 (d/2) (by positivity))
  refine ⟨N,fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hb := projection_distance_le (orbitGraph M xi z (eps n))
    (HilbertPair.inl h) (HilbertPair.pair (a xi) ((eps n:ℂ) • a z))
    (orbitGraph_core_mem M xi z (eps n) a ha)
  change _ ≤ ‖HilbertPair.pair (h-a xi) (0 - ((eps n:ℂ) • a z))‖ at hb
  rw [zero_sub] at hb
  have hl := hb.trans (HilbertPair.norm_pair_le _ _)
  simp only [norm_neg] at hl
  rw [dist_eq_norm] at hv
  linarith [hN n hn]

lemma orbitGraph_projection_inr_tendsto (M : VonNeumannAlgebra H) (xi z : H)
    (hcyc : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h})
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi))
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0)) (h : H) :
    Tendsto (fun n => (orbitGraph M xi z (eps n)).starProjection (HilbertPair.inr h))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro d hd
  obtain ⟨v,⟨a,ha,rfl⟩,hv⟩ := hcyc.exists_dist_lt h (show 0 < d/2 by positivity)
  have ht : Tendsto (fun n => ‖(eps n : ℂ) • a z‖) atTop (𝓝 0) := by
    have hh := (Complex.continuous_ofReal.tendsto _ |>.comp heps).smul_const (a z)
    convert hh.norm using 1 <;> simp
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 (d/2) (by positivity))
  refine ⟨N,fun n hn => ?_⟩
  rw [dist_zero_right]
  have hb := projection_norm_le_distance_orthogonal (orbitGraph M xi z (eps n))
    (HilbertPair.inr h) (HilbertPair.pair (-(eps n:ℂ) • a z) (a xi))
    (orbitGraph_rot_mem_orthogonal M xi z (eps n) hz a ha)
  have he : HilbertPair.inr h - HilbertPair.pair (-(eps n:ℂ) • a z) (a xi) =
      HilbertPair.pair ((eps n:ℂ) • a z) (h-a xi) := by
    change HilbertPair.pair (0 - (-(eps n:ℂ) • a z)) (h-a xi) = _
    simp only [neg_smul, sub_neg_eq_add, zero_add]
  rw [he] at hb
  have hl := hb.trans (HilbertPair.norm_pair_le _ _)
  rw [dist_eq_norm] at hv
  linarith [hN n hn]

lemma graphBlock_offdiag_xi (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi)) :
    graphBlock M xi z eps true false xi =
        (eps:ℂ) • (z-graphBlock M xi z eps true true z) ∧
    graphBlock M xi z eps false true xi =
        (eps:ℂ) • graphBlock M xi z eps false false z := by
  let G := orbitGraph M xi z eps
  have hc : HilbertPair.pair xi ((eps:ℂ) • z) ∈ G := by
    simpa only [one_apply_eq_self] using orbitGraph_core_mem M xi z eps 1 (one_mem _)
  have ho : HilbertPair.pair (-(eps:ℂ) • z) xi ∈ Gᗮ := by
    simpa only [one_apply_eq_self] using orbitGraph_rot_mem_orthogonal M xi z eps hz 1 (one_mem _)
  have hc' := congrArg (WithLp.sndL 2 ℂ H H) (G.starProjection_eq_self_iff.mpr hc)
  have ho' := congrArg (WithLp.fstL 2 ℂ H H) (G.starProjection_apply_eq_zero_iff.mpr ho)
  rw [HilbertPair.pair_eq_inl_add_inr] at hc' ho'
  simp only [map_add, map_smul, map_zero, neg_smul, map_neg, HilbertPair.snd_inl,
    HilbertPair.snd_inr, zero_add] at hc' ho'
  constructor
  · change graphBlock M xi z eps true false xi +
      (eps:ℂ) • graphBlock M xi z eps true true z = (eps:ℂ) • z at hc'
    rw [smul_sub]
    exact eq_sub_iff_add_eq.mpr hc'
  · change -((eps:ℂ) • graphBlock M xi z eps false false z) +
      graphBlock M xi z eps false true xi = 0 at ho'
    exact (eq_of_neg_add_eq_zero ho').symm

def graphApproximant (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) : H →L[ℂ] H :=
  ((2*eps:ℝ):ℂ)⁻¹ • (graphBlock M xi z eps true false + graphBlock M xi z eps false true)

lemma graphApproximant_mem (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    graphApproximant M xi z eps ∈ M.commutant :=
  M.commutant.toStarSubalgebra.smul_mem
    (add_mem (graphBlock_mem M xi z eps _ _) (graphBlock_mem M xi z eps _ _)) _

lemma graphApproximant_selfAdjoint (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    IsSelfAdjoint (graphApproximant M xi z eps) := by
  change star (graphApproximant M xi z eps) = _
  rw [graphApproximant, star_smul, star_add, graphBlock_star, graphBlock_star]
  simp only [map_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [add_comm]

lemma graphApproximant_xi (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) (heps : eps ≠ 0)
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi)) :
    graphApproximant M xi z eps xi = (1/2:ℂ) •
      (z-graphBlock M xi z eps true true z + graphBlock M xi z eps false false z) := by
  rcases graphBlock_offdiag_xi M xi z eps hz with ⟨h1,h2⟩
  simp only [graphApproximant, smul_apply, add_apply, h1,h2, ← smul_add, smul_smul]
  congr 1
  have he : (eps:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr heps
  push_cast
  field_simp

lemma real_commutation (M : VonNeumannAlgebra H) (xi z : H)
    (hcyc : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h})
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi)) :
    z ∈ closure {v : H | ∃ b : H →L[ℂ] H, b ∈ M.commutant ∧ IsSelfAdjoint b ∧ b xi = v} := by
  let eps (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have heps : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepne (n : ℕ) : eps n ≠ 0 := by dsimp [eps]; positivity
  have hf : Tendsto (fun n => graphBlock M xi z (eps n) false false z) atTop (𝓝 z) := by
    exact ((WithLp.fstL 2 ℂ H H).continuous.tendsto _).comp
      (orbitGraph_projection_inl_tendsto M xi z hcyc eps heps z)
  have hs : Tendsto (fun n => graphBlock M xi z (eps n) true true z) atTop (𝓝 0) := by
    convert ((WithLp.sndL 2 ℂ H H).continuous.tendsto _).comp
      (orbitGraph_projection_inr_tendsto M xi z hcyc hz eps heps z) using 1 <;>
      simp [graphBlock, Function.comp_def]
  have ht : Tendsto (fun n => graphApproximant M xi z (eps n) xi) atTop (𝓝 z) := by
    have hh : Tendsto (fun n => (1/2:ℂ) •
        (z-graphBlock M xi z (eps n) true true z + graphBlock M xi z (eps n) false false z))
        atTop (𝓝 ((1/2:ℂ) • (z-0+z))) :=
      ((tendsto_const_nhds.sub hs).add hf).const_smul (1/2:ℂ)
    have he : (1/2:ℂ) • (z-0+z) = z := by module
    simpa only [graphApproximant_xi M xi z _ (hepne _) hz, he] using hh
  exact mem_closure_of_tendsto ht (Filter.Eventually.of_forall (fun n =>
    ⟨graphApproximant M xi z (eps n), graphApproximant_mem _ _ _ _,
      graphApproximant_selfAdjoint _ _ _ _,rfl⟩))

end BoundedRecovery

end

end OAI


