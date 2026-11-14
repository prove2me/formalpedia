-- Prove2me | Definitions.Def_BuhaiPapers_Background_Sampling
-- name    : BuhaiPapers_Background_Sampling
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:45.79181+00:00
-- url     : https://prove2.me/theorems/7cf89f99-9e9f-488a-b220-d3e535e1b6da
-- title:
--   Background.Sampling — Sampling random graphs from coins
-- statement:
--   This is module `Background.Sampling`, shared background material of the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0), published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) uses it.
--
--   An algorithm with coins can add random edges to its input graph: reading its coin string in
--   chunks of `b` bits, one chunk per pair of vertices, it adds the pair when the number of the chunk
--   is below `j`. The added graph is `G(n, j/2^b)`, independent of the input; adding it to
--   `R ∼ G(n, p)` gives `G(n, p + r - p r)`, `r = j/2^b` (`Sampling.sum_mass_coins_sup`).
--
--   * `Sampling.sum_prod_mul_comp`: a sum over functions `x : I → X` of a product weight times a
--     function of `φ ∘ x` regroups as a sum over `ω : I → Bool` of products of fibre sums.
--   * `Sampling.sum_chunks`: the numbers of the first `N` chunks of `b` bits of a uniform string are
--     uniform on `Fin N → Fin 2^b`.
--   * `Sampling.pairsF`, `Sampling.pairEquiv`: the pairs `i < j` of `Fin n` in lexicographic order,
--     the order in which algorithms list them, and the bijection with `RandomGraph.Pair (Fin n)`.
--
--   **Contents.** The module is published as a whole: 31 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BuhaiPapers_Background_Sampling`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Background/Sampling.lean

module

public import Definitions.Def_BuhaiPapers_Background_RandomGraph
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.List.GetD

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `Background.Sampling` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Sampling random graphs from coins

An algorithm with coins can add random edges to its input graph: reading its coin string in
chunks of `b` bits, one chunk per pair of vertices, it adds the pair when the number of the chunk
is below `j`. The added graph is `G(n, j/2^b)`, independent of the input; adding it to
`R ∼ G(n, p)` gives `G(n, p + r - p r)`, `r = j/2^b` (`Sampling.sum_mass_coins_sup`).

* `Sampling.sum_prod_mul_comp`: a sum over functions `x : I → X` of a product weight times a
  function of `φ ∘ x` regroups as a sum over `ω : I → Bool` of products of fibre sums.
* `Sampling.sum_chunks`: the numbers of the first `N` chunks of `b` bits of a uniform string are
  uniform on `Fin N → Fin 2^b`.
* `Sampling.pairsF`, `Sampling.pairEquiv`: the pairs `i < j` of `Fin n` in lexicographic order,
  the order in which algorithms list them, and the bijection with `RandomGraph.Pair (Fin n)`.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory unitInterval SimpleGraph RandomGraph

namespace Sampling

/-! ### Regrouping sums of products -/

/-- **Regrouping.**
`∑_{x : ι → X} ∏ᵢ g(x i) · F(φ ∘ x) = ∑_{ω : ι → Bool} F ω ∏ᵢ ∑_{φ y = ω i} g y`. -/
theorem sum_prod_mul_comp {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (g : X → ℝ) (φ : X → Bool) (F : (ι → Bool) → ℝ) :
    ∑ x : ι → X, (∏ i, g (x i)) * F (fun i ↦ φ (x i)) =
      ∑ ω : ι → Bool, F ω * ∏ i, ∑ y ∈ univ.filter (fun y ↦ φ y = ω i), g y := by
  classical
  rw [← sum_fiberwise univ (fun x : ι → X ↦ fun i ↦ φ (x i))]
  refine sum_congr rfl fun ω _ ↦ ?_
  rw [prod_univ_sum, mul_sum]
  have hfib : (univ.filter fun x : ι → X ↦ (fun i ↦ φ (x i)) = ω) =
      Fintype.piFinset fun i ↦ univ.filter (fun y ↦ φ y = ω i) := by
    ext x
    simp [funext_iff]
  rw [hfib]
  refine sum_congr rfl fun x hx ↦ ?_
  have : (fun i ↦ φ (x i)) = ω := by
    ext i
    simpa using (Fintype.mem_piFinset.1 hx) i
  rw [this, mul_comm]

/-! ### Chunks of bits -/

/-- The number given by the `b` bits of `l` at positions `e b, …, e b + b - 1`. -/
def chunkVal (b : ℕ) (l : List Bool) (e : ℕ) : ℕ :=
  ∑ t ∈ range b, if l.getD (e * b + t) false then 2 ^ t else 0

/-- Bits as digits. -/
def toDigit (x : Bool) : Fin 2 := if x then 1 else 0

/-- The equivalence between bit strings of length `T ≥ N b` and the numbers of their first `N`
chunks together with the remaining bits. -/
def chunkEquiv {T N b : ℕ} (h : N * b ≤ T) :
    (Fin T → Bool) ≃ (Fin N → Fin (2 ^ b)) × (Fin (T - N * b) → Bool) :=
  ((Equiv.arrowCongr ((finSumFinEquiv (m := N * b) (n := T - N * b)).trans
      (finCongr (Nat.add_sub_cancel' h))).symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)).trans
  (Equiv.prodCongr
    (((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)).trans
      (Equiv.arrowCongr (Equiv.refl _)
        ((Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv)))
    (Equiv.refl _))

theorem toDigit_eq (x : Bool) : finTwoEquiv.symm x = toDigit x := by
  cases x <;> rfl

theorem chunkEquiv_fst {T N b : ℕ} (h : N * b ≤ T) (c : Fin T → Bool) (e : Fin N) :
    ((chunkEquiv h c).1 e : ℕ) = chunkVal b (List.ofFn c) e := by
  simp only [chunkEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.arrowCongr_apply, Equiv.refl_apply, Equiv.refl_symm, Function.comp_apply,
    Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.curry_apply, Function.curry_apply,
    Equiv.symm_symm, finFunctionFinEquiv_apply]
  rw [chunkVal, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun t _ ↦ ?_
  have hlt : (e : ℕ) * b + t < T := by
    have h1 : (e : ℕ) * b + t < N * b := by
      calc (e : ℕ) * b + t < (e : ℕ) * b + b := by omega
        _ = ((e : ℕ) + 1) * b := by ring
        _ ≤ N * b := Nat.mul_le_mul_right _ e.2
    omega
  have hget : (List.ofFn c).getD ((e : ℕ) * b + t) false = c ⟨(e : ℕ) * b + t, hlt⟩ := by
    rw [List.getD_eq_getElem (List.ofFn c) false (by simpa using hlt), List.getElem_ofFn]
  rw [hget]
  have hidx : (finCongr (Nat.add_sub_cancel' h)) (finSumFinEquiv (Sum.inl (finProdFinEquiv (e, t))))
      = ⟨(e : ℕ) * b + t, hlt⟩ := by
    ext
    simp [finProdFinEquiv]
    ring
  rw [hidx, toDigit_eq]
  unfold toDigit
  split_ifs <;> simp

/-- **Chunks are uniform**: summing a function of the numbers of the first `N` chunks of `b` bits
over all strings of length `T ≥ N b` is `2^(T - N b)` times the sum over `Fin N → Fin 2^b`. -/
theorem sum_chunks {T N b : ℕ} (h : N * b ≤ T) (F : (Fin N → ℕ) → ℝ) :
    ∑ c : Fin T → Bool, F (fun e ↦ chunkVal b (List.ofFn c) e) =
      2 ^ (T - N * b) * ∑ u : Fin N → Fin (2 ^ b), F (fun e ↦ u e) := by
  rw [← (chunkEquiv h).symm.sum_comp]
  have : ∀ x : (Fin N → Fin (2 ^ b)) × (Fin (T - N * b) → Bool),
      (fun e : Fin N ↦ chunkVal b (List.ofFn ((chunkEquiv h).symm x)) e) =
        fun e : Fin N ↦ (x.1 e : ℕ) := by
    intro x
    funext e
    rw [← chunkEquiv_fst h, Equiv.apply_symm_apply]
  simp_rw [this]
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  rw [mul_comm, ← mul_sum]

/-! ### The pairs of vertices, in order -/

/-- The pairs `i < j` of `Fin n`, in lexicographic order. -/
def pairsF (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i ↦ ((List.finRange n).filter fun j ↦ i < j).map fun j ↦ (i, j)

theorem mem_pairsF {n : ℕ} {e : Fin n × Fin n} : e ∈ pairsF n ↔ e.1 < e.2 := by
  simp only [pairsF, List.mem_flatMap, List.mem_finRange, List.mem_map, List.mem_filter,
    decide_eq_true_eq, true_and]
  constructor
  · rintro ⟨a, b, h, rfl⟩
    exact h
  · intro h
    exact ⟨e.1, e.2, h, rfl⟩

theorem nodup_pairsF (n : ℕ) : (pairsF n).Nodup := by
  unfold pairsF
  refine List.nodup_flatMap.2 ⟨fun i _ ↦ ?_, ?_⟩
  · exact ((List.nodup_finRange n).filter _).map fun a b h ↦ by simpa using h
  · refine (List.nodup_finRange n).pairwise_of_forall_ne fun i _ i' _ hii' ↦ ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_filter]
    rintro _ ⟨j, _, rfl⟩ ⟨j', _, h⟩
    exact hii' (congrArg Prod.fst h).symm

/-- The pair of an ordered pair `i < j`. -/
def toPair {n : ℕ} (e : Fin n × Fin n) (h : e.1 < e.2) : Pair (Fin n) :=
  ⟨s(e.1, e.2), by simpa using h.ne⟩

/-- The `i`-th pair of `pairsF n`. -/
def pairAt (n : ℕ) (i : Fin (pairsF n).length) : Pair (Fin n) :=
  toPair (pairsF n)[i] (mem_pairsF.1 (List.getElem_mem _))

theorem pairAt_bijective (n : ℕ) : Function.Bijective (pairAt n) := by
  constructor
  · intro i i' h
    simp only [pairAt, toPair, Subtype.mk.injEq, Sym2.eq_iff, Fin.getElem_fin] at h
    have hi := mem_pairsF.1 (List.getElem_mem (l := pairsF n) i.2)
    have hi' := mem_pairsF.1 (List.getElem_mem (l := pairsF n) i'.2)
    have heq : (pairsF n)[(i : ℕ)] = (pairsF n)[(i' : ℕ)] := by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        rw [Fin.lt_def] at hi hi'
        rw [Fin.ext_iff] at h1 h2
        omega
    exact Fin.ext ((nodup_pairsF n).getElem_inj_iff.1 heq)
  · rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa using hz
      rcases lt_or_gt_of_ne huv with h | h
      · obtain ⟨i, hi, he⟩ := List.getElem_of_mem (mem_pairsF.2 (show (u, v).1 < (u, v).2 from h))
        refine ⟨⟨i, hi⟩, ?_⟩
        simp only [pairAt, toPair, Fin.getElem_fin, he]
      · obtain ⟨i, hi, he⟩ := List.getElem_of_mem (mem_pairsF.2 (show (v, u).1 < (v, u).2 from h))
        refine ⟨⟨i, hi⟩, ?_⟩
        simp only [pairAt, toPair, Subtype.mk.injEq, Fin.getElem_fin, he]
        exact Sym2.eq_swap

/-- The pairs of `Fin n` numbered by their position in `pairsF n`. -/
noncomputable def pairEquiv (n : ℕ) : Fin (pairsF n).length ≃ Pair (Fin n) :=
  Equiv.ofBijective _ (pairAt_bijective n)

theorem length_pairsF (n : ℕ) : (pairsF n).length = n.choose 2 := by
  have := Fintype.card_congr (pairEquiv n)
  rw [Fintype.card_fin] at this
  rw [this, Sym2.card_subtype_not_diag, Fintype.card_fin]

/-! ### Graphs as functions on the pairs -/

variable {V : Type*}

/-- The graph whose edges are the pairs `e` with `ω e`. -/
def graphB (ω : Pair V → Bool) : SimpleGraph V := graphOf fun e ↦ ω e = true

open Classical in
/-- The edges of a graph, as a function on the pairs. -/
noncomputable def edgeB (R : SimpleGraph V) : Pair V → Bool := fun e ↦ decide (e.1 ∈ R.edgeSet)

theorem graphB_edgeB (R : SimpleGraph V) : graphB (edgeB R) = R := by
  ext u v
  simp only [graphB, edgeB, graphOf_adj, decide_eq_true_eq, mem_edgeSet]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨R.ne_of_adj h, h⟩⟩

theorem edgeB_graphB (ω : Pair V → Bool) : edgeB (graphB ω) = ω := by
  classical
  funext e
  apply Bool.eq_iff_iff.2
  rw [edgeB, decide_eq_true_iff]
  obtain ⟨z, hz⟩ := e
  induction z using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := by simpa using hz
    simp only [graphB, mem_edgeSet, graphOf_adj]
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨huv, h⟩⟩

/-- Graphs are functions on the pairs. -/
noncomputable def graphEquiv : SimpleGraph V ≃ (Pair V → Bool) :=
  ⟨edgeB, graphB, graphB_edgeB, edgeB_graphB⟩

theorem graphB_bijective : Function.Bijective (graphB : (Pair V → Bool) → SimpleGraph V) :=
  graphEquiv.symm.bijective

/-- Sums over graphs are sums over the functions on the pairs. -/
theorem sum_graph_eq [Fintype V] [DecidableEq V] {M : Type*} [AddCommMonoid M]
    (g : SimpleGraph V → M) : ∑ R, g R = ∑ ω : Pair V → Bool, g (graphB ω) :=
  (Fintype.sum_bijective graphB graphB_bijective _ g fun _ ↦ rfl).symm

theorem graphB_sup (ω ω' : Pair V → Bool) :
    graphB ω ⊔ graphB ω' = graphB fun e ↦ ω e || ω' e := by
  ext u v
  simp only [graphB, sup_adj, graphOf_adj, Bool.or_eq_true]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact ⟨h, Or.inl h'⟩
    · exact ⟨h, Or.inr h'⟩
  · rintro ⟨h, h' | h'⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩

theorem card_edgeFinset_graphB {n : ℕ} (ω : Pair (Fin n) → Bool) [Fintype (graphB ω).edgeSet] :
    (graphB ω).edgeFinset.card = (univ.filter fun e ↦ ω e = true).card := by
  classical
  rw [← (univ.filter fun e ↦ ω e = true).card_map (Function.Embedding.subtype _)]
  congr 1
  ext z
  simp only [mem_edgeFinset, mem_map, mem_filter, mem_univ, true_and,
    Function.Embedding.coe_subtype]
  induction z using Sym2.ind with
  | _ u v =>
    simp only [graphB, mem_edgeSet, graphOf_adj]
    constructor
    · rintro ⟨huv, h⟩
      exact ⟨⟨s(u, v), by simpa using huv⟩, h, rfl⟩
    · rintro ⟨⟨z, hz⟩, h, rfl⟩
      have huv : u ≠ v := by simpa using hz
      exact ⟨huv, h⟩

open Classical in
/-- **The mass of a graph** under `G(Fin n, p)` is the product over the pairs. -/
theorem binomialRandom_real_graphB {n : ℕ} (p : I) (ω : Pair (Fin n) → Bool) :
    (G(Fin n, p)).real {graphB ω} = ∏ e, if ω e = true then (p : ℝ) else 1 - p := by
  rw [binomialRandom_real_singleton, prod_ite, prod_const, prod_const, card_edgeFinset_graphB]
  congr 2
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Pair (Fin n))))
    fun e ↦ ω e = true
  rw [card_univ, Sym2.card_subtype_not_diag, Fintype.card_fin] at h
  omega

/-! ### Adding random edges from coins -/

/-- The graph of the pairs whose chunk of `b` bits of `l` has a number below `j`; the `e`-th pair
of `pairsF n` gets the `e`-th chunk. -/
noncomputable def chunkGraph (n b j : ℕ) (l : List Bool) : SimpleGraph (Fin n) :=
  graphB fun z ↦ decide (chunkVal b l ((pairEquiv n).symm z) < j)

/-- `p + r - p r`, the edge probability of the union of independent `G(n, p)` and `G(n, r)`. -/
noncomputable def supProb (p r : I) : I :=
  ⟨p + r - p * r, by
    constructor
    · nlinarith [p.2.1, p.2.2, r.2.1, r.2.2]
    · nlinarith [p.2.1, p.2.2, r.2.1, r.2.2]⟩

/-- The probability `j / 2^b`, for `j ≤ 2^b`. -/
noncomputable def dyadic (b j : ℕ) (hj : j ≤ 2 ^ b) : I :=
  ⟨j / 2 ^ b, div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_le_one (by positivity)).2 (by exact_mod_cast hj)⟩

/-- Probabilities under `G(Fin n, p)` as sums over the functions on the pairs. -/
theorem real_setOf_eq_sum {n : ℕ} (p : I) (P : SimpleGraph (Fin n) → Prop) [DecidablePred P] :
    (G(Fin n, p)).real {R | P R} =
      ∑ ω : Pair (Fin n) → Bool, (if P (graphB ω) then 1 else 0) *
        ∏ e, if ω e = true then (p : ℝ) else 1 - p := by
  have hset : ({R | P R} : Set (SimpleGraph (Fin n))) =
      ((univ.filter P : Finset (SimpleGraph (Fin n))) : Set (SimpleGraph (Fin n))) := by
    ext
    simp
  rw [hset, ← sum_measureReal_singleton, sum_filter, sum_graph_eq]
  refine sum_congr rfl fun ω _ ↦ ?_
  rw [binomialRandom_real_graphB]
  split_ifs <;> simp

/-- The coins, for a fixed graph `R = graphB ω₁`: the chunks become numbers on the pairs. -/
theorem sum_coins_sup {n b j T : ℕ} (hT : (pairsF n).length * b ≤ T)
    (P : SimpleGraph (Fin n) → Prop) [DecidablePred P] (ω₁ : Pair (Fin n) → Bool) :
    ∑ c : Fin T → Bool, (if P (graphB ω₁ ⊔ chunkGraph n b j (List.ofFn c)) then (1 : ℝ) else 0)
      = 2 ^ (T - (pairsF n).length * b) * ∑ u : Pair (Fin n) → Fin (2 ^ b),
          if P (graphB fun e ↦ ω₁ e || decide ((u e : ℕ) < j)) then 1 else 0 := by
  have := sum_chunks hT (F := fun v : Fin (pairsF n).length → ℕ ↦
    if P (graphB ω₁ ⊔ graphB fun z ↦ decide (v ((pairEquiv n).symm z) < j)) then (1 : ℝ) else 0)
  refine (Eq.trans rfl this).trans ?_
  rw [← (Equiv.arrowCongr (pairEquiv n) (Equiv.refl _)).sum_comp]
  congr 1
  refine sum_congr rfl fun u _ ↦ ?_
  rw [graphB_sup]
  rfl

/-- **Adding random edges from coins.** Let `R ∼ G(n, p)` and add the pairs whose chunks of a
uniform string of `T ≥ C(n, 2) b` bits are below `j ≤ 2^b`: the result is `G(n, p + r - p r)`
with `r = j / 2^b`. -/
theorem sum_mass_coins_sup {n b j T : ℕ} (hT : n.choose 2 * b ≤ T) (hj : j ≤ 2 ^ b) (p : I)
    (P : SimpleGraph (Fin n) → Prop) [DecidablePred P] :
    ∑ R : SimpleGraph (Fin n), (G(Fin n, p)).real {R} *
      (((univ.filter fun c : Fin T → Bool ↦ P (R ⊔ chunkGraph n b j (List.ofFn c))).card : ℝ) /
        2 ^ T) = (G(Fin n, supProb p (dyadic b j hj))).real {R | P R} := by
  classical
  have hNc : (pairsF n).length = n.choose 2 := length_pairsF n
  have hT' : (pairsF n).length * b ≤ T := by rw [hNc]; exact hT
  simp_rw [card_filter]
  rw [real_setOf_eq_sum, sum_graph_eq]
  simp_rw [binomialRandom_real_graphB]
  push_cast
  simp_rw [sum_coins_sup hT' P]
  -- One sum over the pairs of (edge, chunk) choices.
  have h2 : (2 : ℝ) ^ T = 2 ^ (T - (pairsF n).length * b) * ∏ _e : Pair (Fin n), (2 : ℝ) ^ b := by
    rw [prod_const, card_univ, Sym2.card_subtype_not_diag, Fintype.card_fin, ← hNc,
      ← pow_mul, ← pow_add, mul_comm b, Nat.sub_add_cancel hT']
  set g : Bool × Fin (2 ^ b) → ℝ := fun y ↦ (if y.1 = true then (p : ℝ) else 1 - p) / 2 ^ b
    with hg
  set φ : Bool × Fin (2 ^ b) → Bool := fun y ↦ y.1 || decide ((y.2 : ℕ) < j) with hφ
  have hsum : ∑ ω₁ : Pair (Fin n) → Bool, (∏ e, if ω₁ e = true then (p : ℝ) else 1 - p) *
      ((2 ^ (T - (pairsF n).length * b) * ∑ u : Pair (Fin n) → Fin (2 ^ b),
        if P (graphB fun e ↦ ω₁ e || decide ((u e : ℕ) < j)) then (1 : ℝ) else 0) / 2 ^ T) =
      ∑ x : Pair (Fin n) → Bool × Fin (2 ^ b), (∏ e, g (x e)) *
        (if P (graphB fun e ↦ φ (x e)) then 1 else 0) := by
    rw [← (Equiv.arrowProdEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type, h2]
    refine sum_congr rfl fun ω₁ _ ↦ ?_
    rw [mul_div_mul_left _ _ (by positivity), sum_div, mul_sum]
    refine sum_congr rfl fun u _ ↦ ?_
    simp only [hg, hφ, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, prod_div_distrib]
    ring
  rw [hsum, sum_prod_mul_comp g φ (fun ω ↦ if P (graphB ω) then 1 else 0)]
  refine sum_congr rfl fun ω _ ↦ ?_
  congr 1
  refine prod_congr rfl fun e _ ↦ ?_
  -- The fibre sums: `p + (1 - p) j / 2^b` for an edge, `(1 - p)(1 - j / 2^b)` otherwise.
  have hlt : ((univ.filter fun t : Fin (2 ^ b) ↦ (t : ℕ) < j).card : ℝ) = j := by
    have : (univ.filter fun t : Fin (2 ^ b) ↦ (t : ℕ) < j).card = j := by
      rw [Fin.card_filter_val_lt]
      exact min_eq_right hj
    exact_mod_cast this
  have hge : ((univ.filter fun t : Fin (2 ^ b) ↦ ¬ (t : ℕ) < j).card : ℝ) = 2 ^ b - j := by
    rw [Finset.filter_not, card_univ_sdiff, Fintype.card_fin, Fin.card_filter_val_lt,
      min_eq_right hj, Nat.cast_sub hj]
    push_cast
    ring
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hsup : ((supProb p (dyadic b j hj) : I) : ℝ) = p + j / 2 ^ b - p * (j / 2 ^ b) := rfl
  rw [sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, hsup]
  simp only [hg, hφ, Bool.true_or, Bool.false_or, ite_true, Bool.false_eq_true, ite_false]
  cases ω e
  · simp only [Bool.true_eq_false, ite_false, sum_const_zero, zero_add, Bool.false_eq_true,
      decide_eq_false_iff_not]
    rw [← sum_filter, sum_const, nsmul_eq_mul, hge]
    field_simp
    ring
  · simp only [ite_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, decide_eq_true_eq]
    rw [← sum_filter, sum_const, nsmul_eq_mul, hlt]
    push_cast
    field_simp
    ring

end Sampling


