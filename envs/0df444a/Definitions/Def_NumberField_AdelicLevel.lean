-- Prove2me | Definitions.Def_NumberField_AdelicLevel
-- name    : NumberField_AdelicLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/1101a7ec-abac-5291-a359-616abcd4fba3
-- title:
--   Adelic GL(2) level subgroups, component maps and Hecke elements
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $K$. For an ideal $N \subseteq R$ and a height-one prime $v$, `idealBound R N v` is the element of $\mathbb{Z}^{m0} =$ `WithZero (Multiplicative ℤ)` equal to $0$ if $N = \bot$ and to $\exp(-\operatorname{ord}_v N)$ otherwise, $\operatorname{ord}_v N$ being the multiplicity of $v$ in the factorisation of $N$; it is $\le 1$, equals $1$ exactly off the (finitely many) primes dividing $N$, and is $1$ for $N = \top$. Inside the finite adele ring (Mathlib's restricted product over height-one primes with respect to the $\mathcal{O}_v$), `integralFiniteAdeles` is the set of $x$ with $x_v \in \mathcal{O}_v$ for all $v$, and `idealBall R K N` the set of $x$ with $v(x_v) \le$ `idealBound R N v` for all $v$ (for $N \ne \bot$ this is $\prod_v N\mathcal{O}_v$; for $N = \bot$ it is $\{0\}$). The structures `IsLevelZeroMatrix`/`IsLevelOneMatrix` are predicates on a $2\times 2$ matrix over the finite adeles: all entries integral and the $(1,0)$ entry in the $N$-ball, plus, for level one, the $(1,1)$ entry congruent to $1$ modulo the $N$-ball. The subgroups `finiteLevelZero R K N`, `finiteLevelOne R K N` of $\mathrm{GL}_2(\mathbb{A}_K^f)$ are defined by imposing the corresponding predicate on $g$ and on $g^{-1}$ simultaneously (so inversion-closure is a symmetry of the definition); `finiteIntegralGL2 R K` abbreviates `finiteLevelZero R K ⊤`, and `mem_finiteIntegralGL2_iff` identifies it with integrality of $g$ and $g^{-1}$. Their preimages under the finite-part projection give `levelZero`, `levelOne` in $\mathrm{GL}_2(\mathbb{A}_K)$, with no condition at the infinite places. Accompanying lemmas prove these sets closed, open when $N \ne \bot$, and compact when $R$ is a finite free $\mathbb{Z}$-module, with `levelOne` $\le$ `levelZero`. The module also supplies the component-reading ring homomorphisms `adeleArch`, `adeleFin`, `archEval`, `finAdeleEval` and their $\mathrm{GL}_2$ analogues `glArch`, `glFin`, `archComponent`, `finComponent`, each with a definitional `_apply` lemma and a continuity statement; and Hecke elements: `localUnit` places a unit of $K_v$ at the single coordinate $v$, `diagOne` sends a unit $a$ to $\mathrm{diag}(a,1)$, and `heckeGenAt R K v t` is the resulting element of $\mathrm{GL}_2(\mathbb{A}_K)$, trivial at all other places. A chosen uniformizer `uniformizer v` $\in R$ (with `intValuation` $=\exp(-1)$, via choice) yields `uniformizerUnit` and `heckeGen`; `heckeGenAt_inv_mul_heckeGenAt_mem_levelOne` shows that equal valuations of $t,t'$ force $h_v(t)^{-1}h_v(t') \in$ `levelOne R K N` for every $N$, so the relevant cosets are independent of the choice.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring $\mathbb{A}_K = \mathbb{A}_{K,\infty} \times \mathbb{A}_K^f$, the finite adeles as a restricted product, the local completions `adicCompletion` with their valuation subrings `adicCompletionIntegers`, and `Matrix.GeneralLinearGroup.map`; the valuation bound attached to an ideal, the level predicates and the level subgroups of adelic $\mathrm{GL}_2$, the component homomorphisms as bundled ring/group maps, and the Hecke elements are the project's own definitions built on those.
--
--   **Where it is used.** These open compact subgroups are the level structures at which the project's adelic automorphic forms for $\mathrm{GL}_2$ are defined, `levelOne` being the one needed to accommodate a nontrivial nebentypus; the Hecke elements and the coset-independence statement are what the Hecke action at a finite place is built from. The construction is applied with $R = \mathbb{Z}$ and with rings of integers of number fields, where the compactness hypotheses hold.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_AdelicLevel.lean

import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct
open scoped Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

open scoped Classical in

def idealBound (N : Ideal R) (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ) :=
  if N = ⊥ then 0
  else WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ))

section IdealBound

variable {R}

theorem idealBound_bot (v : HeightOneSpectrum R) : idealBound R ⊥ v = 0 := if_pos rfl

theorem idealBound_of_ne_bot {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v
      = WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ)) := by
  classical
  exact if_neg hN

theorem idealBound_ne_zero {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v ≠ 0 := by
  rw [idealBound_of_ne_bot hN]; exact WithZero.exp_ne_zero

theorem idealBound_le_one (N : Ideal R) (v : HeightOneSpectrum R) : idealBound R N v ≤ 1 := by
  by_cases hN : N = ⊥
  · rw [hN, idealBound_bot]; exact zero_le'
  · rw [idealBound_of_ne_bot hN, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

theorem idealBound_eq_one_of_not_dvd {N : Ideal R} (hN : N ≠ ⊥) {v : HeightOneSpectrum R}
    (hv : ¬ v.asIdeal ∣ N) : idealBound R N v = 1 := by
  classical
  rw [idealBound_of_ne_bot hN]
  have h0 : (Associates.mk v.asIdeal).count (Associates.mk N).factors = 0 := by
    by_contra h
    exact hv ((Associates.count_ne_zero_iff_dvd (show N ≠ 0 from hN) v.irreducible).mp h)
  rw [h0]; simp

theorem idealBound_top (v : HeightOneSpectrum R) : idealBound R (⊤ : Ideal R) v = 1 :=
  idealBound_eq_one_of_not_dvd top_ne_bot fun h =>
    v.isPrime.ne_top ((Ideal.dvd_iff_le.mp h).antisymm le_top |>.symm ▸ rfl)

theorem finite_setOf_idealBound_ne_one {N : Ideal R} (hN : N ≠ ⊥) :
    {v : HeightOneSpectrum R | idealBound R N v ≠ 1}.Finite :=
  (Ideal.finite_factors hN).subset fun _ hv => by
    by_contra h
    exact hv (idealBound_eq_one_of_not_dvd hN h)

end IdealBound

section Local

variable {R K} (v : HeightOneSpectrum R)

theorem algebraMap_mem_adicCompletionIntegers (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

theorem valued_algebraMap (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

theorem setOf_valued_le_eq_preimage (t : v.adicCompletion K) (ht : t ≠ 0) :
    {y : v.adicCompletion K | Valued.v y ≤ Valued.v t}
      = (fun y => y * t⁻¹) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
  rw [mul_inv_le_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ht)), one_mul]

theorem isOpen_setOf_valued_le (t : v.adicCompletion K) (ht : t ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} := by
  rw [setOf_valued_le_eq_preimage v t ht]
  exact (continuous_id.mul continuous_const).isOpen_preimage _ (Valued.isOpen_valuationSubring _)

theorem isClosed_adicCompletionIntegers :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isClosed_valuationSubring _

theorem isClosed_setOf_valued_le (t : v.adicCompletion K) (ht : t ≠ 0) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} := by
  rw [setOf_valued_le_eq_preimage v t ht]
  exact (isClosed_adicCompletionIntegers v).preimage (continuous_id.mul continuous_const)

theorem exists_valued_eq_exp_neg (n : ℕ) :
    ∃ t : v.adicCompletion K, t ≠ 0 ∧ Valued.v t = WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  refine ⟨(algebraMap K (v.adicCompletion K) (algebraMap R K π)) ^ n, ?_, ?_⟩
  · refine pow_ne_zero _ fun h => ?_
    have := valued_algebraMap (K := K) v π
    rw [h, map_zero, hπ] at this
    exact WithZero.exp_ne_zero this.symm
  · rw [map_pow, valued_algebraMap, hπ]
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

theorem isOpen_setOf_valued_le_idealBound {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := K) v
    ((Associates.mk v.asIdeal).count (Associates.mk N).factors)
  rw [idealBound_of_ne_bot hN, ← hvt]
  exact isOpen_setOf_valued_le v t ht

theorem isClosed_setOf_valued_le_idealBound (N : Ideal R) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} := by
  by_cases hN : N = ⊥
  · have : {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} = {0} := by
      ext y; simp [hN, idealBound_bot]
    rw [this]; exact isClosed_singleton
  · obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := K) v
      ((Associates.mk v.asIdeal).count (Associates.mk N).factors)
    rw [idealBound_of_ne_bot hN, ← hvt]
    exact isClosed_setOf_valued_le v t ht

end Local

section Projections

def archEval (w : InfinitePlace K) : InfiniteAdeleRing K →+* w.Completion where
  toFun a := a w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def finAdeleEval (v : HeightOneSpectrum R) : FiniteAdeleRing R K →+* v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def adeleArch : AdeleRing R K →+* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def adeleFin : AdeleRing R K →+* FiniteAdeleRing R K where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem archEval_apply (w : InfinitePlace K) (a : InfiniteAdeleRing K) : archEval K w a = a w := rfl
theorem finAdeleEval_apply (v : HeightOneSpectrum R) (a : FiniteAdeleRing R K) :
    finAdeleEval R K v a = a v := rfl
theorem adeleArch_apply (a : AdeleRing R K) : adeleArch R K a = a.1 := rfl
theorem adeleFin_apply (a : AdeleRing R K) : adeleFin R K a = a.2 := rfl

theorem continuous_archEval (w : InfinitePlace K) : Continuous (archEval K w) :=
  (continuous_apply w : Continuous fun a : (∀ w : InfinitePlace K, w.Completion) => a w)

theorem continuous_finAdeleEval (v : HeightOneSpectrum R) : Continuous (finAdeleEval R K v) :=
  (RestrictedProduct.continuous_eval v :
    Continuous fun x : Πʳ w : HeightOneSpectrum R, [w.adicCompletion K, w.adicCompletionIntegers K] => x v)

theorem continuous_adeleArch : Continuous (adeleArch R K) :=
  (continuous_fst : Continuous fun x : AdeleRing R K => x.1)

theorem continuous_adeleFin : Continuous (adeleFin R K) :=
  (continuous_snd : Continuous fun x : AdeleRing R K => x.2)

def archComponent (w : InfinitePlace K) : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (archEval K w)

def finComponent (v : HeightOneSpectrum R) :
    GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (finAdeleEval R K v)

def glArch : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (adeleArch R K)

def glFin : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.GeneralLinearGroup.map (adeleFin R K)

theorem archComponent_apply (w : InfinitePlace K) (g : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    (archComponent K w g : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w := rfl
theorem finComponent_apply (v : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K))
    (i j : Fin 2) : (finComponent R K v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v := rfl
theorem glArch_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glArch R K g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1 := rfl
theorem glFin_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glFin R K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 := rfl

private theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

theorem continuous_archComponent (w : InfinitePlace K) : Continuous (archComponent K w) :=
  continuous_glMap _ (continuous_archEval K w)
theorem continuous_finComponent (v : HeightOneSpectrum R) : Continuous (finComponent R K v) :=
  continuous_glMap _ (continuous_finAdeleEval R K v)
theorem continuous_glArch : Continuous (glArch R K) := continuous_glMap _ (continuous_adeleArch R K)
theorem continuous_glFin : Continuous (glFin R K) := continuous_glMap _ (continuous_adeleFin R K)

end Projections

section FiniteAdelic

def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, x v ∈ v.adicCompletionIntegers K}

def idealBall (N : Ideal R) : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, Valued.v (x v) ≤ idealBound R N v}

variable {R K}

section Coe
variable (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R)
theorem coe_zero_apply : (0 : FiniteAdeleRing R K) v = 0 := rfl
theorem coe_one_apply : (1 : FiniteAdeleRing R K) v = 1 := rfl
theorem coe_add_apply : (x + y) v = x v + y v := rfl
theorem coe_mul_apply : (x * y) v = x v * y v := rfl
theorem coe_sub_apply : (x - y) v = x v - y v := rfl
theorem coe_neg_apply : (-x) v = -x v := rfl
end Coe

theorem idealBall_subset_integralFiniteAdeles (N : Ideal R) :
    idealBall R K N ⊆ integralFiniteAdeles R K := fun _ hx v =>
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ((hx v).trans (idealBound_le_one N v))

theorem zero_mem_idealBall (N : Ideal R) : (0 : FiniteAdeleRing R K) ∈ idealBall R K N :=
  fun v => by rw [coe_zero_apply, map_zero]; exact zero_le'

variable (R K)

theorem isOpen_integralFiniteAdeles : IsOpen (integralFiniteAdeles R K) :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out

theorem isClosed_integralFiniteAdeles : IsClosed (integralFiniteAdeles R K) := by
  have : integralFiniteAdeles R K = ⋂ v : HeightOneSpectrum R,
      (fun x : FiniteAdeleRing R K => x v) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x; simp [integralFiniteAdeles]
  rw [this]
  exact isClosed_iInter fun v => (isClosed_adicCompletionIntegers v).preimage (continuous_finAdeleEval R K v)

theorem isClosed_idealBall (N : Ideal R) : IsClosed (idealBall R K N) := by
  have : idealBall R K N = ⋂ v : HeightOneSpectrum R,
      (fun x : FiniteAdeleRing R K => x v) ⁻¹' {y | Valued.v y ≤ idealBound R N v} := by
    ext x; simp [idealBall]
  rw [this]
  exact isClosed_iInter fun v =>
    (isClosed_setOf_valued_le_idealBound v N).preimage (continuous_finAdeleEval R K v)

theorem isOpen_idealBall {N : Ideal R} (hN : N ≠ ⊥) : IsOpen (idealBall R K N) := by
  have hfin := finite_setOf_idealBound_ne_one hN
  have : idealBall R K N = integralFiniteAdeles R K ∩
      ⋂ v ∈ {v : HeightOneSpectrum R | idealBound R N v ≠ 1},
        (fun x : FiniteAdeleRing R K => x v) ⁻¹' {y | Valued.v y ≤ idealBound R N v} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    refine ⟨fun hx => ⟨idealBall_subset_integralFiniteAdeles N hx, fun v _ => hx v⟩,
      fun ⟨hint, hT⟩ v => ?_⟩
    by_cases hv : idealBound R N v = 1
    · rw [hv]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hint v)
    · exact hT v hv
  rw [this]
  exact (isOpen_integralFiniteAdeles R K).inter (hfin.isOpen_biInter fun v _ =>
    (isOpen_setOf_valued_le_idealBound v hN).preimage (continuous_finAdeleEval R K v))

variable [Module.Free ℤ R] [Module.Finite ℤ R]

theorem isCompact_integralFiniteAdeles : IsCompact (integralFiniteAdeles R K) := by
  haveI : ∀ v : HeightOneSpectrum R,
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end FiniteAdelic

section FiniteLevel

structure IsLevelZeroMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop where
  integral : ∀ i j, m i j ∈ integralFiniteAdeles R K
  lowerLeft : m 1 0 ∈ idealBall R K N

structure IsLevelOneMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop extends IsLevelZeroMatrix R K N m where
  lowerRight : m 1 1 - 1 ∈ idealBall R K N

variable {R K}
variable {N : Ideal R}

theorem one_mem_integralFiniteAdeles : (1 : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K :=
  fun _ => one_mem _

theorem zero_mem_integralFiniteAdeles : (0 : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K :=
  fun _ => zero_mem _

theorem add_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x + y ∈ integralFiniteAdeles R K :=
  fun v => add_mem (hx v) (hy v)

theorem mul_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x * y ∈ integralFiniteAdeles R K :=
  fun v => mul_mem (hx v) (hy v)

theorem sub_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ integralFiniteAdeles R K) : x - y ∈ integralFiniteAdeles R K :=
  fun v => sub_mem (hx v) (hy v)

theorem valued_apply_le_one {x : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (v : HeightOneSpectrum R) : Valued.v (x v) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx v)

theorem add_mem_idealBall {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ idealBall R K N) : x + y ∈ idealBall R K N := fun v =>
  (Valuation.map_add _ _ _).trans (max_le (hx v) (hy v))

theorem mul_mem_idealBall_left {x y : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
    (hy : y ∈ idealBall R K N) : x * y ∈ idealBall R K N := fun v => by
  rw [coe_mul_apply, map_mul]
  calc Valued.v (x v) * Valued.v (y v) ≤ 1 * idealBound R N v :=
        mul_le_mul' (valued_apply_le_one hx v) (hy v)
    _ = idealBound R N v := one_mul _

theorem mul_mem_idealBall_right {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ integralFiniteAdeles R K) : x * y ∈ idealBall R K N := by
  rw [mul_comm]; exact mul_mem_idealBall_left hy hx

namespace IsLevelZeroMatrix

protected theorem one : IsLevelZeroMatrix R K N 1 where
  integral i j := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [Matrix.one_apply_ne (by decide)]
    exact zero_mem_idealBall N

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

protected theorem mul (hm : IsLevelZeroMatrix R K N m) (hm' : IsLevelZeroMatrix R K N m') :
    IsLevelZeroMatrix R K N (m * m') where
  integral i j := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_integralFiniteAdeles
      (mul_mem_integralFiniteAdeles (hm.integral i 0) (hm'.integral 0 j))
      (mul_mem_integralFiniteAdeles (hm.integral i 1) (hm'.integral 1 j))
  lowerLeft := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_idealBall (mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 0))
      (mul_mem_idealBall_left (hm.integral 1 1) hm'.lowerLeft)

end IsLevelZeroMatrix

namespace IsLevelOneMatrix

protected theorem one : IsLevelOneMatrix R K N 1 where
  toIsLevelZeroMatrix := .one
  lowerRight := by
    rw [Matrix.one_apply_eq, sub_self]
    exact zero_mem_idealBall N

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

protected theorem mul (hm : IsLevelOneMatrix R K N m) (hm' : IsLevelOneMatrix R K N m') :
    IsLevelOneMatrix R K N (m * m') where
  toIsLevelZeroMatrix := hm.toIsLevelZeroMatrix.mul hm'.toIsLevelZeroMatrix
  lowerRight := by
    have h : (m * m') 1 1 - 1
        = m 1 0 * m' 0 1 + ((m 1 1 - 1) * m' 1 1 + (m' 1 1 - 1)) := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h]
    exact add_mem_idealBall (mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 1))
      (add_mem_idealBall (mul_mem_idealBall_right hm.lowerRight (hm'.integral 1 1)) hm'.lowerRight)

end IsLevelOneMatrix

variable (R K) (N)

def finiteLevelZero : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelZeroMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelZeroMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by rw [mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

def finiteLevelOne : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelOneMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by rw [mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {R K N}

theorem mem_finiteLevelZero_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteLevelZero R K N ↔ IsLevelZeroMatrix R K N (g : Matrix _ _ _) ∧
      IsLevelZeroMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) :=
  Iff.rfl

theorem mem_finiteLevelOne_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteLevelOne R K N ↔ IsLevelOneMatrix R K N (g : Matrix _ _ _) ∧
      IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) :=
  Iff.rfl

variable (R K N)

theorem finiteLevelOne_le_finiteLevelZero : finiteLevelOne R K N ≤ finiteLevelZero R K N :=
  fun _ hg => ⟨hg.1.toIsLevelZeroMatrix, hg.2.toIsLevelZeroMatrix⟩

abbrev finiteIntegralGL2 : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) := finiteLevelZero R K ⊤

variable {R K} in
theorem mem_finiteIntegralGL2_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteIntegralGL2 R K ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
        i j ∈ integralFiniteAdeles R K :=
  ⟨fun h => ⟨h.1.integral, h.2.integral⟩, fun h =>
    ⟨⟨h.1, fun v => (idealBound_top v).symm ▸ valued_apply_le_one (h.1 1 0) v⟩,
     ⟨h.2, fun v => (idealBound_top v).symm ▸ valued_apply_le_one (h.2 1 0) v⟩⟩⟩

theorem isClosed_setOf_isLevelZeroMatrix :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m}
      = (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' integralFiniteAdeles R K)
        ∩ (fun m => m 1 0) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h => ⟨h.integral, h.lowerLeft⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isClosed_iInter fun i => isClosed_iInter fun j =>
      (isClosed_integralFiniteAdeles R K).preimage (continuous_id.matrix_elem i j)).inter
    ((isClosed_idealBall R K N).preimage (continuous_id.matrix_elem 1 0))

theorem isClosed_setOf_isLevelOneMatrix :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m}
      = {m | IsLevelZeroMatrix R K N m} ∩ (fun m => m 1 1 - 1) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h => ⟨h.toIsLevelZeroMatrix, h.lowerRight⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isClosed_setOf_isLevelZeroMatrix R K N).inter
    ((isClosed_idealBall R K N).preimage ((continuous_id.matrix_elem 1 1).sub continuous_const))

variable {N} in
theorem isOpen_setOf_isLevelZeroMatrix (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelZeroMatrix R K N m}
      = (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' integralFiniteAdeles R K)
        ∩ (fun m => m 1 0) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h => ⟨h.integral, h.lowerLeft⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_integralFiniteAdeles R K).preimage (continuous_id.matrix_elem i j)).inter
    ((isOpen_idealBall R K hN).preimage (continuous_id.matrix_elem 1 0))

variable {N} in
theorem isOpen_setOf_isLevelOneMatrix (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m} := by
  have : {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) | IsLevelOneMatrix R K N m}
      = {m | IsLevelZeroMatrix R K N m} ∩ (fun m => m 1 1 - 1) ⁻¹' idealBall R K N := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h => ⟨h.toIsLevelZeroMatrix, h.lowerRight⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isOpen_setOf_isLevelZeroMatrix R K hN).inter
    ((isOpen_idealBall R K hN).preimage ((continuous_id.matrix_elem 1 1).sub continuous_const))

variable {N} in

theorem isOpen_finiteLevelZero (hN : N ≠ ⊥) :
    IsOpen (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isOpen_setOf_isLevelZeroMatrix R K hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLevelZeroMatrix R K hN).preimage Units.continuous_coe_inv)

variable {N} in

theorem isOpen_finiteLevelOne (hN : N ≠ ⊥) :
    IsOpen (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isOpen_setOf_isLevelOneMatrix R K hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLevelOneMatrix R K hN).preimage Units.continuous_coe_inv)

theorem isClosed_finiteLevelZero :
    IsClosed (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isClosed_setOf_isLevelZeroMatrix R K N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLevelZeroMatrix R K N).preimage Units.continuous_coe_inv)

theorem isClosed_finiteLevelOne :
    IsClosed (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  ((isClosed_setOf_isLevelOneMatrix R K N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLevelOneMatrix R K N).preimage Units.continuous_coe_inv)

section Compact

variable [Module.Free ℤ R] [Module.Finite ℤ R]

theorem isCompact_setOf_integral :
    IsCompact {g : GL (Fin 2) (FiniteAdeleRing R K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
        ∈ integralFiniteAdeles R K} := by
  set C : Set (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :=
    {m | ∀ i j, m i j ∈ integralFiniteAdeles R K} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 =>
        Set.pi Set.univ fun _ : Fin 2 => integralFiniteAdeles R K := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles R K
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : {g : GL (Fin 2) (FiniteAdeleRing R K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈ integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
        ∈ integralFiniteAdeles R K}
      = (Units.embedProduct (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) ⁻¹'
        (C ×ˢ (MulOpposite.op '' C)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      Set.mem_image, hC_def]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
    · rintro ⟨h1, m, hm, hm'⟩
      refine ⟨h1, ?_⟩
      have : m = ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :=
        MulOpposite.op_injective hm'
      rw [← this]; exact hm
  rw [heq]; exact hK

theorem isCompact_finiteLevelZero :
    IsCompact (finiteLevelZero R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  (isCompact_setOf_integral R K).of_isClosed_subset (isClosed_finiteLevelZero R K N)
    fun _ hg => ⟨hg.1.integral, hg.2.integral⟩

theorem isCompact_finiteLevelOne :
    IsCompact (finiteLevelOne R K N : Set (GL (Fin 2) (FiniteAdeleRing R K))) :=
  (isCompact_finiteLevelZero R K N).of_isClosed_subset (isClosed_finiteLevelOne R K N)
    (finiteLevelOne_le_finiteLevelZero R K N)

end Compact

end FiniteLevel

section Adelic

variable (N : Ideal R)

def levelZero : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelZero R K N).comap (glFin R K)

def levelOne : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelOne R K N).comap (glFin R K)

variable {R K N}

theorem mem_levelZero_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ levelZero R K N ↔ glFin R K g ∈ finiteLevelZero R K N := Iff.rfl

theorem mem_levelOne_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ levelOne R K N ↔ glFin R K g ∈ finiteLevelOne R K N := Iff.rfl

variable (R K N)

theorem levelOne_le_levelZero : levelOne R K N ≤ levelZero R K N :=
  Subgroup.comap_mono (finiteLevelOne_le_finiteLevelZero R K N)

variable {N} in

theorem isOpen_levelZero (hN : N ≠ ⊥) : IsOpen (levelZero R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isOpen_finiteLevelZero R K hN).preimage (continuous_glFin R K)

variable {N} in

theorem isOpen_levelOne (hN : N ≠ ⊥) : IsOpen (levelOne R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isOpen_finiteLevelOne R K hN).preimage (continuous_glFin R K)

theorem isClosed_levelZero : IsClosed (levelZero R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isClosed_finiteLevelZero R K N).preimage (continuous_glFin R K)

theorem isClosed_levelOne : IsClosed (levelOne R K N : Set (GL (Fin 2) (AdeleRing R K))) :=
  (isClosed_finiteLevelOne R K N).preimage (continuous_glFin R K)

end Adelic

section Gen

def diagOne {A : Type*} [CommRing A] : Aˣ →* GL (Fin 2) A where
  toFun a :=
    { val := Matrix.diagonal ![(a : A), 1]
      inv := Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp }
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diagOne_coe_apply {A : Type*} [CommRing A] (a : Aˣ) (i j : Fin 2) :
    (diagOne a : Matrix (Fin 2) (Fin 2) A) i j = Matrix.diagonal ![(a : A), 1] i j := rfl

def finIncl : FiniteAdeleRing R K →* AdeleRing R K where
  toFun x := ((1 : InfiniteAdeleRing K), x)
  map_one' := rfl
  map_mul' _ _ := Prod.ext (one_mul _).symm rfl

theorem finIncl_apply_fst (x : FiniteAdeleRing R K) : (finIncl R K x).1 = 1 := rfl
theorem finIncl_apply_snd (x : FiniteAdeleRing R K) : (finIncl R K x).2 = x := rfl

variable (v : HeightOneSpectrum R)

open scoped Classical in

def localUnit : (v.adicCompletion K)ˣ →* (FiniteAdeleRing R K)ˣ where
  toFun t :=
    { val := ⟨Function.update 1 v (t : v.adicCompletion K),
        Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
          by_contra hwv
          exact hw (by rw [Function.update_of_ne hwv]; exact one_mem _))⟩
      inv := ⟨Function.update 1 v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
          by_contra hwv
          exact hw (by rw [Function.update_of_ne hwv]; exact one_mem _))⟩
      val_inv := by
        refine Subtype.ext (funext fun w => ?_)
        show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            (t : v.adicCompletion K) w *
          Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w = 1
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      inv_val := by
        refine Subtype.ext (funext fun w => ?_)
        show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w *
          Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
            (t : v.adicCompletion K) w = 1
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw] }
  map_one' := by
    refine Units.ext (Subtype.ext (funext fun w => ?_))
    show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v 1 w = 1
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  map_mul' t t' := by
    refine Units.ext (Subtype.ext (funext fun w => ?_))
    show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
        ((t * t' : (v.adicCompletion K)ˣ) : v.adicCompletion K) w =
      Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
          (t : v.adicCompletion K) w *
        Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
          (t' : v.adicCompletion K) w
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]

open scoped Classical in
theorem localUnit_apply_self (t : (v.adicCompletion K)ˣ) :
    ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = t := by
  show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
      (t : v.adicCompletion K) v = t
  simp

open scoped Classical in
theorem localUnit_apply_of_ne (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum R} (hw : w ≠ v) :
    ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w = 1 := by
  show Function.update (1 : ∀ w : HeightOneSpectrum R, w.adicCompletion K) v
      (t : v.adicCompletion K) w = 1
  simp [Function.update_of_ne hw]

def heckeGenAt : (v.adicCompletion K)ˣ →* GL (Fin 2) (AdeleRing R K) :=
  diagOne.comp ((Units.map (finIncl R K)).comp (localUnit R K v))

variable {R K v}

theorem heckeGenAt_fst (t : (v.adicCompletion K)ˣ) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1
      = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem heckeGenAt_snd_apply_of_ne (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum R}
    (hw : w ≠ v) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 w
      = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  fin_cases i <;> fin_cases j
  · show ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w = 1
    exact localUnit_apply_of_ne R K v t hw
  · rfl
  · rfl
  · rfl

theorem heckeGenAt_snd_apply_self (t : (v.adicCompletion K)ˣ) (i j : Fin 2) :
    ((heckeGenAt R K v t : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 v
      = Matrix.diagonal ![(t : v.adicCompletion K), 1] i j := by
  fin_cases i <;> fin_cases j
  · show ((localUnit R K v t : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = t
    exact localUnit_apply_self R K v t
  · rfl
  · rfl
  · rfl

theorem heckeGenAt_inv_mul_heckeGenAt_mem_levelOne (t t' : (v.adicCompletion K)ˣ)
    (h : Valued.v (t : v.adicCompletion K) = Valued.v (t' : v.adicCompletion K)) (N : Ideal R) :
    (heckeGenAt R K v t)⁻¹ * heckeGenAt R K v t' ∈ levelOne R K N := by
  rw [← map_inv, ← map_mul]
  set u : (v.adicCompletion K)ˣ := t⁻¹ * t' with hu
  have ht0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  have hu1 : Valued.v (u : v.adicCompletion K) = 1 := by
    rw [hu, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h, ← h,
      inv_mul_cancel₀ ht0]
  have hui : Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]

  have hint : ∀ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 →
      ((localUnit R K v s : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
        ∈ integralFiniteAdeles R K := by
    intro s hs w
    classical
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, hs]
    · rw [localUnit_apply_of_ne R K v s hw]; exact one_mem _
  have key : ∀ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 →
      IsLevelOneMatrix R K N (glFin R K (heckeGenAt R K v s) : Matrix _ _ _) := by
    intro s hs
    refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact hint s hs
      · exact zero_mem_integralFiniteAdeles
      · exact zero_mem_integralFiniteAdeles
      · exact one_mem_integralFiniteAdeles
    · exact zero_mem_idealBall N
    · show (1 : FiniteAdeleRing R K) - 1 ∈ idealBall R K N
      rw [sub_self]; exact zero_mem_idealBall N
  refine ⟨key u hu1, ?_⟩
  rw [← map_inv, ← map_inv]
  exact key u⁻¹ hui

variable (K v)

def uniformizer : R := Classical.choose v.intValuation_exists_uniformizer

theorem intValuation_uniformizer : v.intValuation (uniformizer v) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec v.intValuation_exists_uniformizer

theorem valued_uniformizer :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v)))
      = WithZero.exp (-1 : ℤ) := by
  rw [valued_algebraMap, intValuation_uniformizer]

def uniformizerUnit : (v.adicCompletion K)ˣ :=
  Units.mk0 (algebraMap K (v.adicCompletion K) (algebraMap R K (uniformizer v))) fun h => by
    have := valued_uniformizer K v
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm

theorem valued_uniformizerUnit :
    Valued.v (uniformizerUnit K v : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  valued_uniformizer K v

variable (R)

def heckeGen : GL (Fin 2) (AdeleRing R K) := heckeGenAt R K v (uniformizerUnit K v)

variable {R K v}

theorem heckeGen_inv_mul_heckeGenAt_mem_levelOne (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (N : Ideal R) :
    (heckeGen R K v)⁻¹ * heckeGenAt R K v t ∈ levelOne R K N :=
  heckeGenAt_inv_mul_heckeGenAt_mem_levelOne _ _ ((valued_uniformizerUnit K v).trans ht.symm) N

end Gen

end NumberField.AdelicLevel

end


