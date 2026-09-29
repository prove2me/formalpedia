-- Prove2me | Definitions.Def_MvPowerSeries_RestrictedEvalV2
-- name    : MvPowerSeries_RestrictedEvalV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/1b4f96f5-40b2-5a23-bd54-839419f694bf
-- title:
--   Restricted evaluation of multivariate power series
-- statement:
--   Fix a commutative ring $\mathcal O$, an index type $\sigma$ and a natural number $p$ (no primality is assumed; $p$ is used through its image in the relevant ring). A series $S \in \mathcal O[[X_s : s \in \sigma]]$ satisfies `Tendsto0 p S` when for every $N$ the coefficient $\operatorname{coeff}_m S$ lies in the ideal $(p^N)$ for all but finitely many exponents $m$, i.e. the condition holds eventually along the cofinite filter on $\sigma \to_0 \mathbb N$. For such an $S$, `Tendsto0.bad hS N` is the resulting finite set of exceptional exponents $\{m : \operatorname{coeff}_m S \notin (p^N)\}$, increasing in $N$. A group of lemmas records that this class contains $0$, $1$, the images of polynomials, $X_s$ and $C(c)$, and is closed under addition, negation, subtraction and $\mathcal O$-scaling; when $\sigma$ is finite it is equivalently described by total degree (for each $N$ some $K$ with $\operatorname{coeff}_m S \in (p^N)$ whenever $\deg m \ge K$) and is closed under multiplication, powers, finite products, polynomial expressions (`tendsto0_aeval`) and substitution of a family of such series with vanishing constant coefficients (`tendsto0_subst`).
--
--   For the target, `Cplt p Y` abbreviates `IsAdicComplete (Ideal.span {(p : Y)}) Y`, and $Y$ is a commutative $\mathcal O$-algebra. With $\operatorname{monom} x\, m = \prod_s (x_s)^{m_s}$ and partial sums $\operatorname{psum} x\, T\, S = \sum_{m \in T} \operatorname{algebraMap}(\operatorname{coeff}_m S)\cdot \operatorname{monom} x\,m$ over finite sets $T$, the sums over `bad N` form a Cauchy family for the $(p)$-adic filtration, so completeness yields an element $L$ with $L - \operatorname{psum} x (\mathrm{bad}\,N) S \in (p^N)$ for all $N$; `evalT p hY x S` is such an $L$ for restricted $S$ and $0$ otherwise, hence a total function of an arbitrary tuple $x \in Y^{\sigma}$. It is characterised by the congruences $\operatorname{evalT} \equiv \operatorname{psum} x\,T\,S \pmod{(p^N)}$ for all finite $T \supseteq \mathrm{bad}\,N$, agrees with `MvPolynomial.aeval` on polynomials, is additive, $\mathcal O$-semilinear and (for finite $\sigma$) multiplicative, sends series with all coefficients in $(p^N)$ into $(p^N)Y$, and satisfies $\operatorname{evalT}(x, \operatorname{subst} a\, S) = \operatorname{evalT}(\operatorname{evalT}(x, a), S)$. The truncation `badPart p hS N` is the polynomial $\sum_{m \in \mathrm{bad}\,N} c_m X^m$ used to split a restricted series into a polynomial part and a part with all coefficients divisible by $p^N$.
--
--   **Relation to Mathlib.** Mathlib's `MvPowerSeries.aeval` and `MvPowerSeries.subst` evaluate at topologically nilpotent arguments; the predicate `Tendsto0` and the evaluation `evalT` defined here are the project's own, and impose the growth condition on the coefficients instead, so that the arguments $x \in Y^\sigma$ may be arbitrary. Completeness appears as an explicit hypothesis `Cplt p Y`, an abbreviation for Mathlib's `IsAdicComplete (Ideal.span {(p : Y)}) Y`, rather than as an instance.
--
--   **Where it is used.** The evaluation is needed where power series with $p$-adically growing divisibility of coefficients, such as the integral logarithm $f(pX)/p$ of a formal group, must be evaluated at elements that are not topologically nilpotent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvPowerSeries_RestrictedEvalV2.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries

namespace MvPowerSeries.Restricted

universe u v w

variable {𝓞 : Type u} [CommRing 𝓞] {σ : Type v}

def Tendsto0 (p : ℕ) (S : MvPowerSeries σ 𝓞) : Prop :=
  ∀ N : ℕ, ∀ᶠ m in Filter.cofinite, coeff m S ∈ Ideal.span {(p : 𝓞) ^ N}

namespace Tendsto0

variable {p : ℕ} {S T : MvPowerSeries σ 𝓞}

theorem finite_setOf (hS : Tendsto0 p S) (N : ℕ) :
    {m : σ →₀ ℕ | coeff m S ∉ Ideal.span {(p : 𝓞) ^ N}}.Finite :=
  Filter.eventually_cofinite.1 (hS N)

noncomputable def bad (hS : Tendsto0 p S) (N : ℕ) : Finset (σ →₀ ℕ) :=
  (hS.finite_setOf N).toFinset

theorem mem_bad_iff (hS : Tendsto0 p S) (N : ℕ) (m : σ →₀ ℕ) :
    m ∈ hS.bad N ↔ coeff m S ∉ Ideal.span {(p : 𝓞) ^ N} := by
  simp [bad]

theorem coeff_mem_of_not_mem_bad (hS : Tendsto0 p S) {N : ℕ} {m : σ →₀ ℕ} (hm : m ∉ hS.bad N) :
    coeff m S ∈ Ideal.span {(p : 𝓞) ^ N} := by
  by_contra h
  exact hm ((hS.mem_bad_iff N m).2 h)

theorem span_pow_le_span_pow {R : Type*} [CommRing R] (a : R) {M N : ℕ} (h : M ≤ N) :
    Ideal.span {a ^ N} ≤ Ideal.span {a ^ M} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow a h)

theorem bad_mono (hS : Tendsto0 p S) {M N : ℕ} (h : M ≤ N) : hS.bad M ⊆ hS.bad N := by
  intro m hm
  rw [mem_bad_iff] at hm ⊢
  exact fun h' => hm (span_pow_le_span_pow (p : 𝓞) h h')

theorem of_forall_eventually_eq_zero {S : MvPowerSeries σ 𝓞}
    (h : ∀ᶠ m in Filter.cofinite, coeff m S = 0) : Tendsto0 p S := by
  intro N
  filter_upwards [h] with m hm
  rw [hm]
  exact Ideal.zero_mem _

theorem zero : Tendsto0 p (0 : MvPowerSeries σ 𝓞) :=
  of_forall_eventually_eq_zero (Filter.Eventually.of_forall fun m => by simp)

theorem coe (P : MvPolynomial σ 𝓞) : Tendsto0 p (P : MvPowerSeries σ 𝓞) := by
  apply of_forall_eventually_eq_zero
  rw [Filter.eventually_cofinite]
  refine (P.support.finite_toSet).subset ?_
  intro m hm
  by_contra h'
  apply hm
  rw [MvPolynomial.coeff_coe]
  exact MvPolynomial.notMem_support_iff.1 h'

theorem one : Tendsto0 p (1 : MvPowerSeries σ 𝓞) := by
  have h := coe (p := p) (σ := σ) (𝓞 := 𝓞) 1
  rwa [MvPolynomial.coe_one] at h

theorem add (hS : Tendsto0 p S) (hT : Tendsto0 p T) : Tendsto0 p (S + T) := by
  intro N
  filter_upwards [hS N, hT N] with m hmS hmT
  rw [map_add]
  exact Ideal.add_mem _ hmS hmT

theorem neg (hS : Tendsto0 p S) : Tendsto0 p (-S) := by
  intro N
  filter_upwards [hS N] with m hm
  rw [map_neg]
  exact (Ideal.neg_mem_iff _).2 hm

theorem sub (hS : Tendsto0 p S) (hT : Tendsto0 p T) : Tendsto0 p (S - T) := by
  rw [sub_eq_add_neg]; exact hS.add hT.neg

theorem smul (hS : Tendsto0 p S) (c : 𝓞) : Tendsto0 p (c • S) := by
  intro N
  filter_upwards [hS N] with m hm
  rw [map_smul, smul_eq_mul]
  exact Ideal.mul_mem_left _ c hm

theorem exists_degree [Finite σ] (hS : Tendsto0 p S) (N : ℕ) :
    ∃ K : ℕ, ∀ m : σ →₀ ℕ, K ≤ m.degree → coeff m S ∈ Ideal.span {(p : 𝓞) ^ N} := by
  classical
  refine ⟨(hS.bad N).sup (fun m => m.degree) + 1, fun m hm => ?_⟩
  apply hS.coeff_mem_of_not_mem_bad
  intro hbad
  have := Finset.le_sup (f := fun m : σ →₀ ℕ => m.degree) hbad
  omega

theorem of_degree [Finite σ] {S : MvPowerSeries σ 𝓞}
    (h : ∀ N : ℕ, ∃ K : ℕ, ∀ m : σ →₀ ℕ, K ≤ m.degree → coeff m S ∈ Ideal.span {(p : 𝓞) ^ N}) :
    Tendsto0 p S := by
  classical
  intro N
  obtain ⟨K, hK⟩ := h N
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Finsupp.finite_of_degree_le (σ := σ) (n := K)) ?_
  intro m hm
  by_contra h'
  simp only [Set.mem_setOf_eq, not_le] at h'
  exact hm (hK m h'.le)

theorem mul [Finite σ] (hS : Tendsto0 p S) (hT : Tendsto0 p T) : Tendsto0 p (S * T) := by
  classical
  apply of_degree
  intro N
  obtain ⟨K, hK⟩ := hS.exists_degree N
  obtain ⟨K', hK'⟩ := hT.exists_degree N
  refine ⟨K + K', fun e he => ?_⟩
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hdeg : x.1.degree + x.2.degree = e.degree := by rw [← map_add, hx]
  by_cases h1 : K ≤ x.1.degree
  · exact Ideal.mul_mem_right _ _ (hK _ h1)
  · have h2 : K' ≤ x.2.degree := by omega
    exact Ideal.mul_mem_left _ _ (hK' _ h2)

theorem pow [Finite σ] (hS : Tendsto0 p S) : ∀ n : ℕ, Tendsto0 p (S ^ n)
  | 0 => by rw [pow_zero]; exact one
  | n + 1 => by rw [pow_succ]; exact (pow hS n).mul hS

theorem prod [Finite σ] {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ 𝓞)
    (hf : ∀ i ∈ s, Tendsto0 p (f i)) : Tendsto0 p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Tendsto0

theorem tendsto0_X (p : ℕ) (s : σ) : Tendsto0 p (X s : MvPowerSeries σ 𝓞) := by
  have h := Tendsto0.coe (p := p) (MvPolynomial.X s : MvPolynomial σ 𝓞)
  rwa [MvPolynomial.coe_X] at h

theorem tendsto0_C (p : ℕ) (c : 𝓞) : Tendsto0 p (C c : MvPowerSeries σ 𝓞) := by
  have h := Tendsto0.coe (p := p) (MvPolynomial.C c : MvPolynomial σ 𝓞)
  rwa [MvPolynomial.coe_C] at h

theorem tendsto0_of_forall_coeff_mem_pow_degree [Finite σ] (p : ℕ) {S : MvPowerSeries σ 𝓞}
    (h : ∀ m, coeff m S ∈ Ideal.span {(p : 𝓞) ^ m.degree}) : Tendsto0 p S :=
  Tendsto0.of_degree fun N => ⟨N, fun m hm => Tendsto0.span_pow_le_span_pow (p : 𝓞) hm (h m)⟩

section Eval

variable (p : ℕ) {Y : Type w} [CommRing Y] [Algebra 𝓞 Y]

abbrev Cplt (Y : Type w) [CommRing Y] : Prop := IsAdicComplete (Ideal.span {(p : Y)}) Y

def monom (x : σ → Y) (m : σ →₀ ℕ) : Y := m.prod fun s e => x s ^ e

theorem monom_zero (x : σ → Y) : monom x 0 = 1 := by simp [monom]

theorem monom_add (x : σ → Y) (m m' : σ →₀ ℕ) : monom x (m + m') = monom x m * monom x m' := by
  classical
  simp only [monom]
  rw [Finsupp.prod_add_index']
  · intro s; exact pow_zero _
  · intro s a b; exact pow_add _ _ _

noncomputable def psum (x : σ → Y) (T : Finset (σ →₀ ℕ)) (S : MvPowerSeries σ 𝓞) : Y :=
  ∑ m ∈ T, algebraMap 𝓞 Y (coeff m S) * monom x m

theorem algebraMap_mem_span_pow {N : ℕ} {c : 𝓞} (hc : c ∈ Ideal.span {(p : 𝓞) ^ N}) :
    algebraMap 𝓞 Y c ∈ Ideal.span {(p : Y) ^ N} := by
  rw [Ideal.mem_span_singleton] at hc ⊢
  obtain ⟨d, rfl⟩ := hc
  refine ⟨algebraMap 𝓞 Y d, ?_⟩
  rw [map_mul, map_pow, map_natCast]

theorem psum_sub_psum_mem {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) {N : ℕ}
    {T T' : Finset (σ →₀ ℕ)} (hT : hS.bad N ⊆ T) (hT' : hS.bad N ⊆ T') :
    psum x T S - psum x T' S ∈ Ideal.span {(p : Y) ^ N} := by
  classical
  have key : ∀ (A B : Finset (σ →₀ ℕ)), hS.bad N ⊆ B →
      psum x A S - psum x (A ∩ B) S ∈ Ideal.span {(p : Y) ^ N} := by
    intro A B hB
    rw [psum, psum, ← Finset.sum_sdiff (Finset.inter_subset_left (s₁ := A) (s₂ := B)), add_sub_cancel_right]
    refine Ideal.sum_mem _ fun m hm => ?_
    rw [Finset.mem_sdiff, Finset.mem_inter, not_and] at hm
    have hmB : m ∉ hS.bad N := fun h => hm.2 hm.1 (hB h)
    exact Ideal.mul_mem_right _ _ (algebraMap_mem_span_pow p (hS.coeff_mem_of_not_mem_bad hmB))
  have h1 := key T T' hT'
  have h2 := key T' T hT
  rw [Finset.inter_comm] at h2
  have := Ideal.sub_mem _ h1 h2
  rwa [sub_sub_sub_cancel_right] at this

theorem smodEq_iff_sub_mem (N : ℕ) (a b : Y) :
    a ≡ b [SMOD (Ideal.span {(p : Y)}) ^ N • (⊤ : Submodule Y Y)] ↔ a - b ∈ Ideal.span {(p : Y) ^ N} := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]

theorem eq_of_forall_sub_mem (hY : Cplt p Y) {a b : Y}
    (h : ∀ N : ℕ, a - b ∈ Ideal.span {(p : Y) ^ N}) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hY.toIsHausdorff (a - b) fun N => ?_
  rw [smodEq_iff_sub_mem, sub_zero]
  exact h N

theorem exists_limit (hY : Cplt p Y) {S : MvPowerSeries σ 𝓞}
    (hS : Tendsto0 p S) (x : σ → Y) :
    ∃ L : Y, ∀ N : ℕ, L - psum x (hS.bad N) S ∈ Ideal.span {(p : Y) ^ N} := by
  have hprec := IsPrecomplete.prec hY.toIsPrecomplete (f := fun N => psum x (hS.bad N) S) ?_
  · obtain ⟨L, hL⟩ := hprec
    refine ⟨L, fun N => ?_⟩
    have h := (smodEq_iff_sub_mem p N _ _).1 (hL N)
    rw [← Ideal.neg_mem_iff, neg_sub] at h
    exact h
  · intro M N hMN
    rw [smodEq_iff_sub_mem]
    exact psum_sub_psum_mem p hS x subset_rfl (hS.bad_mono hMN)

open Classical in

noncomputable def evalT (hY : Cplt p Y) (x : σ → Y) (S : MvPowerSeries σ 𝓞) : Y :=
  if hS : Tendsto0 p S then Classical.choose (exists_limit p hY hS x) else 0

variable (hY : Cplt p Y)
include hY

theorem evalT_sub_psum_bad_mem {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) (N : ℕ) :
    evalT p hY x S - psum x (hS.bad N) S ∈ Ideal.span {(p : Y) ^ N} := by
  rw [evalT, dif_pos hS]
  exact Classical.choose_spec (exists_limit p hY hS x) N

theorem evalT_sub_psum_mem {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) {N : ℕ}
    {T : Finset (σ →₀ ℕ)} (hT : hS.bad N ⊆ T) :
    evalT p hY x S - psum x T S ∈ Ideal.span {(p : Y) ^ N} := by
  have h1 := evalT_sub_psum_bad_mem p hY hS x N
  have h2 := psum_sub_psum_mem p hS x subset_rfl hT
  have := Ideal.add_mem _ h1 h2
  rwa [sub_add_sub_cancel] at this

theorem evalT_mem_of_forall_coeff_mem {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) {N : ℕ}
    (h : ∀ m, coeff m S ∈ Ideal.span {(p : 𝓞) ^ N}) : evalT p hY x S ∈ Ideal.span {(p : Y) ^ N} := by
  have hbad : hS.bad N = ∅ := by
    ext m
    simp only [Finset.notMem_empty, iff_false]
    rw [hS.mem_bad_iff]
    exact fun hm => hm (h m)
  have := evalT_sub_psum_bad_mem p hY hS x N
  rwa [hbad, psum, Finset.sum_empty, sub_zero] at this

theorem evalT_congr_of_forall_sub_mem {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) {a : Y}
    (h : ∀ N : ℕ, ∃ T : Finset (σ →₀ ℕ), hS.bad N ⊆ T ∧ a - psum x T S ∈ Ideal.span {(p : Y) ^ N}) :
    evalT p hY x S = a := by
  refine eq_of_forall_sub_mem p hY fun N => ?_
  obtain ⟨T, hT, ha⟩ := h N
  have := Ideal.sub_mem _ (evalT_sub_psum_mem p hY hS x hT) ha
  rwa [sub_sub_sub_cancel_right] at this

theorem evalT_coe (x : σ → Y) (P : MvPolynomial σ 𝓞) :
    evalT p hY x (P : MvPowerSeries σ 𝓞) = MvPolynomial.aeval x P := by
  classical
  apply evalT_congr_of_forall_sub_mem p hY (Tendsto0.coe P) x
  intro N
  refine ⟨(Tendsto0.coe (p := p) P).bad N ∪ P.support, Finset.subset_union_left, ?_⟩
  have : psum x ((Tendsto0.coe (p := p) P).bad N ∪ P.support) (P : MvPowerSeries σ 𝓞) =
      MvPolynomial.aeval x P := by
    rw [psum, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, ← Finset.sum_subset Finset.subset_union_right]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.coeff_coe, monom, Finsupp.prod]
    · intro m _ hm
      rw [MvPolynomial.coeff_coe, MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]
  rw [this, sub_self]
  exact Ideal.zero_mem _

theorem evalT_add {S T : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (hT : Tendsto0 p T) (x : σ → Y) :
    evalT p hY x (S + T) = evalT p hY x S + evalT p hY x T := by
  classical
  apply evalT_congr_of_forall_sub_mem p hY (hS.add hT) x
  intro N
  refine ⟨(hS.add hT).bad N ∪ (hS.bad N ∪ hT.bad N), Finset.subset_union_left, ?_⟩
  set U := (hS.add hT).bad N ∪ (hS.bad N ∪ hT.bad N)
  have hU : psum x U (S + T) = psum x U S + psum x U T := by
    simp only [psum, map_add, add_mul, Finset.sum_add_distrib]
  rw [hU, add_sub_add_comm]
  exact Ideal.add_mem _
    (evalT_sub_psum_mem p hY hS x (Finset.subset_union_left.trans Finset.subset_union_right))
    (evalT_sub_psum_mem p hY hT x (Finset.subset_union_right.trans Finset.subset_union_right))

theorem evalT_smul {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (c : 𝓞) (x : σ → Y) :
    evalT p hY x (c • S) = algebraMap 𝓞 Y c * evalT p hY x S := by
  classical
  apply evalT_congr_of_forall_sub_mem p hY (hS.smul c) x
  intro N
  refine ⟨(hS.smul c).bad N ∪ hS.bad N, Finset.subset_union_left, ?_⟩
  have hU : psum x ((hS.smul c).bad N ∪ hS.bad N) (c • S) =
      algebraMap 𝓞 Y c * psum x ((hS.smul c).bad N ∪ hS.bad N) S := by
    simp only [psum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  rw [hU, ← mul_sub]
  exact Ideal.mul_mem_left _ _ (evalT_sub_psum_mem p hY hS x Finset.subset_union_right)

theorem evalT_neg {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) :
    evalT p hY x (-S) = -evalT p hY x S := by
  have h := evalT_smul p hY hS (-1 : 𝓞) x
  rwa [neg_one_smul, map_neg, map_one, neg_one_mul] at h

theorem evalT_sub {S T : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (hT : Tendsto0 p T) (x : σ → Y) :
    evalT p hY x (S - T) = evalT p hY x S - evalT p hY x T := by
  rw [sub_eq_add_neg, evalT_add p hY hS hT.neg, evalT_neg p hY hT, sub_eq_add_neg]

theorem evalT_zero (x : σ → Y) : evalT p hY x (0 : MvPowerSeries σ 𝓞) = 0 := by
  have h := evalT_coe p hY x (0 : MvPolynomial σ 𝓞)
  rwa [MvPolynomial.coe_zero, map_zero] at h

theorem evalT_one (x : σ → Y) : evalT p hY x (1 : MvPowerSeries σ 𝓞) = 1 := by
  have h := evalT_coe p hY x (1 : MvPolynomial σ 𝓞)
  rwa [MvPolynomial.coe_one, map_one] at h

theorem evalT_C (x : σ → Y) (c : 𝓞) : evalT p hY x (C c : MvPowerSeries σ 𝓞) = algebraMap 𝓞 Y c := by
  have h := evalT_coe p hY x (MvPolynomial.C c : MvPolynomial σ 𝓞)
  rwa [MvPolynomial.coe_C, MvPolynomial.aeval_C] at h

theorem evalT_X (x : σ → Y) (s : σ) : evalT p hY x (X s : MvPowerSeries σ 𝓞) = x s := by
  have h := evalT_coe p hY x (MvPolynomial.X s : MvPolynomial σ 𝓞)
  rwa [MvPolynomial.coe_X, MvPolynomial.aeval_X] at h

noncomputable def badPart {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (N : ℕ) : MvPolynomial σ 𝓞 :=
  ∑ m ∈ hS.bad N, MvPolynomial.monomial m (coeff m S)

omit hY in
theorem coeff_badPart [DecidableEq σ] {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (N : ℕ) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (badPart p hS N) = if m ∈ hS.bad N then coeff m S else 0 := by
  classical
  rw [badPart, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']

omit hY in

theorem coeff_sub_badPart_mem {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (N : ℕ) (m : σ →₀ ℕ) :
    coeff m (S - (badPart p hS N : MvPowerSeries σ 𝓞)) ∈ Ideal.span {(p : 𝓞) ^ N} := by
  classical
  rw [map_sub, MvPolynomial.coeff_coe, coeff_badPart]
  split_ifs with h
  · rw [sub_self]; exact Ideal.zero_mem _
  · rw [sub_zero]; exact hS.coeff_mem_of_not_mem_bad h

omit hY in
theorem coeff_mul_mem_of_forall_left {I : Ideal 𝓞} {S : MvPowerSeries σ 𝓞} (h : ∀ m, coeff m S ∈ I)
    (T : MvPowerSeries σ 𝓞) (e : σ →₀ ℕ) : coeff e (S * T) ∈ I := by
  classical
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (h x.1)

omit hY in
theorem coeff_mul_mem_of_forall_right {I : Ideal 𝓞} (S : MvPowerSeries σ 𝓞) {T : MvPowerSeries σ 𝓞}
    (h : ∀ m, coeff m T ∈ I) (e : σ →₀ ℕ) : coeff e (S * T) ∈ I := by
  rw [mul_comm]; exact coeff_mul_mem_of_forall_left h S e

theorem evalT_sub_aeval_badPart_mem {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) (N : ℕ) :
    evalT p hY x S - MvPolynomial.aeval x (badPart p hS N) ∈ Ideal.span {(p : Y) ^ N} := by
  classical
  have hdec : S = (badPart p hS N : MvPowerSeries σ 𝓞) + (S - (badPart p hS N : MvPowerSeries σ 𝓞)) := by
    ring
  have h1 : evalT p hY x S = evalT p hY x (badPart p hS N : MvPowerSeries σ 𝓞) +
      evalT p hY x (S - (badPart p hS N : MvPowerSeries σ 𝓞)) := by
    conv_lhs => rw [hdec]
    exact evalT_add p hY (Tendsto0.coe _) (hS.sub (Tendsto0.coe _)) x
  rw [h1, evalT_coe, add_sub_cancel_left]
  exact evalT_mem_of_forall_coeff_mem p hY (hS.sub (Tendsto0.coe _)) x (coeff_sub_badPart_mem p hS N)

theorem evalT_mul [Finite σ] {S T : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (hT : Tendsto0 p T)
    (x : σ → Y) : evalT p hY x (S * T) = evalT p hY x S * evalT p hY x T := by
  classical
  refine eq_of_forall_sub_mem p hY fun N => ?_
  set PS := badPart p hS N
  set PT := badPart p hT N
  set S' := S - (PS : MvPowerSeries σ 𝓞)
  set T' := T - (PT : MvPowerSeries σ 𝓞)
  have hS' : Tendsto0 p S' := hS.sub (Tendsto0.coe _)
  have hT' : Tendsto0 p T' := hT.sub (Tendsto0.coe _)
  have hcS' : ∀ m, coeff m S' ∈ Ideal.span {(p : 𝓞) ^ N} := coeff_sub_badPart_mem p hS N
  have hcT' : ∀ m, coeff m T' ∈ Ideal.span {(p : 𝓞) ^ N} := coeff_sub_badPart_mem p hT N
  have hdec : S * T = ((PS * PT : MvPolynomial σ 𝓞) : MvPowerSeries σ 𝓞) +
      ((PS : MvPowerSeries σ 𝓞) * T' + S' * T) := by
    simp only [S', T', MvPolynomial.coe_mul]; ring
  have hR : Tendsto0 p ((PS : MvPowerSeries σ 𝓞) * T' + S' * T) :=
    ((Tendsto0.coe _).mul hT').add (hS'.mul hT)
  have hcR : ∀ m, coeff m ((PS : MvPowerSeries σ 𝓞) * T' + S' * T) ∈ Ideal.span {(p : 𝓞) ^ N} := by
    intro m
    rw [map_add]
    exact Ideal.add_mem _ (coeff_mul_mem_of_forall_right _ hcT' m) (coeff_mul_mem_of_forall_left hcS' _ m)
  have h1 : evalT p hY x (S * T) = MvPolynomial.aeval x PS * MvPolynomial.aeval x PT +
      evalT p hY x ((PS : MvPowerSeries σ 𝓞) * T' + S' * T) := by
    rw [hdec, evalT_add p hY (Tendsto0.coe _) hR, evalT_coe, map_mul]
  have h2 := evalT_mem_of_forall_coeff_mem p hY hR x hcR
  have h3 := evalT_sub_aeval_badPart_mem p hY hS x N
  have h4 := evalT_sub_aeval_badPart_mem p hY hT x N

  have h5 : evalT p hY x S * evalT p hY x T - MvPolynomial.aeval x PS * MvPolynomial.aeval x PT ∈
      Ideal.span {(p : Y) ^ N} := by
    have : evalT p hY x S * evalT p hY x T - MvPolynomial.aeval x PS * MvPolynomial.aeval x PT =
        (evalT p hY x S - MvPolynomial.aeval x PS) * evalT p hY x T +
          MvPolynomial.aeval x PS * (evalT p hY x T - MvPolynomial.aeval x PT) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h3) (Ideal.mul_mem_left _ _ h4)
  rw [h1]
  have : MvPolynomial.aeval x PS * MvPolynomial.aeval x PT +
      evalT p hY x ((PS : MvPowerSeries σ 𝓞) * T' + S' * T) - evalT p hY x S * evalT p hY x T =
      evalT p hY x ((PS : MvPowerSeries σ 𝓞) * T' + S' * T) -
        (evalT p hY x S * evalT p hY x T - MvPolynomial.aeval x PS * MvPolynomial.aeval x PT) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h5

theorem evalT_pow [Finite σ] {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) :
    ∀ n : ℕ, evalT p hY x (S ^ n) = evalT p hY x S ^ n
  | 0 => by rw [pow_zero, pow_zero, evalT_one]
  | n + 1 => by rw [pow_succ, pow_succ, evalT_mul p hY (hS.pow n) hS, evalT_pow hS x n]

omit hY in
theorem tendsto0_aeval [Finite σ] {τ : Type*} (a : τ → MvPowerSeries σ 𝓞) (ha : ∀ i, Tendsto0 p (a i))
    (P : MvPolynomial τ 𝓞) : Tendsto0 p (MvPolynomial.aeval a P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    exact Tendsto0.one.smul c
  | add P Q hP hQ => rw [map_add]; exact hP.add hQ
  | mul_X P i hP => rw [map_mul, MvPolynomial.aeval_X]; exact hP.mul (ha i)

theorem evalT_aeval [Finite σ] {τ : Type*} (a : τ → MvPowerSeries σ 𝓞) (ha : ∀ i, Tendsto0 p (a i))
    (x : σ → Y) (P : MvPolynomial τ 𝓞) :
    evalT p hY x (MvPolynomial.aeval a P) = MvPolynomial.aeval (fun i => evalT p hY x (a i)) P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
      evalT_smul p hY Tendsto0.one, evalT_one, mul_one]
  | add P Q hP hQ =>
    rw [map_add, map_add, evalT_add p hY (tendsto0_aeval p a ha P) (tendsto0_aeval p a ha Q), hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_X,
      evalT_mul p hY (tendsto0_aeval p a ha P) (ha i), hP]

omit hY in

theorem tendsto0_subst [Finite σ] {τ : Type*} [Finite τ] {a : τ → MvPowerSeries σ 𝓞}
    (ha0 : ∀ i, constantCoeff (a i) = 0) (ha : ∀ i, Tendsto0 p (a i))
    {S : MvPowerSeries τ 𝓞} (hS : Tendsto0 p S) : Tendsto0 p (subst a S) := by
  classical
  have has : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  intro N

  have hmon : ∀ d : τ →₀ ℕ, Tendsto0 p (d.prod fun s e => a s ^ e) := by
    intro d
    exact Tendsto0.prod _ _ fun s _ => (ha s).pow _
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset ((hS.bad N).finite_toSet.biUnion fun d _ => (hmon d).finite_setOf N) ?_
  intro e he
  simp only [Set.mem_setOf_eq] at he
  by_contra hcon
  apply he
  rw [coeff_subst has S e, finsum_eq_sum _ (coeff_subst_finite has S e)]
  refine Ideal.sum_mem _ fun d hd => ?_
  by_cases hbad : d ∈ hS.bad N
  · have : coeff e (d.prod fun s e => a s ^ e) ∈ Ideal.span {(p : 𝓞) ^ N} := by
      by_contra h'
      exact hcon (Set.mem_biUnion (Finset.mem_coe.2 hbad) h')
    rw [smul_eq_mul]
    exact Ideal.mul_mem_left _ _ this
  · rw [smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (hS.coeff_mem_of_not_mem_bad hbad)

omit hY in
theorem coeff_subst_mem_of_forall {τ : Type*} {a : τ → MvPowerSeries σ 𝓞} (has : HasSubst a)
    {I : Ideal 𝓞} {S : MvPowerSeries τ 𝓞} (h : ∀ d, coeff d S ∈ I) (e : σ →₀ ℕ) :
    coeff e (subst a S) ∈ I := by
  classical
  rw [coeff_subst has S e, finsum_eq_sum _ (coeff_subst_finite has S e)]
  refine Ideal.sum_mem _ fun d _ => ?_
  rw [smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (h d)

theorem evalT_subst [Finite σ] {τ : Type*} [Finite τ] {a : τ → MvPowerSeries σ 𝓞}
    (ha0 : ∀ i, constantCoeff (a i) = 0) (ha : ∀ i, Tendsto0 p (a i))
    {S : MvPowerSeries τ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) :
    evalT p hY x (subst a S) = evalT p hY (fun i => evalT p hY x (a i)) S := by
  classical
  have has : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  refine eq_of_forall_sub_mem p hY fun N => ?_
  set P := badPart p hS N
  set S' := S - (P : MvPowerSeries τ 𝓞)
  have hS' : Tendsto0 p S' := hS.sub (Tendsto0.coe _)
  have hdec : S = (P : MvPowerSeries τ 𝓞) + S' := by simp only [S']; ring
  have hsub : subst a S = MvPolynomial.aeval a P + subst a S' := by
    conv_lhs => rw [hdec]
    rw [subst_add has, subst_coe]
  have hS'sub : Tendsto0 p (subst a S') := tendsto0_subst p ha0 ha hS'
  have h1 : evalT p hY x (subst a S) = MvPolynomial.aeval (fun i => evalT p hY x (a i)) P +
      evalT p hY x (subst a S') := by
    rw [hsub, evalT_add p hY (tendsto0_aeval p a ha P) hS'sub, evalT_aeval p hY a ha]
  have h2 : evalT p hY x (subst a S') ∈ Ideal.span {(p : Y) ^ N} :=
    evalT_mem_of_forall_coeff_mem p hY hS'sub x
      (coeff_subst_mem_of_forall has (coeff_sub_badPart_mem p hS N))
  have h3 := evalT_sub_aeval_badPart_mem p hY hS (fun i => evalT p hY x (a i)) N
  rw [h1]
  have : MvPolynomial.aeval (fun i => evalT p hY x (a i)) P + evalT p hY x (subst a S') -
      evalT p hY (fun i => evalT p hY x (a i)) S =
      evalT p hY x (subst a S') - (evalT p hY (fun i => evalT p hY x (a i)) S -
        MvPolynomial.aeval (fun i => evalT p hY x (a i)) P) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h3

end Eval

end MvPowerSeries.Restricted


