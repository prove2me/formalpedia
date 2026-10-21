-- Prove2me | Definitions.Def_FiniteFields_Dwork_NuclearOperator
-- name    : FiniteFields_Dwork_NuclearOperator
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T01:29:37.767103+00:00
-- url     : https://prove2.me/theorems/32ffd573-afeb-46a2-826b-3903ade8326c
-- title:
--   Dwork's Frobenius operator $\alpha=\sigma^{-1}\circ\psi_p\circ F$ on the ramified Tate algebra and nuclear traces
-- statement:
--   Let $k$ be a finite field with $q=p^a$ elements, $a=[k:\mathbb F_p]$. Let $L=K_0(\zeta)$ be the ramified coefficient field with Frobenius $\sigma_L$, $\lambda=\zeta-1$, and let $\theta$ be Dwork's splitting series, all from the preceding files. Fix $d$ and a positive weight $w$ on $\mathbb N^d$. Write $L\langle x\rangle=L\langle x_1,\dots,x_d\rangle$ for the Tate algebra over $L$.
--
--   1. **Splitting product.** For $a\in k$ and $u\in\mathbb N^d$, the series $\theta(\hat a\,x^u)=\sum_n\theta_n\hat a^{\,n}x^{nu}$ converges in $L\langle x\rangle$, where $\hat a$ is the Teichmüller lift. For a polynomial $f=\sum_u a_ux^u$ over $k$ with finite support, the splitting product is
--   $$F_f(x)=\prod_{u\in\operatorname{supp}f}\theta\big(\hat a_u\,x^u\big)\in L\langle x\rangle .$$
--   2. **Dwork's operators.** The $p$-level operator and the $q$-level operator are
--   $$\alpha_f=\sigma_L^{-1}\circ\psi_p\circ M_{F_f},\qquad \alpha_{f,q}=\alpha_f^{\,a}.$$
--   Here $M_{F_f}$ is multiplication by $F_f$, $\psi_p$ is exponent division $(\psi_pg)_u=g_{pu}$, and $\sigma_L^{-1}$ acts on coefficients. The map $\alpha_f$ is additive and $\sigma_L^{-1}$-semilinear. The matrix of $\alpha_{f,q}$ in the monomial basis is $A_f(u,v)=$ the coefficient of $x^u$ in $\alpha_{f,q}(x^v)$.
--   3. **Nuclear operators.** Let $K$ be a complete, nontrivially normed, ultrametric field. A nuclear operator is an infinite kernel $A:\mathbb N^d\times\mathbb N^d\to K$ together with a tail bound $t:\mathbb N\to\mathbb R$ such that:
--       1. $t(N)\ge0$ and $t(N)\to0$;
--       2. $|A(u,v)|\le t(N)$ whenever $|u|_w>N$ or $|v|_w>N$;
--       3. $|A(u,v)|\le1$ for all $u,v$.
--
--      Writing $A_{\le N}$ for the finite matrix indexed by $\{u:|u|_w\le N\}$, the trace of the $s$-th power ($s\ge1$) is
--   $$\operatorname{Tr}(A^s)=\lim_{N\to\infty}\operatorname{tr}\big((A_{\le N})^s\big).$$
--   4. **Dwork's nuclear operator.** The kernel $A_f$ is conjugated by an explicit diagonal matrix of powers of $\lambda$, giving $\lambda^{n(v)-n(u)}A_f(u,v)$. With an explicit tail bound that is a power of $|\lambda|$, this is a nuclear operator over $L$ in the above sense.
--   5. **Witt trace.** The trace $W(k)\to W(\mathbb F_p)=\mathbb Z_p$ is defined by $w\mapsto\sum_{i<a}\sigma^i(w)$ through the Frobenius-fixed subring.
--   6. **Truncated principal units.** For a commutative ring $R$, the group of principal units of $R[[X]]/(X^N)$. The file also defines the series $-\sum_{j\ge0}X^{p^j-1}$, which is the logarithmic derivative of $E_p$, over any ring, and the image of $E_p$ in any $\mathbb Q$-algebra.
--
--   The file also contains the structural lemmas that make these definitions meaningful: convergence of the splitting factors, coefficient formulas, and the entry and tail estimates needed to bundle Dwork's kernel as a nuclear operator.
--
--   This is the operator side of Dwork's §2. The operator $\alpha_{f,q}$ is Dwork's $\psi\circ H$, and the nuclear trace is the trace appearing in his trace formula (14). The Witt trace and truncated principal units are the algebraic inputs for the additive-character identity (7)–(8).
--
--   **Formalization Note** The trace is defined with `limUnder`, so it is the true limit only when the limit exists. Its convergence under the decay hypotheses is proved separately. The diagonal exponents are $n(u)=\lfloor(3p|u|_w-G)/(2G)\rfloor$ with truncated subtraction, where $G=q\cdot\max(1,\max_{u\in\operatorname{supp}f}|u|_w)$. The tail bound is $|\lambda|^{\lfloor (N+1)/(2G)\rfloor-2}$, again with truncated subtraction. The nuclear-decay condition is the specific sufficient condition used in this development, and no equivalence with a classical definition of nuclear operators is claimed.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §2: the operator $\psi\circ H$, (13) and properties (I)–(III), and the trace in Lemma 2 (14); §1 (7)–(8) for the trace of the unramified extension. Lean: ported from the `finite_fields` project (commit e8b5bf14), modules `WeilConjectures/Dwork/TeichmullerSplitting.lean`, `WeilConjectures/Dwork/DworkFrobenius.lean`, `WeilConjectures/Dwork/FiniteTruncation.lean`, `WeilConjectures/Dwork/CompletelyContinuous.lean`, `WeilConjectures/Dwork/NuclearTrace.lean`, `WeilConjectures/Dwork/NuclearOperator.lean`, `WeilConjectures/Dwork/DworkNuclearOperator/OperatorKernel.lean`, `WeilConjectures/Dwork/DworkNuclearOperator/WeightNormalization.lean`, `WeilConjectures/Dwork/DworkNuclearOperator/NuclearBundle.lean`, `WeilConjectures/Dwork/WittTrace.lean`, `WeilConjectures/Dwork/TruncatedArtinHasse/TruncationPrincipalUnits.lean`.

import Mathlib
import Definitions.Def_FiniteFields_Dwork_ArtinHasse

section
noncomputable section
open Filter IsUltrametricDist Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ} (w : PositiveMonomialWeight d)
abbrev RamifiedOverconvergentTateAlgebra :=
  OverconvergentTateAlgebra (DworkCyclotomicField k p) d w
 def ramifiedTeichmullerLift_priv (a : k) : DworkCyclotomicField k p :=
  algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
    (coefficientRingAlgebraMap k p (teichmullerLift k p a))
 theorem coefficientRingAlgebraMap_norm_le_one (x : CoefficientRing k p) :
    ‖coefficientRingAlgebraMap k p x‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff]
  rw [show coefficientRingAlgebraMap k p x =
      (((WithVal.equiv (coefficientValuation k p)).symm
        (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) x) :
          WithVal (coefficientValuation k p)) : CoefficientField k p) by rfl]
  rw [Valued.valuedCompletion_apply]
  change coefficientValuation k p
      (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) x) ≤ 1
  exact (IsDiscreteValuationRing.maximalIdeal (CoefficientRing k p)).valuation_le_one
    (K := CoefficientFractionField k p) x
 theorem ramifiedTeichmullerLift_norm_le_one_priv (a : k) :
    ‖ramifiedTeichmullerLift_priv k p a‖ ≤ 1 := by
  rw [ramifiedTeichmullerLift_priv, dworkCyclotomicField_norm_algebraMap]
  exact coefficientRingAlgebraMap_norm_le_one k p (teichmullerLift k p a)
def ramifiedTateMonomial (u : MonomialIndex d) (a : DworkCyclotomicField k p) :
    RamifiedOverconvergentTateAlgebra k p w :=
  finsuppToOverconvergentTateAlgebra w 1 (Finsupp.single u a)
 theorem ramifiedTateMonomial_coefficient
    (u v : MonomialIndex d) (a : DworkCyclotomicField k p) :
    overconvergentTateAlgebraCoefficient w v (ramifiedTateMonomial k p w u a) =
      if u = v then a else 0 := by
  change seriesCoefficient w v
      (finsuppToOverconvergentSeries w 1 (Finsupp.single u a)) = _
  calc
    seriesCoefficient w v (finsuppToOverconvergentSeries w 1 (Finsupp.single u a)) =
        weightedCoefficient w (1 : DworkCyclotomicField k p) v
          (finsuppToOverconvergentSeries w 1 (Finsupp.single u a)) := by
      simp [weightedCoefficient_apply, seriesCoefficient_apply]
    _ = Finsupp.single u a v :=
      weightedCoefficient_finsuppToOverconvergentSeries
        w (1 : DworkCyclotomicField k p) one_ne_zero (Finsupp.single u a) v
    _ = if u = v then a else 0 := by simp [Finsupp.single_apply]
 theorem ramifiedTateMonomial_mul
    (u v : MonomialIndex d) (a b : DworkCyclotomicField k p) :
    ramifiedTateMonomial k p w u a * ramifiedTateMonomial k p w v b =
      ramifiedTateMonomial k p w (u + v) (a * b) := by
  simpa only [ramifiedTateMonomial, finsuppCauchyProduct_single] using
    (finsuppToOverconvergentTateAlgebra_mul w (1 : DworkCyclotomicField k p) one_ne_zero
      (Finsupp.single u a) (Finsupp.single v b)).symm
theorem ramifiedTateMonomial_pow
    (u : MonomialIndex d) (a : DworkCyclotomicField k p) (n : ℕ) :
    ramifiedTateMonomial k p w u a ^ n =
      ramifiedTateMonomial k p w (n • u) (a ^ n) := by
  induction n with
  | zero =>
      simp only [pow_zero, zero_nsmul]
      rfl
  | succ n ih =>
      rw [pow_succ, ih, ramifiedTateMonomial_mul, pow_succ, succ_nsmul]
 theorem ramifiedTateMonomial_norm_le
    (u : MonomialIndex d) (a : DworkCyclotomicField k p) :
    ‖ramifiedTateMonomial k p w u a‖ ≤ ‖a‖ := by
  rw [← OverconvergentTateAlgebra.norm_toSeries,
    ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg a)).2 ?_
  intro v
  have h := BoundedContinuousFunction.norm_coe_le_norm
    (finsuppToOverconvergentSeries w 1 (Finsupp.single u a)).toBCF v
  change ‖(finsuppToOverconvergentSeries w 1 (Finsupp.single u a)) v‖ ≤ ‖a‖
  calc
    ‖(finsuppToOverconvergentSeries w 1 (Finsupp.single u a)) v‖ ≤
        ‖finsuppToOverconvergentSeries w 1 (Finsupp.single u a)‖ := h
    _ ≤ ‖a‖ := by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      refine (BoundedContinuousFunction.norm_le (norm_nonneg a)).2 ?_
      intro z
      have hz := weightedCoefficient_finsuppToOverconvergentSeries
        w (1 : DworkCyclotomicField k p) one_ne_zero (Finsupp.single u a) z.ofTopology
      have hz' : (finsuppToOverconvergentSeries w 1 (Finsupp.single u a)) z =
          Finsupp.single u a z.ofTopology := by
        simpa [weightedCoefficient_apply, seriesCoefficient_apply] using hz
      change ‖(finsuppToOverconvergentSeries w 1 (Finsupp.single u a)) z‖ ≤ ‖a‖
      rw [hz']
      by_cases huz : u = z.ofTopology <;> simp [huz]
def dworkMonomialSplittingTerm (a : k) (u : MonomialIndex d) (n : ℕ) :
    RamifiedOverconvergentTateAlgebra k p w :=
  PowerSeries.coeff n (dworkSplittingFunction k p) •
    ramifiedTateMonomial k p w u (ramifiedTeichmullerLift_priv k p a) ^ n
theorem dworkMonomialSplittingTerm_norm_le (a : k) (u : MonomialIndex d) (n : ℕ) :
    ‖dworkMonomialSplittingTerm k p w a u n‖ ≤
      ‖dworkArtinHasseParameter k p‖ ^ n := by
  have hmonomial :
      ‖ramifiedTateMonomial k p w u (ramifiedTeichmullerLift_priv k p a) ^ n‖ ≤ 1 := by
    rw [ramifiedTateMonomial_pow]
    exact (ramifiedTateMonomial_norm_le k p w (n • u)
      (ramifiedTeichmullerLift_priv k p a ^ n)).trans <| by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (ramifiedTeichmullerLift_norm_le_one_priv k p a)
  exact (norm_smul_le _ _).trans <| by
    calc
      ‖PowerSeries.coeff n (dworkSplittingFunction k p)‖ *
          ‖ramifiedTateMonomial k p w u (ramifiedTeichmullerLift_priv k p a) ^ n‖ ≤
        ‖dworkArtinHasseParameter k p‖ ^ n * 1 :=
          mul_le_mul (dworkSplittingFunction_coeff_norm_le k p n) hmonomial
            (norm_nonneg _) (by positivity)
      _ = ‖dworkArtinHasseParameter k p‖ ^ n := mul_one _
theorem dworkMonomialSplittingTerm_hasSum (a : k) (u : MonomialIndex d) :
    HasSum (dworkMonomialSplittingTerm k p w a u)
      (∑' n : ℕ, dworkMonomialSplittingTerm k p w a u n) := by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ dworkMonomialSplittingTerm_norm_le k p w a u n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (dworkArtinHasseParameter_norm_lt_one k p))
def dworkMonomialSplittingFactor (a : k) (u : MonomialIndex d) :
    RamifiedOverconvergentTateAlgebra k p w :=
  ∑' n : ℕ, dworkMonomialSplittingTerm k p w a u n
 theorem dworkMonomialSplittingTerm_coefficient
    (a : k) (u v : MonomialIndex d) (n : ℕ) :
    overconvergentTateAlgebraCoefficient w v
        (dworkMonomialSplittingTerm k p w a u n) =
      if n • u = v then
        PowerSeries.coeff n (dworkSplittingFunction k p) *
          ramifiedTeichmullerLift_priv k p a ^ n
      else 0 := by
  rw [dworkMonomialSplittingTerm, map_smul,
    ramifiedTateMonomial_pow, ramifiedTateMonomial_coefficient]
  split_ifs with h
  · rfl
  · simp
theorem dworkMonomialSplittingFactor_coefficient
    (a : k) (u v : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w v
        (dworkMonomialSplittingFactor k p w a u) =
      ∑' n : ℕ, if n • u = v then
        PowerSeries.coeff n (dworkSplittingFunction k p) *
          algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
            (coefficientRingAlgebraMap k p (teichmullerLift k p a)) ^ n
      else 0 := by
  rw [dworkMonomialSplittingFactor,
    (overconvergentTateAlgebraCoefficient w v).map_tsum
      (dworkMonomialSplittingTerm_hasSum k p w a u).summable]
  apply tsum_congr
  intro n
  exact dworkMonomialSplittingTerm_coefficient k p w a u v n
theorem dworkMonomialSplittingFactor_coefficient_on_ray
    (a : k) {u : MonomialIndex d} (hu : u ≠ 0) (m : ℕ) :
    overconvergentTateAlgebraCoefficient w (m • u)
        (dworkMonomialSplittingFactor k p w a u) =
      PowerSeries.coeff m (dworkSplittingFunction k p) *
        algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
          (coefficientRingAlgebraMap k p (teichmullerLift k p a)) ^ m := by
  have hinjective : Function.Injective (fun n : ℕ ↦ n • u) := by
    intro n n' hnn'
    have hexists : ∃ i, u i ≠ 0 := by
      by_contra h
      apply hu
      ext i
      exact not_ne_iff.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hexists
    have hcoordinate := congrArg
      (Finsupp.lapply i : MonomialIndex d →ₗ[ℕ] ℕ) hnn'
    rw [map_nsmul, map_nsmul] at hcoordinate
    change n * u i = n' * u i at hcoordinate
    exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hi) hcoordinate
  rw [dworkMonomialSplittingFactor_coefficient]
  have hfiber : ∀ n : ℕ, (n • u = m • u) ↔ n = m := fun n ↦ hinjective.eq_iff
  simp only [hfiber]
  rw [tsum_eq_single m]
  · simp
  · intro n hn
    simp [hn]
theorem dworkMonomialSplittingFactor_coefficient_off_ray
    (a : k) (u v : MonomialIndex d) (hv : ∀ n : ℕ, n • u ≠ v) :
    overconvergentTateAlgebraCoefficient w v
        (dworkMonomialSplittingFactor k p w a u) = 0 := by
  rw [dworkMonomialSplittingFactor_coefficient]
  simp [hv]
theorem dworkMonomialSplittingFactor_norm_le_one (a : k) (u : MonomialIndex d) :
    ‖dworkMonomialSplittingFactor k p w a u‖ ≤ 1 := by
  rw [dworkMonomialSplittingFactor]
  apply norm_tsum_le_of_forall_le_of_nonneg zero_le_one
  intro n
  exact (dworkMonomialSplittingTerm_norm_le k p w a u n).trans <|
    pow_le_one₀ (norm_nonneg _) (dworkArtinHasseParameter_norm_lt_one k p).le
def teichmullerSplittingProduct (f : MonomialIndex d →₀ k) :
    RamifiedOverconvergentTateAlgebra k p w :=
  f.support.prod fun u ↦ dworkMonomialSplittingFactor k p w (f u) u
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ} (w : PositiveMonomialWeight d)
 def ramifiedCoefficientwiseFrobeniusInvSeries
    (g : OverconvergentSeries (DworkCyclotomicField k p) d w) :
    OverconvergentSeries (DworkCyclotomicField k p) d w where
  toFun u := (ramifiedCoefficientFrobenius k p).symm (g u)
  continuous_toFun := (ramifiedCoefficientFrobenius_symm_continuous k p).comp g.continuous
  zero_at_infty' :=
    ((ramifiedCoefficientFrobenius_symm_continuous k p).tendsto' 0 0
      (map_zero (ramifiedCoefficientFrobenius k p).symm)).comp (zero_at_infty g)
def ramifiedCoefficientwiseFrobeniusInv :
    RamifiedOverconvergentTateAlgebra k p w →+
      RamifiedOverconvergentTateAlgebra k p w where
  toFun g := ⟨ramifiedCoefficientwiseFrobeniusInvSeries k p w g.toSeries⟩
  map_zero' := OverconvergentTateAlgebra.ext <| by
    ext u
    exact map_zero (ramifiedCoefficientFrobenius k p).symm
  map_add' g h := OverconvergentTateAlgebra.ext <| by
    ext u
    exact map_add (ramifiedCoefficientFrobenius k p).symm (g.toSeries u) (h.toSeries u)
@[simp]
theorem ramifiedCoefficientwiseFrobeniusInv_coefficient
    (g : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u
        (ramifiedCoefficientwiseFrobeniusInv k p w g) =
      (ramifiedCoefficientFrobenius k p).symm
        (overconvergentTateAlgebraCoefficient w u g) :=
  rfl
 theorem overconvergentTateAlgebraCoefficient_mul
    (g h : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (g * h) =
      ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal u,
        overconvergentTateAlgebraCoefficient w uv.1 g *
          overconvergentTateAlgebraCoefficient w uv.2 h := by
  have hconvolution := seriesConvolution_weightedCoefficient
    w (1 : DworkCyclotomicField k p) g.toSeries h.toSeries u
  simpa [seriesConvolution, weightedCoefficient_apply,
    overconvergentTateAlgebraCoefficient_apply, seriesCoefficient_apply] using hconvolution
def dworkFrobenius (f : MonomialIndex d →₀ k)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    RamifiedOverconvergentTateAlgebra k p w :=
  ramifiedCoefficientwiseFrobeniusInv k p w
    (exponentDivision w p (teichmullerSplittingProduct k p w f * g))
theorem dworkFrobenius_coefficient (f : MonomialIndex d →₀ k)
    (g : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (dworkFrobenius k p w f g) =
      (ramifiedCoefficientFrobenius k p).symm
        (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (p • u),
          overconvergentTateAlgebraCoefficient w ab.1
              (teichmullerSplittingProduct k p w f) *
            overconvergentTateAlgebraCoefficient w ab.2 g) := by
  rw [dworkFrobenius, ramifiedCoefficientwiseFrobeniusInv_coefficient,
    exponentDivision_coefficient, overconvergentTateAlgebraCoefficient_mul]
  rfl
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Set Topology
open scoped Matrix.Norms.Elementwise
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
abbrev WeightedCutoff (bound : ℕ) := {u : MonomialIndex d // u ∈ MonomialCutoff w bound}
noncomputable instance weightedCutoffFinite (bound : ℕ) : Finite (WeightedCutoff w bound) := by
  letI := (finite_monomialCutoff w bound).fintype
  infer_instance
noncomputable instance weightedCutoffFintype (bound : ℕ) : Fintype (WeightedCutoff w bound) :=
  Fintype.ofFinite _
def weightedCutoffInclusion {smaller larger : ℕ} (h : smaller ≤ larger) :
    WeightedCutoff w smaller ↪ WeightedCutoff w larger where
  toFun u := ⟨u.1, u.2.trans h⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact congrArg (fun x : WeightedCutoff w larger ↦ x.1) huv
@[simp]
theorem weightedCutoffInclusion_val {smaller larger : ℕ} (h : smaller ≤ larger)
    (u : WeightedCutoff w smaller) :
    (weightedCutoffInclusion w h u).1 = u.1 :=
  rfl
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Set Topology
open scoped Matrix.Norms.Elementwise
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
def InfiniteWeightedKernel := MonomialIndex d → MonomialIndex d → K
def cutoffKernel (kernel : InfiniteWeightedKernel (K := K) (d := d)) (bound : ℕ) :
    Matrix (WeightedCutoff w bound) (WeightedCutoff w bound) K :=
  fun u v ↦ kernel u.1 v.1
omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
@[simp]
theorem cutoffKernel_apply (kernel : InfiniteWeightedKernel (K := K) (d := d)) (bound : ℕ)
    (u v : WeightedCutoff w bound) :
    cutoffKernel w kernel bound u v = kernel u.1 v.1 :=
  rfl
def KernelTailDecay (kernel : InfiniteWeightedKernel (K := K) (d := d))
    (tailBound : ℕ → ℝ) : Prop :=
  (∀ bound, 0 ≤ tailBound bound) ∧
    Tendsto tailBound atTop (nhds 0) ∧
    ∀ bound u v, bound < monomialWeight w u ∨ bound < monomialWeight w v →
      ‖kernel u v‖ ≤ tailBound bound
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Set Topology
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
def NuclearKernelDecay (kernel : InfiniteWeightedKernel (K := K) (d := d))
    (tailBound : ℕ → ℝ) : Prop :=
  KernelTailDecay w kernel tailBound ∧ ∀ u v, ‖kernel u v‖ ≤ 1
def finiteKernelPowerTrace (kernel : InfiniteWeightedKernel (K := K) (d := d))
    (power bound : ℕ) : K :=
  Matrix.trace ((cutoffKernel w kernel bound) ^ power)
 def nuclearWeightedCutoffOfLE {smaller larger : ℕ}
    (v : WeightedCutoff w larger) (hv : monomialWeight w v.1 ≤ smaller) :
    WeightedCutoff w smaller :=
  ⟨v.1, hv⟩
 def nuclearNestedWeightedCutoffEquiv {smaller larger : ℕ} (h : smaller ≤ larger) :
    WeightedCutoff w smaller ≃
      {v : WeightedCutoff w larger // monomialWeight w v.1 ≤ smaller} where
  toFun u := ⟨⟨u.1, u.2.trans h⟩, u.2⟩
  invFun v := nuclearWeightedCutoffOfLE w v.1 v.2
  left_inv _ := rfl
  right_inv _ := rfl
 def nuclearPaddedCutoffKernel
    (kernel : InfiniteWeightedKernel (K := K) (d := d)) (smaller larger : ℕ) :
    Matrix (WeightedCutoff w larger) (WeightedCutoff w larger) K :=
  fun u v ↦
    if _hu : monomialWeight w u.1 ≤ smaller then
      if _hv : monomialWeight w v.1 ≤ smaller then kernel u.1 v.1 else 0
    else 0
def nuclearTracePower
    (kernel : InfiniteWeightedKernel (K := K) (d := d)) (tailBound : ℕ → ℝ)
    (_hnuclear : NuclearKernelDecay w kernel tailBound)
    (power : ℕ) (_hpower : 0 < power) : K :=
  limUnder atTop (fun bound ↦ finiteKernelPowerTrace w kernel power bound)
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Set Topology
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
structure NuclearOperator where
  kernel : InfiniteWeightedKernel (K := K) (d := d)
  tailBound : ℕ → ℝ
  decay : NuclearKernelDecay w kernel tailBound
namespace NuclearOperator
def tracePower (T : NuclearOperator (K := K) w) (power : ℕ+) : K :=
  nuclearTracePower w T.kernel T.tailBound T.decay (power : ℕ) power.2
end NuclearOperator
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance dw5bResiduePrimeAlgebra : Algebra (ZMod p) k := ZMod.algebra k p
 def ramifiedFrobPow : ℕ → (DworkCyclotomicField k p →+* DworkCyclotomicField k p)
  | 0 => RingHom.id _
  | m + 1 => (ramifiedFrobPow m).comp (ramifiedCoefficientFrobenius k p).toRingHom
theorem dworkCyclotomicField_norm_p_lt_one : ‖(p : DworkCyclotomicField k p)‖ < 1 := by
  rw [show (p : DworkCyclotomicField k p)
      = algebraMap (CoefficientField k p) (DworkCyclotomicField k p) (p : CoefficientField k p) by
        simp,
    dworkCyclotomicField_norm_algebraMap]
  exact coefficientField_norm_p_lt_one k p
theorem dworkCyclotomicField_p_ne_zero : (p : DworkCyclotomicField k p) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
noncomputable instance dworkCyclotomicFieldNontriviallyNormedField :
    NontriviallyNormedField (DworkCyclotomicField k p) :=
  { (inferInstance : NormedField (DworkCyclotomicField k p)) with
    non_trivial := by
      refine ⟨(p : DworkCyclotomicField k p)⁻¹, ?_⟩
      rw [norm_inv]
      exact one_lt_inv_iff₀.mpr
        ⟨norm_pos_iff.mpr (dworkCyclotomicField_p_ne_zero k p),
          dworkCyclotomicField_norm_p_lt_one k p⟩ }
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance : Algebra (ZMod p) k := ZMod.algebra k p
variable {d : ℕ} (w : PositiveMonomialWeight d)
def dworkQFrobenius (f : MonomialIndex d →₀ k)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    RamifiedOverconvergentTateAlgebra k p w :=
  (dworkFrobenius k p w f)^[Module.finrank (ZMod p) k] g
def unitMonomial (v : MonomialIndex d) : RamifiedOverconvergentTateAlgebra k p w :=
  finsuppToOverconvergentTateAlgebra w (1 : DworkCyclotomicField k p) (Finsupp.single v 1)
@[simp]
theorem unitMonomial_coefficient (u v : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (unitMonomial k p w v)
      = if u = v then 1 else 0 := by
  rw [unitMonomial, overconvergentTateAlgebraCoefficient_apply, seriesCoefficient_apply,
    finsuppToOverconvergentTateAlgebra_toSeries, finsuppToOverconvergentSeries_apply]
  simp [Finsupp.single_apply, eq_comm]
def dworkQFrobeniusKernel (f : MonomialIndex d →₀ k) :
    InfiniteWeightedKernel (K := DworkCyclotomicField k p) (d := d) :=
  fun u v => overconvergentTateAlgebraCoefficient w u
    (dworkQFrobenius k p w f (unitMonomial k p w v))
theorem tate_one_eq_unitMonomial :
    (1 : RamifiedOverconvergentTateAlgebra k p w) = unitMonomial k p w 0 := rfl
@[simp]
theorem coefficient_one (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (1 : RamifiedOverconvergentTateAlgebra k p w)
      = if u = 0 then 1 else 0 := by
  rw [tate_one_eq_unitMonomial, unitMonomial_coefficient]
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance : Algebra (ZMod p) k := ZMod.algebra k p
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem norm_overconvergentTateAlgebraCoefficient_le (u : MonomialIndex d)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    ‖overconvergentTateAlgebraCoefficient w u g‖ ≤ ‖g‖ := by
  rw [overconvergentTateAlgebraCoefficient_apply, seriesCoefficient_apply,
    ← OverconvergentTateAlgebra.norm_toSeries,
    ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toSeries.toBCF _
def cyclotomicTeichmuller (a : k) : DworkCyclotomicField k p :=
  algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
    (coefficientRingAlgebraMap k p (teichmullerLift k p a))
theorem norm_cyclotomicTeichmuller_le_one (a : k) : ‖cyclotomicTeichmuller k p a‖ ≤ 1 := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  have hcard : a ^ Nat.card k = a := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  have hpow : cyclotomicTeichmuller k p a ^ Nat.card k = cyclotomicTeichmuller k p a := by
    simp only [cyclotomicTeichmuller]
    rw [← map_pow, ← map_pow, ← map_pow, hcard]
  by_contra hgt
  rw [not_le] at hgt
  have hcard1 : 1 < Nat.card k := Finite.one_lt_card
  have hlt : ‖cyclotomicTeichmuller k p a‖ < ‖cyclotomicTeichmuller k p a‖ ^ Nat.card k := by
    conv_lhs => rw [← pow_one ‖cyclotomicTeichmuller k p a‖]
    exact pow_lt_pow_right₀ hgt hcard1
  rw [← norm_pow, hpow] at hlt
  exact lt_irrefl _ hlt
theorem coefficient_mul (g h : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (g * h)
      = ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal u,
          overconvergentTateAlgebraCoefficient w xy.1 g *
            overconvergentTateAlgebraCoefficient w xy.2 h := by
  have hconvolution := seriesConvolution_weightedCoefficient
    w (1 : DworkCyclotomicField k p) g.toSeries h.toSeries u
  simpa [seriesConvolution, weightedCoefficient_apply,
    overconvergentTateAlgebraCoefficient_apply, seriesCoefficient_apply] using hconvolution
 theorem norm_sum_pow_le_of_forall {ι : Type*} (s : Finset ι)
    (g : ι → DworkCyclotomicField k p) {N : ℕ} (hN : N ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i ∈ s, ‖g i‖ ^ N ≤ C) : ‖∑ i ∈ s, g i‖ ^ N ≤ C := by
  have hroot : (0 : ℝ) ≤ C ^ ((N : ℝ)⁻¹) := Real.rpow_nonneg hC _
  have hpow : (C ^ ((N : ℝ)⁻¹)) ^ N = C := by
    rw [← Real.rpow_natCast (C ^ ((N : ℝ)⁻¹)) N, ← Real.rpow_mul hC,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN), Real.rpow_one]
  have hle : ∀ i ∈ s, ‖g i‖ ≤ C ^ ((N : ℝ)⁻¹) := by
    intro i hi
    refine le_of_pow_le_pow_left₀ hN hroot ?_
    rw [hpow]
    exact hbound i hi
  calc ‖∑ i ∈ s, g i‖ ^ N
      ≤ (C ^ ((N : ℝ)⁻¹)) ^ N :=
        pow_le_pow_left₀ (norm_nonneg _)
          (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hroot hle) N
    _ = C := hpow
def dworkSupportGauge (f : MonomialIndex d →₀ k) : ℕ :=
  max 1 (f.support.sup fun u ↦ monomialWeight w u)
omit [Finite k] in
theorem one_le_dworkSupportGauge (f : MonomialIndex d →₀ k) :
    1 ≤ dworkSupportGauge k w f :=
  le_max_left _ _
omit [Finite k] in
theorem dworkSupportGauge_pos (f : MonomialIndex d →₀ k) :
    0 < dworkSupportGauge k w f :=
  one_le_dworkSupportGauge k w f
omit [Finite k] in
theorem monomialWeight_le_dworkSupportGauge (f : MonomialIndex d →₀ k)
    {u : MonomialIndex d} (hu : u ∈ f.support) :
    monomialWeight w u ≤ dworkSupportGauge k w f :=
  le_max_of_le_right (Finset.le_sup hu)
def gaugeCeil (x g : ℕ) : ℕ := (x + g - 1) / g
@[simp]
theorem gaugeCeil_zero (g : ℕ) : gaugeCeil 0 g = 0 := by
  rcases Nat.eq_zero_or_pos g with hg | hg
  · simp [gaugeCeil, hg]
  · simpa [gaugeCeil] using Nat.div_eq_of_lt (by omega)
theorem gaugeCeil_le_iff {g : ℕ} (hg : 0 < g) (x n : ℕ) :
    gaugeCeil x g ≤ n ↔ x ≤ n * g := by
  rw [gaugeCeil, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hg, Nat.succ_mul]
  omega
theorem le_mul_gaugeCeil {g : ℕ} (hg : 0 < g) (x : ℕ) : x ≤ g * gaugeCeil x g := by
  rw [mul_comm]
  exact (gaugeCeil_le_iff hg x (gaugeCeil x g)).mp le_rfl
theorem gaugeCeil_add_le {g : ℕ} (hg : 0 < g) (x y : ℕ) :
    gaugeCeil (x + y) g ≤ gaugeCeil x g + gaugeCeil y g := by
  rw [gaugeCeil_le_iff hg, add_mul]
  have hx := (gaugeCeil_le_iff hg x (gaugeCeil x g)).mp le_rfl
  have hy := (gaugeCeil_le_iff hg y (gaugeCeil y g)).mp le_rfl
  omega
theorem norm_dworkMonomialSplittingFactor_coefficient_le
    (a : k) (u₀ c : MonomialIndex d) {g : ℕ} (hg : 0 < g)
    (hu₀ : monomialWeight w u₀ ≤ g) :
    ‖overconvergentTateAlgebraCoefficient w c (dworkMonomialSplittingFactor k p w a u₀)‖
      ≤ ‖dworkArtinHasseParameter k p‖ ^ gaugeCeil (monomialWeight w c) g := by
  classical
  by_cases hray : ∃ m : ℕ, m • u₀ = c
  · obtain ⟨m, rfl⟩ := hray
    by_cases hzero : u₀ = 0
    · subst hzero
      rw [smul_zero, monomialWeight_zero, gaugeCeil_zero, pow_zero]
      exact (norm_overconvergentTateAlgebraCoefficient_le k p w 0 _).trans
        (dworkMonomialSplittingFactor_norm_le_one k p w a 0)
    · rw [dworkMonomialSplittingFactor_coefficient_on_ray k p w a hzero m]
      have hterm :
          ‖PowerSeries.coeff m (dworkSplittingFunction k p) *
              cyclotomicTeichmuller k p a ^ m‖
            ≤ ‖dworkArtinHasseParameter k p‖ ^ m := by
        rw [norm_mul, norm_pow]
        calc ‖PowerSeries.coeff m (dworkSplittingFunction k p)‖ *
              ‖cyclotomicTeichmuller k p a‖ ^ m
            ≤ ‖dworkArtinHasseParameter k p‖ ^ m * 1 :=
              mul_le_mul (dworkSplittingFunction_coeff_norm_le k p m)
                (pow_le_one₀ (norm_nonneg _) (norm_cyclotomicTeichmuller_le_one k p a))
                (by positivity) (by positivity)
          _ = ‖dworkArtinHasseParameter k p‖ ^ m := mul_one _
      refine hterm.trans (pow_le_pow_of_le_one (norm_nonneg _)
        (dworkArtinHasseParameter_norm_lt_one k p).le ?_)
      rw [gaugeCeil_le_iff hg, map_nsmul, smul_eq_mul]
      exact Nat.mul_le_mul_left m hu₀
  · rw [dworkMonomialSplittingFactor_coefficient_off_ray k p w a u₀ c
      (fun n hn ↦ hray ⟨n, hn⟩), norm_zero]
    positivity
 theorem norm_prod_dworkMonomialSplittingFactor_coefficient_le
    (f : MonomialIndex d →₀ k) {g : ℕ} (hg : 0 < g) (s : Finset (MonomialIndex d)) :
    (∀ u ∈ s, monomialWeight w u ≤ g) → ∀ c : MonomialIndex d,
      ‖overconvergentTateAlgebraCoefficient w c
          (∏ u ∈ s, dworkMonomialSplittingFactor k p w (f u) u)‖
        ≤ ‖dworkArtinHasseParameter k p‖ ^ gaugeCeil (monomialWeight w c) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ c
      rw [Finset.prod_empty, coefficient_one]
      split_ifs with hc
      · subst hc
        simp
      · rw [norm_zero]
        positivity
  | @insert u₀ s hu₀ ih =>
      intro hs c
      have hs₀ : monomialWeight w u₀ ≤ g := hs u₀ (Finset.mem_insert_self u₀ s)
      have hsrest : ∀ u ∈ s, monomialWeight w u ≤ g :=
        fun u hu ↦ hs u (Finset.mem_insert_of_mem hu)
      rw [Finset.prod_insert hu₀, coefficient_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
      rintro ⟨x, y⟩ hxy
      have hsum : x + y = c := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
      rw [norm_mul]
      calc ‖overconvergentTateAlgebraCoefficient w x
              (dworkMonomialSplittingFactor k p w (f u₀) u₀)‖ *
            ‖overconvergentTateAlgebraCoefficient w y
              (∏ v ∈ s, dworkMonomialSplittingFactor k p w (f v) v)‖
          ≤ ‖dworkArtinHasseParameter k p‖ ^ gaugeCeil (monomialWeight w x) g *
              ‖dworkArtinHasseParameter k p‖ ^ gaugeCeil (monomialWeight w y) g :=
            mul_le_mul
              (norm_dworkMonomialSplittingFactor_coefficient_le k p w (f u₀) u₀ x hg hs₀)
              (ih hsrest y) (norm_nonneg _) (by positivity)
        _ = ‖dworkArtinHasseParameter k p‖ ^
              (gaugeCeil (monomialWeight w x) g + gaugeCeil (monomialWeight w y) g) :=
            (pow_add _ _ _).symm
        _ ≤ ‖dworkArtinHasseParameter k p‖ ^ gaugeCeil (monomialWeight w c) g := by
            refine pow_le_pow_of_le_one (norm_nonneg _)
              (dworkArtinHasseParameter_norm_lt_one k p).le ?_
            rw [← hsum, monomialWeight_add]
            exact gaugeCeil_add_le hg _ _
theorem norm_teichmullerSplittingProduct_coefficient_le
    (f : MonomialIndex d →₀ k) (c : MonomialIndex d) :
    ‖overconvergentTateAlgebraCoefficient w c (teichmullerSplittingProduct k p w f)‖
      ≤ ‖dworkArtinHasseParameter k p‖ ^
          gaugeCeil (monomialWeight w c) (dworkSupportGauge k w f) :=
  norm_prod_dworkMonomialSplittingFactor_coefficient_le k p w f
    (dworkSupportGauge_pos k w f) f.support
    (fun _ hu ↦ monomialWeight_le_dworkSupportGauge k w f hu) c
theorem norm_teichmullerSplittingProduct_coefficient_pow_le
    (f : MonomialIndex d →₀ k) (c : MonomialIndex d) (N : ℕ) :
    ‖overconvergentTateAlgebraCoefficient w c (teichmullerSplittingProduct k p w f)‖ ^
        (dworkSupportGauge k w f * N)
      ≤ ‖dworkArtinHasseParameter k p‖ ^ (monomialWeight w c * N) := by
  have hbase := norm_teichmullerSplittingProduct_coefficient_le k p w f c
  calc ‖overconvergentTateAlgebraCoefficient w c (teichmullerSplittingProduct k p w f)‖ ^
        (dworkSupportGauge k w f * N)
      ≤ (‖dworkArtinHasseParameter k p‖ ^
          gaugeCeil (monomialWeight w c) (dworkSupportGauge k w f)) ^
            (dworkSupportGauge k w f * N) :=
        pow_le_pow_left₀ (norm_nonneg _) hbase _
    _ = ‖dworkArtinHasseParameter k p‖ ^
          (dworkSupportGauge k w f * gaugeCeil (monomialWeight w c)
            (dworkSupportGauge k w f) * N) := by
        rw [← pow_mul]
        ring_nf
    _ ≤ ‖dworkArtinHasseParameter k p‖ ^ (monomialWeight w c * N) := by
        refine pow_le_pow_of_le_one (norm_nonneg _)
          (dworkArtinHasseParameter_norm_lt_one k p).le ?_
        exact Nat.mul_le_mul_right N
          (le_mul_gaugeCeil (dworkSupportGauge_pos k w f) (monomialWeight w c))
 theorem gauge_step_arith {X Y Z β m : ℕ} (hm : 0 < m) (hZ : Z = X + Y) :
    Z - β ≤ X + m * (Y - β) := by
  have hle : Y - β ≤ m * (Y - β) := Nat.le_mul_of_pos_left _ hm
  omega
 theorem norm_dworkFrobenius_coefficient_step
    (f : MonomialIndex d →₀ k) (h : RamifiedOverconvergentTateAlgebra k p w) (r β : ℕ)
    (hh : ∀ y : MonomialIndex d,
      ‖overconvergentTateAlgebraCoefficient w y h‖ ^ (dworkSupportGauge k w f * p ^ r)
        ≤ ‖dworkArtinHasseParameter k p‖ ^ (p ^ (r + 1) * monomialWeight w y - β))
    (u : MonomialIndex d) :
    ‖overconvergentTateAlgebraCoefficient w u (dworkFrobenius k p w f h)‖ ^
        (dworkSupportGauge k w f * p ^ (r + 1))
      ≤ ‖dworkArtinHasseParameter k p‖ ^ (p ^ (r + 2) * monomialWeight w u - β) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hppow : 0 < p ^ (r + 1) := pow_pos hp _
  have hN : dworkSupportGauge k w f * p ^ (r + 1) ≠ 0 :=
    Nat.mul_ne_zero (dworkSupportGauge_pos k w f).ne' hppow.ne'
  rw [dworkFrobenius_coefficient, ramifiedCoefficientFrobenius_symm_norm]
  refine norm_sum_pow_le_of_forall k p _ _ hN (by positivity) ?_
  rintro ⟨x, y⟩ hxy
  have hsum : x + y = p • u := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
  have hweight : monomialWeight w x + monomialWeight w y = p * monomialWeight w u := by
    rw [← monomialWeight_add, hsum, map_nsmul, smul_eq_mul]
  have hfactor :
      ‖overconvergentTateAlgebraCoefficient w x (teichmullerSplittingProduct k p w f)‖ ^
          (dworkSupportGauge k w f * p ^ (r + 1))
        ≤ ‖dworkArtinHasseParameter k p‖ ^ (monomialWeight w x * p ^ (r + 1)) :=
    norm_teichmullerSplittingProduct_coefficient_pow_le k p w f x (p ^ (r + 1))
  have hinput :
      ‖overconvergentTateAlgebraCoefficient w y h‖ ^
          (dworkSupportGauge k w f * p ^ (r + 1))
        ≤ ‖dworkArtinHasseParameter k p‖ ^
            (p * (p ^ (r + 1) * monomialWeight w y - β)) := by
    have hsplit : dworkSupportGauge k w f * p ^ (r + 1)
        = dworkSupportGauge k w f * p ^ r * p := by ring
    rw [hsplit, pow_mul]
    calc (‖overconvergentTateAlgebraCoefficient w y h‖ ^
            (dworkSupportGauge k w f * p ^ r)) ^ p
        ≤ (‖dworkArtinHasseParameter k p‖ ^
            (p ^ (r + 1) * monomialWeight w y - β)) ^ p :=
          pow_le_pow_left₀ (by positivity) (hh y) p
      _ = ‖dworkArtinHasseParameter k p‖ ^
            (p * (p ^ (r + 1) * monomialWeight w y - β)) := by
          rw [← pow_mul, Nat.mul_comm]
  have harith : p ^ (r + 2) * monomialWeight w u - β
      ≤ monomialWeight w x * p ^ (r + 1) + p * (p ^ (r + 1) * monomialWeight w y - β) := by
    refine gauge_step_arith hp ?_
    calc p ^ (r + 2) * monomialWeight w u = p ^ (r + 1) * (p * monomialWeight w u) := by ring
      _ = p ^ (r + 1) * (monomialWeight w x + monomialWeight w y) := by rw [hweight]
      _ = monomialWeight w x * p ^ (r + 1) + p ^ (r + 1) * monomialWeight w y := by ring
  rw [norm_mul, mul_pow]
  calc ‖overconvergentTateAlgebraCoefficient w x (teichmullerSplittingProduct k p w f)‖ ^
          (dworkSupportGauge k w f * p ^ (r + 1)) *
        ‖overconvergentTateAlgebraCoefficient w y h‖ ^
          (dworkSupportGauge k w f * p ^ (r + 1))
      ≤ ‖dworkArtinHasseParameter k p‖ ^ (monomialWeight w x * p ^ (r + 1)) *
          ‖dworkArtinHasseParameter k p‖ ^
            (p * (p ^ (r + 1) * monomialWeight w y - β)) :=
        mul_le_mul hfactor hinput (by positivity) (by positivity)
    _ = ‖dworkArtinHasseParameter k p‖ ^
          (monomialWeight w x * p ^ (r + 1) +
            p * (p ^ (r + 1) * monomialWeight w y - β)) := (pow_add _ _ _).symm
    _ ≤ ‖dworkArtinHasseParameter k p‖ ^ (p ^ (r + 2) * monomialWeight w u - β) :=
        pow_le_pow_of_le_one (norm_nonneg _)
          (dworkArtinHasseParameter_norm_lt_one k p).le harith
 theorem norm_dworkFrobenius_iterate_unitMonomial_coefficient
    (f : MonomialIndex d →₀ k) (v : MonomialIndex d) (r : ℕ) (u : MonomialIndex d) :
    ‖overconvergentTateAlgebraCoefficient w u
        ((dworkFrobenius k p w f)^[r] (unitMonomial k p w v))‖ ^
        (dworkSupportGauge k w f * p ^ r)
      ≤ ‖dworkArtinHasseParameter k p‖ ^
          (p ^ (r + 1) * monomialWeight w u - p * monomialWeight w v) := by
  induction r generalizing u with
  | zero =>
      rw [Function.iterate_zero_apply, unitMonomial_coefficient]
      split_ifs with hu
      · subst hu
        simp
      · rw [norm_zero, zero_pow (Nat.mul_ne_zero (dworkSupportGauge_pos k w f).ne' (by simp))]
        positivity
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact norm_dworkFrobenius_coefficient_step k p w f _ r _ ih u
theorem norm_dworkQFrobeniusKernel_pow_le (f : MonomialIndex d →₀ k) (u v : MonomialIndex d) :
    ‖dworkQFrobeniusKernel k p w f u v‖ ^
        (dworkSupportGauge k w f * p ^ Module.finrank (ZMod p) k)
      ≤ ‖dworkArtinHasseParameter k p‖ ^
          (p ^ (Module.finrank (ZMod p) k + 1) * monomialWeight w u -
            p * monomialWeight w v) :=
  norm_dworkFrobenius_iterate_unitMonomial_coefficient k p w f v _ u
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance : Algebra (ZMod p) k := ZMod.algebra k p
variable {d : ℕ} (w : PositiveMonomialWeight d)
def conjugateKernel (c : DworkCyclotomicField k p) (n : MonomialIndex d → ℕ)
    (kernel : InfiniteWeightedKernel (K := DworkCyclotomicField k p) (d := d)) :
    InfiniteWeightedKernel (K := DworkCyclotomicField k p) (d := d) :=
  fun u v => c ^ n v * (c ^ n u)⁻¹ * kernel u v
theorem norm_conjugateKernel (c : DworkCyclotomicField k p) (n : MonomialIndex d → ℕ)
    (kernel : InfiniteWeightedKernel (K := DworkCyclotomicField k p) (d := d))
    (u v : MonomialIndex d) :
    ‖conjugateKernel k p c n kernel u v‖
      = ‖c‖ ^ n v * (‖c‖ ^ n u)⁻¹ * ‖kernel u v‖ := by
  rw [conjugateKernel, norm_mul, norm_mul, norm_pow, norm_inv, norm_pow]
theorem two_le_qCard : 2 ≤ p ^ Module.finrank (ZMod p) k := by
  rw [FiniteField.pow_finrank_eq_natCard]
  exact Finite.one_lt_card
theorem norm_dworkArtinHasseParameter_le_ramification :
    ‖dworkArtinHasseParameter k p‖ ≤ ‖dworkRamificationParameter k p‖ :=
  (existsUnique_dworkArtinHasseParameter k p).choose_spec.1.1
def dworkQGauge (f : MonomialIndex d →₀ k) : ℕ :=
  dworkSupportGauge k w f * p ^ Module.finrank (ZMod p) k
omit [Finite k] in
theorem dworkQGauge_pos (f : MonomialIndex d →₀ k) : 0 < dworkQGauge k p w f :=
  Nat.mul_pos (dworkSupportGauge_pos k w f) (pow_pos (Fact.out : p.Prime).pos _)
theorem norm_dworkQFrobeniusKernel_gauge_le (f : MonomialIndex d →₀ k) (u v : MonomialIndex d) :
    ‖dworkQFrobeniusKernel k p w f u v‖ ^ dworkQGauge k p w f
      ≤ ‖dworkRamificationParameter k p‖ ^
          (p ^ (Module.finrank (ZMod p) k + 1) * monomialWeight w u -
            p * monomialWeight w v) :=
  (norm_dworkQFrobeniusKernel_pow_le k p w f u v).trans
    (pow_le_pow_left₀ (norm_nonneg _)
      (norm_dworkArtinHasseParameter_le_ramification k p) _)
def dworkQDiagonalExponent (f : MonomialIndex d →₀ k) (u : MonomialIndex d) : ℕ :=
  (3 * (p * monomialWeight w u) - dworkQGauge k p w f) / (2 * dworkQGauge k p w f)
omit [Finite k] in
theorem dworkQDiagonalExponent_mul_le (f : MonomialIndex d →₀ k) (u : MonomialIndex d) :
    dworkQDiagonalExponent k p w f u * (2 * dworkQGauge k p w f)
      ≤ 3 * (p * monomialWeight w u) - dworkQGauge k p w f :=
  Nat.div_mul_le_self _ _
omit [Finite k] in
theorem lt_dworkQDiagonalExponent_succ_mul (f : MonomialIndex d →₀ k) (u : MonomialIndex d) :
    3 * (p * monomialWeight w u) - dworkQGauge k p w f
      < (dworkQDiagonalExponent k p w f u + 1) * (2 * dworkQGauge k p w f) :=
  (Nat.div_lt_iff_lt_mul (by have := dworkQGauge_pos k p w f; omega)).mp (Nat.lt_succ_self _)
omit [Finite k] in
theorem dworkQDiagonalExponent_bracket (f : MonomialIndex d →₀ k) (u : MonomialIndex d) :
    2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f)
        ≤ 3 * (p * monomialWeight w u) ∧
      3 * (p * monomialWeight w u)
        < 2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f)
          + 3 * dworkQGauge k p w f := by
  have hlow := dworkQDiagonalExponent_mul_le k p w f u
  have hhigh := lt_dworkQDiagonalExponent_succ_mul k p w f u
  have hGpos := dworkQGauge_pos k p w f
  have hl : dworkQDiagonalExponent k p w f u * (2 * dworkQGauge k p w f)
      = 2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f) := by ring
  have hh : (dworkQDiagonalExponent k p w f u + 1) * (2 * dworkQGauge k p w f)
      = 2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f)
        + 2 * dworkQGauge k p w f := by ring
  rw [hl] at hlow
  rw [hh] at hhigh
  omega
omit [Finite k] in
theorem dworkQDiagonalExponent_sharp (f : MonomialIndex d →₀ k) (u : MonomialIndex d)
    (hpos : 0 < dworkQDiagonalExponent k p w f u) :
    2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f) + dworkQGauge k p w f
      ≤ 3 * (p * monomialWeight w u) := by
  have hlow := dworkQDiagonalExponent_mul_le k p w f u
  have hGpos := dworkQGauge_pos k p w f
  have hl : dworkQDiagonalExponent k p w f u * (2 * dworkQGauge k p w f)
      = 2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f) := by ring
  have hge : dworkQGauge k p w f
      ≤ dworkQDiagonalExponent k p w f u * dworkQGauge k p w f :=
    Nat.le_mul_of_pos_left _ hpos
  rw [hl] at hlow
  omega
def dworkQFrobeniusNormalizedKernel (f : MonomialIndex d →₀ k) :
    InfiniteWeightedKernel (K := DworkCyclotomicField k p) (d := d) :=
  conjugateKernel k p (dworkRamificationParameter k p) (dworkQDiagonalExponent k p w f)
    (dworkQFrobeniusKernel k p w f)
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance : Algebra (ZMod p) k := ZMod.algebra k p
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem norm_dworkQFrobeniusNormalizedKernel_le (f : MonomialIndex d →₀ k)
    (u v : MonomialIndex d) (e : ℕ)
    (he : (e + dworkQDiagonalExponent k p w f u) * dworkQGauge k p w f
        ≤ dworkQDiagonalExponent k p w f v * dworkQGauge k p w f
          + (p ^ (Module.finrank (ZMod p) k + 1) * monomialWeight w u -
              p * monomialWeight w v)) :
    ‖dworkQFrobeniusNormalizedKernel k p w f u v‖
      ≤ ‖dworkRamificationParameter k p‖ ^ e := by
  have hGpos := dworkQGauge_pos k p w f
  have hpos : (0 : ℝ) < ‖dworkRamificationParameter k p‖ :=
    norm_pos_iff.mpr (dworkRamificationParameter_ne_zero k p)
  have hle1 : ‖dworkRamificationParameter k p‖ ≤ 1 :=
    (dworkRamificationParameter_norm_lt_one k p).le
  have hK := norm_dworkQFrobeniusKernel_gauge_le k p w f u v
  have hden : ((‖dworkRamificationParameter k p‖ ^
      (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f)) : ℝ) ≠ 0 := by positivity
  refine le_of_pow_le_pow_left₀ hGpos.ne' (by positivity) ?_
  rw [dworkQFrobeniusNormalizedKernel, norm_conjugateKernel, mul_pow, mul_pow,
    inv_pow, ← pow_mul, ← pow_mul]
  calc ‖dworkRamificationParameter k p‖ ^
          (dworkQDiagonalExponent k p w f v * dworkQGauge k p w f) *
        (‖dworkRamificationParameter k p‖ ^
          (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f))⁻¹ *
        ‖dworkQFrobeniusKernel k p w f u v‖ ^ dworkQGauge k p w f
      ≤ ‖dworkRamificationParameter k p‖ ^
          (dworkQDiagonalExponent k p w f v * dworkQGauge k p w f) *
        (‖dworkRamificationParameter k p‖ ^
          (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f))⁻¹ *
        ‖dworkRamificationParameter k p‖ ^
          (p ^ (Module.finrank (ZMod p) k + 1) * monomialWeight w u -
            p * monomialWeight w v) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
    _ = ‖dworkRamificationParameter k p‖ ^
          (dworkQDiagonalExponent k p w f v * dworkQGauge k p w f +
            (p ^ (Module.finrank (ZMod p) k + 1) * monomialWeight w u -
              p * monomialWeight w v)) *
        (‖dworkRamificationParameter k p‖ ^
          (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f))⁻¹ := by
        rw [pow_add]; ring
    _ ≤ ‖dworkRamificationParameter k p‖ ^
          ((e + dworkQDiagonalExponent k p w f u) * dworkQGauge k p w f) *
        (‖dworkRamificationParameter k p‖ ^
          (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f))⁻¹ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hpos.le hle1 he) (by positivity)
    _ = (‖dworkRamificationParameter k p‖ ^ e) ^ dworkQGauge k p w f := by
        rw [add_mul, pow_add, mul_assoc, mul_inv_cancel₀ hden, mul_one, pow_mul]
 theorem gauge_unit_arith {tG sG G Q qP qtG qG : ℕ}
    (hlow : 2 * qtG + qG ≤ 3 * qP) (hqa : 2 * tG ≤ qtG) (hqG : 2 * G ≤ qG)
    (hv : 3 * Q < 2 * sG + 3 * G) (hgap : sG + G ≤ tG) :
    tG ≤ sG + (qP - Q) := by omega
theorem norm_dworkQFrobeniusNormalizedKernel_le_one (f : MonomialIndex d →₀ k)
    (u v : MonomialIndex d) :
    ‖dworkQFrobeniusNormalizedKernel k p w f u v‖ ≤ 1 := by
  have h := norm_dworkQFrobeniusNormalizedKernel_le k p w f u v 0 ?_
  · rwa [pow_zero] at h
  · have hq := two_le_qCard k p
    have hGpos := dworkQGauge_pos k p w f
    rw [Nat.zero_add]
    rcases le_or_gt (dworkQDiagonalExponent k p w f u)
      (dworkQDiagonalExponent k p w f v) with hts | hts
    · exact le_trans (Nat.mul_le_mul_right _ hts) (Nat.le_add_right _ _)
    · have hsharp := dworkQDiagonalExponent_sharp k p w f u (by omega)
      have hvb := (dworkQDiagonalExponent_bracket k p w f v).2
      have hqmul := Nat.mul_le_mul_left (p ^ Module.finrank (ZMod p) k) hsharp
      have hLq : p ^ Module.finrank (ZMod p) k *
            (2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f)
              + dworkQGauge k p w f)
          = 2 * (p ^ Module.finrank (ZMod p) k *
              (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f))
            + p ^ Module.finrank (ZMod p) k * dworkQGauge k p w f := by ring
      have hRq : p ^ Module.finrank (ZMod p) k * (3 * (p * monomialWeight w u))
          = 3 * (p ^ (Module.finrank (ZMod p) k + 1) * monomialWeight w u) := by ring
      rw [hLq, hRq] at hqmul
      have hqa : 2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f)
          ≤ p ^ Module.finrank (ZMod p) k *
              (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f) :=
        Nat.mul_le_mul_right _ hq
      have hqG : 2 * dworkQGauge k p w f
          ≤ p ^ Module.finrank (ZMod p) k * dworkQGauge k p w f :=
        Nat.mul_le_mul_right _ hq
      have hgap : dworkQDiagonalExponent k p w f v * dworkQGauge k p w f + dworkQGauge k p w f
          ≤ dworkQDiagonalExponent k p w f u * dworkQGauge k p w f := by
        have hle : (dworkQDiagonalExponent k p w f v + 1) * dworkQGauge k p w f
            ≤ dworkQDiagonalExponent k p w f u * dworkQGauge k p w f :=
          Nat.mul_le_mul_right _ hts
        have hexp : (dworkQDiagonalExponent k p w f v + 1) * dworkQGauge k p w f
            = dworkQDiagonalExponent k p w f v * dworkQGauge k p w f
              + dworkQGauge k p w f := by ring
        omega
      exact gauge_unit_arith hqmul hqa hqG hvb hgap
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance : Algebra (ZMod p) k := ZMod.algebra k p
variable {d : ℕ} (w : PositiveMonomialWeight d)
def dworkQTailExponent (f : MonomialIndex d →₀ k) (bound : ℕ) : ℕ :=
  (bound + 1) / (2 * dworkQGauge k p w f) - 2
def dworkQFrobeniusTailBound (f : MonomialIndex d →₀ k) (bound : ℕ) : ℝ :=
  ‖dworkRamificationParameter k p‖ ^ dworkQTailExponent k p w f bound
theorem dworkQFrobeniusTailBound_nonneg (f : MonomialIndex d →₀ k) (bound : ℕ) :
    0 ≤ dworkQFrobeniusTailBound k p w f bound := by
  rw [dworkQFrobeniusTailBound]
  positivity
omit [Finite k] in
theorem dworkQTailExponent_tendsto (f : MonomialIndex d →₀ k) :
    Tendsto (dworkQTailExponent k p w f) atTop atTop := by
  have hGpos := dworkQGauge_pos k p w f
  refine Filter.tendsto_atTop_atTop.mpr fun N => ⟨2 * dworkQGauge k p w f * (N + 2), ?_⟩
  intro b hb
  have hdiv : N + 2 ≤ (b + 1) / (2 * dworkQGauge k p w f) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc (N + 2) * (2 * dworkQGauge k p w f)
        = 2 * dworkQGauge k p w f * (N + 2) := by ring
      _ ≤ b := hb
      _ ≤ b + 1 := Nat.le_succ b
  rw [dworkQTailExponent]
  omega
theorem dworkQFrobeniusTailBound_tendsto (f : MonomialIndex d →₀ k) :
    Tendsto (dworkQFrobeniusTailBound k p w f) atTop (nhds 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
    (dworkRamificationParameter_norm_lt_one k p)).comp (dworkQTailExponent_tendsto k p w f)
omit [Finite k] in
theorem dworkQTailExponent_spec (f : MonomialIndex d →₀ k) (bound : ℕ) :
    dworkQTailExponent k p w f bound = 0 ∨
      2 * dworkQGauge k p w f * (dworkQTailExponent k p w f bound + 2) ≤ bound + 1 := by
  have hGpos := dworkQGauge_pos k p w f
  rcases le_or_gt ((bound + 1) / (2 * dworkQGauge k p w f)) 1 with hc | hc
  · left
    rw [dworkQTailExponent]
    omega
  · right
    have hkey : (bound + 1) / (2 * dworkQGauge k p w f) * (2 * dworkQGauge k p w f) ≤ bound + 1 :=
      Nat.div_mul_le_self _ _
    have hsucc : dworkQTailExponent k p w f bound + 2
        = (bound + 1) / (2 * dworkQGauge k p w f) := by
      rw [dworkQTailExponent]
      omega
    rw [hsucc]
    calc 2 * dworkQGauge k p w f * ((bound + 1) / (2 * dworkQGauge k p w f))
        = (bound + 1) / (2 * dworkQGauge k p w f) * (2 * dworkQGauge k p w f) := by ring
      _ ≤ bound + 1 := hkey
 theorem gauge_cross_arith {tG sG G D P Q qP qtG : ℕ}
    (hPhigh : 3 * P < 2 * tG + 3 * G)
    (hQhigh : 3 * Q < 2 * sG + 3 * G)
    (hqlow : 2 * qtG ≤ 3 * qP) (hqa : 2 * tG ≤ qtG)
    (hcross : 2 * D + 4 * G ≤ P + Q) :
    D + tG ≤ sG + (qP - Q) := by omega
theorem norm_dworkQFrobeniusNormalizedKernel_cross_le (f : MonomialIndex d →₀ k) (bound : ℕ)
    (u v : MonomialIndex d)
    (hcross : bound < monomialWeight w u ∨ bound < monomialWeight w v) :
    ‖dworkQFrobeniusNormalizedKernel k p w f u v‖ ≤ dworkQFrobeniusTailBound k p w f bound := by
  rcases dworkQTailExponent_spec k p w f bound with hzero | hspec
  · rw [dworkQFrobeniusTailBound, hzero, pow_zero]
    exact norm_dworkQFrobeniusNormalizedKernel_le_one k p w f u v
  rw [dworkQFrobeniusTailBound]
  refine norm_dworkQFrobeniusNormalizedKernel_le k p w f u v _ ?_
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hq := two_le_qCard k p
  have hGpos := dworkQGauge_pos k p w f
  have hub := dworkQDiagonalExponent_bracket k p w f u
  have hvb := dworkQDiagonalExponent_bracket k p w f v
  have hqmul := Nat.mul_le_mul_left (p ^ Module.finrank (ZMod p) k) hub.1
  have hLq : p ^ Module.finrank (ZMod p) k *
        (2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f))
      = 2 * (p ^ Module.finrank (ZMod p) k *
          (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f)) := by ring
  have hRq : p ^ Module.finrank (ZMod p) k * (3 * (p * monomialWeight w u))
      = 3 * (p ^ (Module.finrank (ZMod p) k + 1) * monomialWeight w u) := by ring
  rw [hLq, hRq] at hqmul
  have hqa : 2 * (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f)
      ≤ p ^ Module.finrank (ZMod p) k *
          (dworkQDiagonalExponent k p w f u * dworkQGauge k p w f) :=
    Nat.mul_le_mul_right _ hq
  have hcrosssum : 2 * (dworkQTailExponent k p w f bound * dworkQGauge k p w f)
      + 4 * dworkQGauge k p w f
      ≤ p * monomialWeight w u + p * monomialWeight w v := by
    have hexp : 2 * dworkQGauge k p w f * (dworkQTailExponent k p w f bound + 2)
        = 2 * (dworkQTailExponent k p w f bound * dworkQGauge k p w f)
          + 4 * dworkQGauge k p w f := by ring
    have hbu : 1 * monomialWeight w u ≤ p * monomialWeight w u :=
      Nat.mul_le_mul_right _ hp1
    have hbv : 1 * monomialWeight w v ≤ p * monomialWeight w v :=
      Nat.mul_le_mul_right _ hp1
    rcases hcross with hcu | hcv
    · omega
    · omega
  rw [add_mul]
  exact gauge_cross_arith hub.2 hvb.2 hqmul hqa hcrosssum
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem dworkQFrobeniusKernel_decay (f : MonomialIndex d →₀ k) :
    NuclearKernelDecay w (dworkQFrobeniusNormalizedKernel k p w f)
      (dworkQFrobeniusTailBound k p w f) :=
  ⟨⟨dworkQFrobeniusTailBound_nonneg k p w f, dworkQFrobeniusTailBound_tendsto k p w f,
      fun bound u v hcross =>
        norm_dworkQFrobeniusNormalizedKernel_cross_le k p w f bound u v hcross⟩,
    fun u v => norm_dworkQFrobeniusNormalizedKernel_le_one k p w f u v⟩
def dworkQFrobeniusNuclearOperator (f : MonomialIndex d →₀ k) :
    NuclearOperator (K := DworkCyclotomicField k p) w where
  kernel := dworkQFrobeniusNormalizedKernel k p w f
  tailBound := dworkQFrobeniusTailBound k p w f
  decay := dworkQFrobeniusKernel_decay k p w f
@[simp]
theorem dworkQFrobeniusNuclearOperator_kernel (f : MonomialIndex d →₀ k) :
    (dworkQFrobeniusNuclearOperator k p w f).kernel
      = dworkQFrobeniusNormalizedKernel k p w f := rfl
end FiniteFields.Dwork
end
end

section
noncomputable section
namespace FiniteFields.Dwork
open Finset
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
  [Algebra (ZMod p) k]
section PrimeFieldMap
def wittPrimeFieldMap : CoefficientRing (ZMod p) p →+* CoefficientRing k p :=
  WittVector.map (algebraMap (ZMod p) k)
omit [CharP k p] [Finite k] in
@[simp]
theorem wittPrimeFieldMap_coeff (w : CoefficientRing (ZMod p) p) (n : ℕ) :
    (wittPrimeFieldMap k p w).coeff n = algebraMap (ZMod p) k (w.coeff n) :=
  rfl
omit [CharP k p] [Finite k] in
theorem wittPrimeFieldMap_injective : Function.Injective (wittPrimeFieldMap k p) :=
  WittVector.map_injective _ (algebraMap (ZMod p) k).injective
end PrimeFieldMap
section FixedPoints
omit [Finite k] in
theorem pow_eq_self_iff_mem_range {x : k} :
    x ^ p = x ↔ ∃ a : ZMod p, algebraMap (ZMod p) k a = x := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p k).1 ((Subfield.mem_bot_iff_pow_eq_self k p).2 hx)
    exact ⟨(n : ZMod p), by rw [map_intCast]; exact hn⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, ZMod.pow_card]
omit [Finite k] in
@[simp]
theorem frobeniusLift_wittPrimeFieldMap (w : CoefficientRing (ZMod p) p) :
    frobeniusLift k p (wittPrimeFieldMap k p w) = wittPrimeFieldMap k p w := by
  ext n
  rw [frobeniusLift, WittVector.coeff_frobenius_charP, wittPrimeFieldMap_coeff, ← map_pow,
    ZMod.pow_card]
def wittPrimeFieldFixedEquiv :
    CoefficientRing (ZMod p) p ≃ {x : CoefficientRing k p // frobeniusLift k p x = x} where
  toFun w := ⟨wittPrimeFieldMap k p w, frobeniusLift_wittPrimeFieldMap k p w⟩
  invFun x :=
    WittVector.mk p fun n => Function.invFun (algebraMap (ZMod p) k) (x.1.coeff n)
  left_inv w := by
    ext n
    exact Function.leftInverse_invFun (algebraMap (ZMod p) k).injective (w.coeff n)
  right_inv x := by
    have hfix : ∀ n, x.1.coeff n ^ p = x.1.coeff n := by
      intro n
      have h := congrArg (fun y : CoefficientRing k p => y.coeff n) x.2
      simpa [frobeniusLift, WittVector.coeff_frobenius_charP] using h
    apply Subtype.ext
    ext n
    obtain ⟨a, ha⟩ := (pow_eq_self_iff_mem_range k p).1 (hfix n)
    show algebraMap (ZMod p) k (Function.invFun (algebraMap (ZMod p) k) (x.1.coeff n)) = _
    rw [← ha, Function.leftInverse_invFun (algebraMap (ZMod p) k).injective a]
omit [Finite k] in
@[simp]
theorem wittPrimeFieldFixedEquiv_apply_coe (w : CoefficientRing (ZMod p) p) :
    ((wittPrimeFieldFixedEquiv k p w : {x : CoefficientRing k p // frobeniusLift k p x = x}) :
        CoefficientRing k p) = wittPrimeFieldMap k p w :=
  rfl
omit [Finite k] in
theorem wittPrimeFieldMap_symm_apply
    (x : {x : CoefficientRing k p // frobeniusLift k p x = x}) :
    wittPrimeFieldMap k p ((wittPrimeFieldFixedEquiv k p).symm x) = x.1 :=
  congrArg Subtype.val ((wittPrimeFieldFixedEquiv k p).apply_symm_apply x)
end FixedPoints
section OrbitSum
omit [CharP k p] [Finite k] [Algebra (ZMod p) k] in
 theorem iterate_frobeniusLift_add (i : ℕ) (x y : CoefficientRing k p) :
    (frobeniusLift k p)^[i] (x + y) =
      (frobeniusLift k p)^[i] x + (frobeniusLift k p)^[i] y := by
  induction i with
  | zero => simp
  | succ n ih =>
      simp only [Function.iterate_succ_apply', ih, map_add]
omit [CharP k p] [Finite k] [Algebra (ZMod p) k] in
 theorem iterate_frobeniusLift_zero (i : ℕ) :
    (frobeniusLift k p)^[i] (0 : CoefficientRing k p) = 0 := by
  induction i with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_zero]
theorem iterate_frobeniusLift_finrank (w : CoefficientRing k p) :
    (frobeniusLift k p)^[Module.finrank (ZMod p) k] w = w := by
  letI := Fintype.ofFinite k
  ext n
  rw [frobeniusLift, WittVector.iterate_frobenius_coeff,
    FiniteField.pow_finrank_eq_natCard p k, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card _
def wittFrobeniusOrbitSum (w : CoefficientRing k p) : CoefficientRing k p :=
  ∑ i ∈ range (Module.finrank (ZMod p) k), (frobeniusLift k p)^[i] w
omit [CharP k p] [Finite k] in
theorem wittFrobeniusOrbitSum_add (x y : CoefficientRing k p) :
    wittFrobeniusOrbitSum k p (x + y) =
      wittFrobeniusOrbitSum k p x + wittFrobeniusOrbitSum k p y := by
  simp only [wittFrobeniusOrbitSum, iterate_frobeniusLift_add, Finset.sum_add_distrib]
omit [CharP k p] [Finite k] in
theorem wittFrobeniusOrbitSum_zero :
    wittFrobeniusOrbitSum k p (0 : CoefficientRing k p) = 0 := by
  simp only [wittFrobeniusOrbitSum, iterate_frobeniusLift_zero, Finset.sum_const_zero]
theorem wittFrobeniusOrbitSum_fixed (w : CoefficientRing k p) :
    frobeniusLift k p (wittFrobeniusOrbitSum k p w) = wittFrobeniusOrbitSum k p w := by
  set d := Module.finrank (ZMod p) k with hd
  have hshift : ∀ i, frobeniusLift k p ((frobeniusLift k p)^[i] w)
      = (frobeniusLift k p)^[i + 1] w := by
    intro i
    rw [Function.iterate_succ_apply']
  have e1 : ∑ i ∈ range (d + 1), (frobeniusLift k p)^[i] w
      = (∑ i ∈ range d, (frobeniusLift k p)^[i + 1] w) + (frobeniusLift k p)^[0] w :=
    Finset.sum_range_succ' _ d
  have e2 : ∑ i ∈ range (d + 1), (frobeniusLift k p)^[i] w
      = (∑ i ∈ range d, (frobeniusLift k p)^[i] w) + (frobeniusLift k p)^[d] w :=
    Finset.sum_range_succ _ d
  rw [iterate_frobeniusLift_finrank k p w] at e2
  simp only [Function.iterate_zero, id_eq] at e1
  rw [wittFrobeniusOrbitSum, map_sum]
  simp only [hshift]
  exact add_right_cancel (e1.symm.trans e2)
end OrbitSum
section Trace
 def wittTraceFun (w : CoefficientRing k p) : CoefficientRing (ZMod p) p :=
  (wittPrimeFieldFixedEquiv k p).symm
    ⟨wittFrobeniusOrbitSum k p w, wittFrobeniusOrbitSum_fixed k p w⟩
 theorem wittPrimeFieldMap_wittTraceFun (w : CoefficientRing k p) :
    wittPrimeFieldMap k p (wittTraceFun k p w) = wittFrobeniusOrbitSum k p w :=
  wittPrimeFieldMap_symm_apply k p _
def wittTrace : CoefficientRing k p →+ CoefficientRing (ZMod p) p where
  toFun := wittTraceFun k p
  map_zero' :=
    wittPrimeFieldMap_injective k p <| by
      rw [wittPrimeFieldMap_wittTraceFun, wittFrobeniusOrbitSum_zero, map_zero]
  map_add' x y :=
    wittPrimeFieldMap_injective k p <| by
      rw [wittPrimeFieldMap_wittTraceFun, map_add, wittPrimeFieldMap_wittTraceFun,
        wittPrimeFieldMap_wittTraceFun, wittFrobeniusOrbitSum_add]
end Trace
section Derived
end Derived
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
open scoped Classical
namespace FiniteFields.Dwork
section Truncation
variable (R : Type*) [CommRing R]
def truncationIdeal (N : ℕ) : Ideal R⟦X⟧ :=
  Ideal.span {(X : R⟦X⟧) ^ N}
abbrev TruncatedSeries (N : ℕ) : Type _ :=
  R⟦X⟧ ⧸ truncationIdeal R N
abbrev truncateSeries (N : ℕ) : R⟦X⟧ →+* TruncatedSeries R N :=
  Ideal.Quotient.mk (truncationIdeal R N)
variable {R}
theorem mem_truncationIdeal_iff {N : ℕ} {f : R⟦X⟧} :
    f ∈ truncationIdeal R N ↔ ∀ m, m < N → coeff m f = 0 := by
  rw [truncationIdeal, Ideal.mem_span_singleton]
  exact PowerSeries.X_pow_dvd_iff
theorem truncateSeries_eq_iff {N : ℕ} {f g : R⟦X⟧} :
    truncateSeries R N f = truncateSeries R N g ↔ ∀ m, m < N → coeff m f = coeff m g := by
  rw [truncateSeries, Ideal.Quotient.eq, mem_truncationIdeal_iff]
  refine forall_congr' fun m => forall_congr' fun _ => ?_
  rw [map_sub, sub_eq_zero]
end Truncation
structure TruncatedPrincipalUnit (R : Type*) [CommRing R] (N : ℕ) where
  val : TruncatedSeries R N
  isPrincipal : ∃ f : R⟦X⟧, constantCoeff f = 1 ∧ truncateSeries R N f = val
namespace TruncatedPrincipalUnit
variable {R : Type*} [CommRing R] {N : ℕ}
@[ext]
theorem ext {a b : TruncatedPrincipalUnit R N} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  subst h
  rfl
def rep (a : TruncatedPrincipalUnit R N) : R⟦X⟧ :=
  a.isPrincipal.choose
theorem constantCoeff_rep (a : TruncatedPrincipalUnit R N) : constantCoeff a.rep = 1 :=
  a.isPrincipal.choose_spec.1
theorem truncateSeries_rep (a : TruncatedPrincipalUnit R N) :
    truncateSeries R N a.rep = a.val :=
  a.isPrincipal.choose_spec.2
instance instMul : Mul (TruncatedPrincipalUnit R N) where
  mul a b :=
    ⟨a.val * b.val, by
      obtain ⟨f, hf, hfa⟩ := a.isPrincipal
      obtain ⟨g, hg, hgb⟩ := b.isPrincipal
      exact ⟨f * g, by rw [map_mul, hf, hg, one_mul], by rw [map_mul, hfa, hgb]⟩⟩
instance instOne : One (TruncatedPrincipalUnit R N) where
  one := ⟨1, ⟨1, map_one _, map_one _⟩⟩
instance instInv : Inv (TruncatedPrincipalUnit R N) where
  inv a :=
    ⟨truncateSeries R N (invOfUnit a.rep 1),
      ⟨invOfUnit a.rep 1, by rw [constantCoeff_invOfUnit]; simp, rfl⟩⟩
@[simp] theorem val_mul (a b : TruncatedPrincipalUnit R N) : (a * b).val = a.val * b.val := rfl
@[simp] theorem val_one : (1 : TruncatedPrincipalUnit R N).val = 1 := rfl
@[simp] theorem val_inv (a : TruncatedPrincipalUnit R N) :
    a⁻¹.val = truncateSeries R N (invOfUnit a.rep 1) := rfl
instance instCommGroup : CommGroup (TruncatedPrincipalUnit R N) where
  mul_assoc _ _ _ := ext (mul_assoc _ _ _)
  one_mul _ := ext (one_mul _)
  mul_one _ := ext (mul_one _)
  mul_comm _ _ := ext (mul_comm _ _)
  inv_mul_cancel a := by
    refine ext ?_
    rw [val_mul, val_inv, val_one, ← truncateSeries_rep a, ← map_mul,
      invOfUnit_mul a.rep 1 (by simp [constantCoeff_rep]), map_one]
def ofSeries (f : R⟦X⟧) (hf : constantCoeff f = 1) : TruncatedPrincipalUnit R N :=
  ⟨truncateSeries R N f, ⟨f, hf, rfl⟩⟩
@[simp] theorem val_ofSeries (f : R⟦X⟧) (hf : constantCoeff f = 1) :
    (ofSeries (N := N) f hf).val = truncateSeries R N f := rfl
theorem ofSeries_eq_ofSeries_iff {f g : R⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) :
    (ofSeries (N := N) f hf) = ofSeries (N := N) g hg ↔ ∀ m, m < N → coeff m f = coeff m g := by
  constructor
  · intro h
    exact truncateSeries_eq_iff.mp (congrArg TruncatedPrincipalUnit.val h)
  · intro h
    exact ext (truncateSeries_eq_iff.mpr h)
theorem ofSeries_mul {f g : R⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    (ofSeries (N := N) (f * g) (by rw [map_mul, hf, hg, one_mul]))
      = ofSeries f hf * ofSeries g hg :=
  ext (by rw [val_ofSeries, val_mul, val_ofSeries, val_ofSeries, map_mul])
theorem ofSeries_one : (ofSeries (N := N) (1 : R⟦X⟧) (map_one _)) = 1 :=
  ext (by rw [val_ofSeries, val_one, map_one])
end TruncatedPrincipalUnit
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
open scoped Classical
namespace FiniteFields.Dwork
def artinHasseLogDerivOf (R : Type*) [CommRing R] (p : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n => if ∃ j : ℕ, p ^ j = n + 1 then -1 else 0
theorem coeff_artinHasseLogDerivOf (R : Type*) [CommRing R] (p n : ℕ) :
    coeff n (artinHasseLogDerivOf R p) = if ∃ j : ℕ, p ^ j = n + 1 then -1 else 0 :=
  PowerSeries.coeff_mk _ _
theorem map_artinHasseLogDerivOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ) :
    PowerSeries.map φ (artinHasseLogDerivOf R p) = artinHasseLogDerivOf S p := by
  ext n
  rw [PowerSeries.coeff_map, coeff_artinHasseLogDerivOf, coeff_artinHasseLogDerivOf]
  split_ifs <;> simp
theorem map_derivative {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    PowerSeries.map φ (PowerSeries.derivative R f)
      = PowerSeries.derivative S (PowerSeries.map φ f) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  congr 1
  simp
section Rational
variable (p : ℕ)
theorem artinHasseLogDerivOf_rat :
    artinHasseLogDerivOf ℚ p = PowerSeries.derivative ℚ (artinHasseLog p) := by
  ext n
  rw [coeff_artinHasseLogDerivOf, PowerSeries.coeff_derivative, artinHasseLog_coeff]
  split_ifs with h
  · obtain ⟨_, _⟩ := h
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  · rw [zero_mul]
theorem derivative_artinHasseExponential :
    PowerSeries.derivative ℚ (artinHasseExponential p)
      = artinHasseExponential p * artinHasseLogDerivOf ℚ p := by
  rw [artinHasseLogDerivOf_rat, artinHasseExponential,
    PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' (artinHasseLog_constantCoeff p)),
    PowerSeries.derivative_exp]
end Rational
section Carrier
variable (K : Type*) [CommRing K] [Algebra ℚ K] (p : ℕ)
def artinHasseSeries : K⟦X⟧ :=
  PowerSeries.map (algebraMap ℚ K) (artinHasseExponential p)
@[simp]
theorem constantCoeff_artinHasseSeries : constantCoeff (artinHasseSeries K p) = 1 := by
  rw [artinHasseSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, artinHasseExponential_constantCoeff, map_one]
theorem derivative_artinHasseSeries :
    PowerSeries.derivative K (artinHasseSeries K p)
      = artinHasseSeries K p * artinHasseLogDerivOf K p := by
  rw [artinHasseSeries, ← map_derivative, derivative_artinHasseExponential, map_mul,
    map_artinHasseLogDerivOf]
end Carrier
end FiniteFields.Dwork
end
end


