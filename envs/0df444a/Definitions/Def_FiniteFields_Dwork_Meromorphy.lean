-- Prove2me | Definitions.Def_FiniteFields_Dwork_Meromorphy
-- name    : FiniteFields_Dwork_Meromorphy
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T01:36:46.505974+00:00
-- url     : https://prove2.me/theorems/9a40b8ac-9325-4232-9a8f-60285ea32221
-- title:
--   Fredholm determinants of nuclear operators, $p$-adic meromorphy and the toric zeta–Fredholm factors
-- statement:
--   Let $K$ be a complete, nontrivially normed, ultrametric field, $w$ a positive weight on $\mathbb N^d$, and $T$ a nuclear operator with kernel $A$ and finite cutoffs $A_{\le N}$, as in the nuclear-operator file.
--
--   1. **Fredholm determinant.** The $m$-th coefficient $c_m$ is the limit as $N\to\infty$ of the $m$-th coefficient of the cutoff determinant $\det(1-XA_{\le N})$, and
--   $$\det(1-XT)=\sum_{m\ge0}c_mX^m\in K[[X]].$$
--   2. **Traces and logarithmic derivative.** The trace series and the negative logarithmic derivative are
--   $$\sum_{n\ge0}\operatorname{Tr}(T^{n+1})X^n,\qquad -\frac{\frac{d}{dX}\det(1-XT)}{\det(1-XT)}.$$
--   The trace series $\sum_n\operatorname{tr}(u^{n+1})X^n$ is defined in the same way for a finite-dimensional endomorphism $u$.
--   3. **$p$-adic entire and meromorphic series.** A series $F=\sum a_nX^n\in K[[X]]$ is *entire* if $|a_n|R^n\to0$ for every real $R\ge0$. It is *meromorphic* if $HF=G$ for entire series $G$ and $H$ with $H(0)=1$.
--   4. **Toric zeta series.** For a finitely supported polynomial $f$ in $d$ variables over a finite field $k_0$ with $q$ elements, with toric counts $N^*_s(f)$,
--   $$Z^*(f;t)=\exp\Big(\sum_{s\ge1}\frac{N^*_s(f)}{s}t^s\Big)\in\mathbb Q[[t]].$$
--   The file also defines its image in $L[[t]]$, where $L=K_0(\zeta)$.
--   5. **Zeta–Fredholm factors.** For a positive weight $w'$ on $\mathbb N^{d+1}$, Dwork's toric operator is the nuclear operator of the auxiliary polynomial $x_0f(x)$, with Fredholm determinant $\Delta_f(t)$. For $0\le i\le d$ and $0\le j\le d+1$ the factors are $1-q^{i-1}t$ and $\Delta_f(q^{j-1}t)$, and the denominator is
--   $$D_f(t)=\prod_{\substack{0\le i\le d\\ d+i\ \text{even}}}\big(1-q^{i-1}t\big)^{\binom di}\prod_{\substack{0\le j\le d+1\\ d+1+j\ \text{even}}}\Delta_f\big(q^{j-1}t\big)^{\binom{d+1}{j}}.$$
--   The numerator $N_f(t)$ is the same product over the indices with $d+i$, respectively $d+1+j$, odd. The file also defines the corresponding signed sums of logarithmic derivatives.
--
--   The file also contains the structural lemmas used to state these definitions, such as the comparison of nested cutoff determinants by zero padding and the finite-dimensional trace–determinant identity.
--
--   These are the analytic objects of Dwork's §3. The determinant $\Delta_f$ is the limit $\Delta(t)$ of Fredholm determinants in (19)–(21), which (22)–(26) show to be entire. The quotient $N_f/D_f$ is the product formula that expresses the zeta function of a toric hypersurface and gives its meromorphy (Theorem 1). The predicates "entire" and "meromorphic" are the hypotheses on the $p$-adic side of the rationality criterion, Theorem 2 of §4.
--
--   **Formalization Note** The scalars $q^{i-1}$ are computed in $L$ as $q^i\cdot q^{-1}$, so $i=0$ and $j=0$ give the factor $q^{-1}$. Coefficient limits use `limUnder`, and their existence is proved separately. The inverse in the logarithmic derivative is the formal inverse of a series with constant term $1$.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §3: Theorem 1 (meromorphy of $\zeta$), formulas (16)–(21) (point counts as traces, the limit $\Delta(t)$ of Fredholm determinants) and (22)–(26) ($\Delta$ is entire); §4: hypotheses of Theorem 2 ((28)–(31)). Lean: ported from the `finite_fields` project (commit e8b5bf14), modules `WeilConjectures/Dwork/FredholmCoefficients/Weighted.lean`, `WeilConjectures/Dwork/FredholmCoefficients/Cofinal.lean`, `WeilConjectures/LinearAlgebra/TracePower.lean`, `WeilConjectures/Dwork/FredholmDeterminant.lean`, `WeilConjectures/Dwork/DworkZetaFredholm/Growth.lean`, `WeilConjectures/Dwork/DworkZetaFredholm/ZetaFredholm.lean`, `WeilConjectures/Dwork/TraceFormula.lean`, `WeilConjectures/Dwork/AffineHypersurfaceRationality/MeromorphicCalculus.lean`.

import Mathlib
import Definitions.Def_FiniteFields_Dwork_TraceFormula

section
noncomputable section
open Filter Set Topology Polynomial PowerSeries Finset
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
namespace NuclearOperator
def cutoffFredholmPolynomial (T : NuclearOperator (K := K) w) (bound : ℕ) : K[X] :=
  FiniteFields.LinearAlgebra.fredholmDeterminant
    (Matrix.toLin' (cutoffKernel w T.kernel bound))
def cutoffFredholmCoefficient (T : NuclearOperator (K := K) w)
    (degree bound : ℕ) : K :=
  (cutoffFredholmPolynomial w T bound).coeff degree
 def fredholmWeightedCutoffOfLE {smaller larger : ℕ}
    (v : WeightedCutoff w larger) (hv : monomialWeight w v.1 ≤ smaller) :
    WeightedCutoff w smaller :=
  ⟨v.1, hv⟩
 def fredholmPaddedCutoffKernel
    (T : NuclearOperator (K := K) w) (smaller larger : ℕ) :
    Matrix (WeightedCutoff w larger) (WeightedCutoff w larger) K :=
  fun u v ↦
    if _hu : monomialWeight w u.1 ≤ smaller then
      if _hv : monomialWeight w v.1 ≤ smaller then T.kernel u.1 v.1 else 0
    else 0
 def fredholmCutoffRestriction {smaller larger : ℕ} (h : smaller ≤ larger) :
    (WeightedCutoff w larger → K) →ₗ[K] (WeightedCutoff w smaller → K) where
  toFun f u := f (weightedCutoffInclusion w h u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
 def fredholmCutoffZeroExtension (smaller larger : ℕ) :
    (WeightedCutoff w smaller → K) →ₗ[K] (WeightedCutoff w larger → K) where
  toFun f v :=
    if hv : monomialWeight w v.1 ≤ smaller then f (fredholmWeightedCutoffOfLE w v hv) else 0
  map_add' f g := by
    ext v
    by_cases hv : monomialWeight w v.1 ≤ smaller <;>
      simp [hv, fredholmWeightedCutoffOfLE]
  map_smul' c f := by
    ext v
    by_cases hv : monomialWeight w v.1 ≤ smaller <;>
      simp [hv, fredholmWeightedCutoffOfLE]
def weightedFredholmCoefficient (T : NuclearOperator (K := K) w) (degree : ℕ) : K :=
  limUnder atTop (fun bound ↦ cutoffFredholmCoefficient w T degree bound)
def weightedFredholmSeries (T : NuclearOperator (K := K) w) : K⟦X⟧ :=
  PowerSeries.mk (weightedFredholmCoefficient w T)
end NuclearOperator
end FiniteFields.Dwork
end
end

section
noncomputable section
open Module Polynomial PowerSeries
namespace FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
def tracePowerSeries (u : Module.End R M) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ LinearMap.trace R M (u ^ (n + 1))
 def matrixGeometricSeries {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    Matrix ι ι R⟦X⟧ :=
  fun i j ↦ PowerSeries.mk fun n ↦ (A ^ n) i j
end FiniteFields.LinearAlgebra
end
end

section
noncomputable section
open Filter Set Topology Polynomial PowerSeries Finset
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
namespace NuclearOperator
def fredholmDeterminant (T : NuclearOperator (K := K) w) : K⟦X⟧ :=
  weightedFredholmSeries w T
def tracePowerSeries (T : NuclearOperator (K := K) w) : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ tracePower w T ⟨n + 1, Nat.succ_pos n⟩
def fredholmLogDerivative (T : NuclearOperator (K := K) w) : K⟦X⟧ :=
  -(PowerSeries.derivative K (fredholmDeterminant w T)) *
    PowerSeries.invOfUnit (fredholmDeterminant w T) 1
 def cutoffEndomorphism (T : NuclearOperator (K := K) w) (bound : ℕ) :
    Module.End K (WeightedCutoff w bound → K) :=
  Matrix.toLin' (cutoffKernel w T.kernel bound)
end NuclearOperator
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section PadicGrowth
variable {K : Type*} [NontriviallyNormedField K]
def IsPadicEntire (F : K⟦X⟧) : Prop :=
  ∀ R : ℝ, 0 ≤ R → Tendsto (fun n ↦ ‖PowerSeries.coeff n F‖ * R ^ n) atTop (nhds 0)
def IsPadicMeromorphic (F : K⟦X⟧) : Prop :=
  ∃ G H : K⟦X⟧,
    IsPadicEntire G ∧ IsPadicEntire H ∧ PowerSeries.constantCoeff H = 1 ∧ H * F = G
end PadicGrowth
section PadicGrowthUltra
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
end PadicGrowthUltra
section PadicGrowthComplete
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
end PadicGrowthComplete
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
section SupBounded
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
 def SupBounded (c : ℝ) (S : K⟦X⟧) : Prop := ∀ m, ‖PowerSeries.coeff m S‖ ≤ c
 def shiftDown (e : ℕ) (S : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ PowerSeries.coeff (n + e) S
end SupBounded
section Inverse
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
end Inverse
section WeierstrassDivision
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
 def wQ (Hh : K⟦X⟧) (e : ℕ) : K⟦X⟧ := shiftDown e Hh
 def wL (Hh : K⟦X⟧) (e : ℕ) : K⟦X⟧ :=
  ((PowerSeries.trunc e Hh : Polynomial K) : K⟦X⟧)
 def wIter (Hh : K⟦X⟧) (e : ℕ) : ℕ → K⟦X⟧
  | 0 => PowerSeries.X ^ e
  | k + 1 => -((wQ Hh e)⁻¹ * shiftDown e (wIter Hh e k)) * wL Hh e
 def wQuo (Hh : K⟦X⟧) (e : ℕ) (k : ℕ) : K⟦X⟧ :=
  (wQ Hh e)⁻¹ * shiftDown e (wIter Hh e k)
 def wRem (Hh : K⟦X⟧) (e : ℕ) (k : ℕ) : K⟦X⟧ :=
  ((PowerSeries.trunc e (wIter Hh e k) : Polynomial K) : K⟦X⟧)
variable {Hh : K⟦X⟧} {e : ℕ} {θ : ℝ}
end WeierstrassDivision
section WeierstrassLimit
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {Hh : K⟦X⟧} {e : ℕ} {θ : ℝ}
 def wQuoSum (Hh : K⟦X⟧) (e : ℕ) : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑' k, PowerSeries.coeff n (wQuo Hh e k)
 def wRemSum (Hh : K⟦X⟧) (e : ℕ) : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑' k, PowerSeries.coeff n (wRem Hh e k)
variable (hb : SupBounded 1 Hh) (hu : ‖PowerSeries.coeff e Hh‖ = 1)
variable (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hlow : ∀ m, m < e → ‖PowerSeries.coeff m Hh‖ ≤ θ)
include hb hu hθ0 hθ1 hlow
end WeierstrassLimit
section Proposition3
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
end Proposition3
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
section ColumnTransform
variable {K : Type*} [Field K]
 def dworkColumnMatrix (P : Polynomial K) (e r : ℕ) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun j' j : Fin r ↦
    if (j : ℕ) < e then (if j' = j then 1 else 0)
    else if (j' : ℕ) ≤ (j : ℕ) then P.coeff ((j : ℕ) - (j' : ℕ)) else 0
end ColumnTransform
section PadicBound
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
end PadicBound
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section FredholmEntire
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
namespace NuclearOperator
 def escapeBound (T : NuclearOperator (K := K) w) (m : ℕ) (u : MonomialIndex d) : ℝ :=
  if monomialWeight w u ≤ m then 1 else T.tailBound m
 def cutoffCard (m : ℕ) : ℕ := (finite_monomialCutoff w m).toFinset.card
end NuclearOperator
end FredholmEntire
section DworkEntire
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
variable {d : ℕ} (w : PositiveMonomialWeight d)
end DworkEntire
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section ZetaSeries
 def countingZetaLog (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n ↦ if n = 0 then 0 else (N (n - 1) : ℚ) / n
 def countingZetaSeries (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  (PowerSeries.exp ℚ).subst (countingZetaLog N)
variable (k₀ : Type) (p : ℕ) [Fact p.Prime] [Field k₀] [CharP k₀ p] [Finite k₀]
variable {d : ℕ}
def toricHypersurfaceZetaSeries (f : MonomialIndex d →₀ k₀) : ℚ⟦X⟧ :=
  countingZetaSeries (toricHypersurfacePointCount k₀ p f)
end ZetaSeries
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section LogDerivative
variable {R : Type*} [CommRing R]
 def geometricLogSeries (c : R) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ c ^ (n + 1)
end LogDerivative
section OdeUniqueness
variable {K : Type*} [Field K] [CharZero K]
end OdeUniqueness
section FredholmLogDerivative
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
end FredholmLogDerivative
section SignedSplit
variable {R : Type*} [CommRing R]
end SignedSplit
section CharZeroInstance
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
instance dworkCyclotomicFieldCharZero : CharZero (DworkCyclotomicField k p) :=
  charZero_of_injective_algebraMap
    (algebraMap (CoefficientField k p) (DworkCyclotomicField k p)).injective
end CharZeroInstance
section ZetaFredholm
variable (k₀ : Type) (p : ℕ) [Fact p.Prime] [Field k₀] [CharP k₀ p] [Finite k₀]
variable {d : ℕ}
def toricZetaScale (i : ℕ) : DworkCyclotomicField k₀ p :=
  (Nat.card k₀ : DworkCyclotomicField k₀ p) ^ i *
    (Nat.card k₀ : DworkCyclotomicField k₀ p)⁻¹
def toricZetaLinearFactor (i : ℕ) : (DworkCyclotomicField k₀ p)⟦X⟧ :=
  1 - PowerSeries.C (toricZetaScale k₀ p i) * PowerSeries.X
variable (w' : PositiveMonomialWeight (d + 1))
def dworkToricOperator (f : MonomialIndex d →₀ k₀) :
    NuclearOperator (K := DworkCyclotomicField k₀ p) w' :=
  dworkQFrobeniusNuclearOperator k₀ p w' (dworkAuxiliaryPolynomial (k := k₀) f)
def toricZetaFredholmFactor (f : MonomialIndex d →₀ k₀) (j : ℕ) :
    (DworkCyclotomicField k₀ p)⟦X⟧ :=
  PowerSeries.rescale (toricZetaScale k₀ p j)
    (NuclearOperator.fredholmDeterminant w' (dworkToricOperator k₀ p w' f))
def toricZetaFredholmDenominator (f : MonomialIndex d →₀ k₀) :
    (DworkCyclotomicField k₀ p)⟦X⟧ :=
  (∏ i ∈ (Finset.range (d + 1)).filter fun i ↦ Even (d + i),
      toricZetaLinearFactor k₀ p i ^ d.choose i) *
    ∏ j ∈ (Finset.range (d + 2)).filter fun j ↦ Even (d + 1 + j),
      toricZetaFredholmFactor k₀ p w' f j ^ (d + 1).choose j
def toricZetaFredholmNumerator (f : MonomialIndex d →₀ k₀) :
    (DworkCyclotomicField k₀ p)⟦X⟧ :=
  (∏ i ∈ (Finset.range (d + 1)).filter fun i ↦ ¬ Even (d + i),
      toricZetaLinearFactor k₀ p i ^ d.choose i) *
    ∏ j ∈ (Finset.range (d + 2)).filter fun j ↦ ¬ Even (d + 1 + j),
      toricZetaFredholmFactor k₀ p w' f j ^ (d + 1).choose j
def toricHypersurfaceZetaSeriesPadic (f : MonomialIndex d →₀ k₀) :
    (DworkCyclotomicField k₀ p)⟦X⟧ :=
  PowerSeries.map (algebraMap ℚ (DworkCyclotomicField k₀ p)) (toricHypersurfaceZetaSeries k₀ p f)
 def toricZetaLinearLog (i : ℕ) : (DworkCyclotomicField k₀ p)⟦X⟧ :=
  geometricLogSeries (toricZetaScale k₀ p i)
 def toricZetaFredholmLog (f : MonomialIndex d →₀ k₀) (j : ℕ) :
    (DworkCyclotomicField k₀ p)⟦X⟧ :=
  PowerSeries.C (toricZetaScale k₀ p j) *
    PowerSeries.rescale (toricZetaScale k₀ p j)
      (NuclearOperator.tracePowerSeries w' (dworkToricOperator k₀ p w' f))
 def toricZetaDenominatorLog (f : MonomialIndex d →₀ k₀) :
    (DworkCyclotomicField k₀ p)⟦X⟧ :=
  (∑ i ∈ (Finset.range (d + 1)).filter fun i ↦ Even (d + i),
      d.choose i • toricZetaLinearLog k₀ p i) +
    ∑ j ∈ (Finset.range (d + 2)).filter fun j ↦ Even (d + 1 + j),
      (d + 1).choose j • toricZetaFredholmLog k₀ p w' f j
 def toricZetaNumeratorLog (f : MonomialIndex d →₀ k₀) :
    (DworkCyclotomicField k₀ p)⟦X⟧ :=
  (∑ i ∈ (Finset.range (d + 1)).filter fun i ↦ ¬ Even (d + i),
      d.choose i • toricZetaLinearLog k₀ p i) +
    ∑ j ∈ (Finset.range (d + 2)).filter fun j ↦ ¬ Even (d + 1 + j),
      (d + 1).choose j • toricZetaFredholmLog k₀ p w' f j
 def toricZetaSignedLog (f : MonomialIndex d →₀ k₀) :
    (DworkCyclotomicField k₀ p)⟦X⟧ :=
  (∑ i ∈ Finset.range (d + 1),
      PowerSeries.C ((-1 : DworkCyclotomicField k₀ p) ^ (d + i)) *
        (d.choose i : (DworkCyclotomicField k₀ p)⟦X⟧) * toricZetaLinearLog k₀ p i) +
    ∑ j ∈ Finset.range (d + 2),
      PowerSeries.C ((-1 : DworkCyclotomicField k₀ p) ^ (d + 1 + j)) *
        ((d + 1).choose j : (DworkCyclotomicField k₀ p)⟦X⟧) * toricZetaFredholmLog k₀ p w' f j
end ZetaFredholm
end FiniteFields.Dwork
end
end


