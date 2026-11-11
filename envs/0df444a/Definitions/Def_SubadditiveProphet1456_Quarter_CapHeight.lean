-- Prove2me | Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
-- name    : SubadditiveProphet1456_Quarter_CapHeight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:05.459784+00:00
-- url     : https://prove2.me/theorems/bf65c2a3-d8fa-4016-9825-94c758bacf2d
-- title:
--   Algorithm 1: fresh-sample CapHeight execution and conditional retention implementation
-- statement:
--   For unconditional tentative-bundle laws $\mu_k$, the procedure $\operatorname{CapHeight}(i,h,A)$ returns zero if $h=0$ or $A$ is empty. Otherwise it independently samples $L_k^r\sim\mu_k$ for $r\in\{0,1\}$ and every buyer $k$, recursively generates scores at $(k,h-1,A\cap L_k^r)$, computes their eligible effective threshold, and returns
--   $$
--   \bigl(1+\Theta_i(Y^0,Y^1)\bigr)|_A.
--   $$
--   The recursion strictly decreases the depth. The same sampled bundle governs every coordinate within a call. The execution law carries its score and the sum of child work plus explicit local charges for bundle sampling/output, intersections, prefix/full maxima, eligibility comparisons and integer-score arithmetic. These charges are relative to unit tentative-bundle sampling access, as in the source's running-time proof. Supplying those samplers from the original input is a separate, fully charged obligation in the goal and Fact 2.1.
--
--   The capped type-dependent generator first samples $X_i\sim\mu_{i,\tau}$ and runs CapHeight at $(i,N,X_i)$. Its reference profile independently generates one such unconditional call for each buyer. The fixed-point comparison independently draws two full depth-$N$ profiles and returns the capped successor of their effective threshold on $A$.
--
--   The implementation for conditional retention independently draws a tentative bundle and two complete depth-$N$ profiles before returning
--   $$
--   \min\{N\mathbf1,\mathbf1+\widetilde\Theta_i\}|_{X_i}.
--   $$
--   The defined conditional welfare fixes the realized type and tentative bundle, integrates over these fresh internal profiles, and then over the mechanism reference profile and independent actual predecessor scores from the same implemented generators. It therefore represents conditioning on the pair $(\tau,A)$, rather than averaging away the bundle or assuming a coupling not supplied by the distributional identity.
--
--   **Formalization Note** Score laws and execution costs are actual recursively defined distributions. No retention, tail bound, distributional fixed point, or runtime estimate is a field of a definition. Theorem items establish those properties. Empty bundles and depth zero are explicit terminal cases.
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, §2 (printed pp.7–9, PDF pp.8–10), §3 (printed pp.9–10, PDF pp.10–11), §4.3 Algorithm 1 (printed pp.15–17, PDF pp.16–18), Appendix A (printed pp.31–34, PDF pp.32–35).

import Definitions.Def_SubadditiveProphet1456_Quarter_Model

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

/-- Algorithm 1 with fresh independent child calls. The second component counts its
specified sampler, coordinate-intersection, maximum, comparison, and integer-addition work.
The cost is relative to a unit tentative-bundle sampler, including its m output bits. -/
noncomputable def capExecution {n m : ℕ} (μ : Fin n → PMF (Bundle m)) :
    ℕ → Fin n → Bundle m → PMF (Score m × ℕ)
  | 0, _, _ => PMF.pure (0,1)
  | h+1, i, A =>
      if A = ∅ then PMF.pure (0,1) else
      let child := fun k => (μ k).bind fun L =>
        (capExecution μ h k (A ∩ L)).map fun z =>
          (z.1, z.2 + 1 + 2*m)
      (independent child).bind fun Y =>
      (independent child).map fun Z =>
        (restrictScore A (fun j => 1+threshold i (fun k => (Y k).1) (fun k => (Z k).1) j),
          1 + (∑ k, ((Y k).2 + (Z k).2)) +
            m*(12*n+8)*(1+Nat.log2 (h+2)))

noncomputable def capHeight {n m : ℕ} (μ : Fin n → PMF (Bundle m))
    (i : Fin n) (h : ℕ) (A : Bundle m) : PMF (Score m) :=
  (capExecution μ h i A).map Prod.fst

noncomputable def capExpectedCost {n m : ℕ} (μ : Fin n → PMF (Bundle m))
    (i : Fin n) (h : ℕ) (A : Bundle m) : ℝ≥0∞ :=
  ∑' z : Score m × ℕ, capExecution μ h i A z * (z.2 : ℝ≥0∞)

noncomputable def capRSG {n m : ℕ} (I : Instance n m) (x : Fractional I) (N : ℕ) : RSG I :=
  fun i t => (tentative I x i t).bind (capHeight (unconditionalBundle I x) i N)

noncomputable def rsgExpectedCost {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (N : ℕ) (i : Fin n) (t : Fin (I.types i+1)) : ℝ≥0∞ :=
  1+m+∑ A : Bundle m, tentative I x i t A *
    capExpectedCost (unconditionalBundle I x) i N A

noncomputable def capReference {n m : ℕ} (μ : Fin n → PMF (Bundle m)) (N : ℕ) :
    PMF (ScoreProfile n m) :=
  independent fun k => (μ k).bind (capHeight μ k N)

noncomputable def capFixedLaw {n m : ℕ} (μ : Fin n → PMF (Bundle m))
    (N : ℕ) (i : Fin n) (A : Bundle m) : PMF (Score m) :=
  (capReference μ N).bind fun Y => (capReference μ N).map fun Z => cappedSuccessor N i Y Z A

/-- The implementation used in Lemma 4.3: a fresh tentative bundle and two full cap-N
reference profiles, independently of every actual or mechanism-reference draw. -/
noncomputable def retentionExecution {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (N : ℕ) (i : Fin n) (t : Fin (I.types i+1)) : PMF (Bundle m × Score m × ℕ) :=
  (tentative I x i t).bind fun A =>
  let child := fun k => (unconditionalBundle I x k).bind fun L =>
    (capExecution (unconditionalBundle I x) N k L).map fun z => (z.1,z.2+1+m)
  (independent child).bind fun Y => (independent child).map fun Z =>
    (A,cappedSuccessor N i (fun k => (Y k).1) (fun k => (Z k).1) A,
      1+m+(∑ k, ((Y k).2+(Z k).2))+m*(12*n+8)*(1+Nat.log2 (N+1)))

noncomputable def retentionRSG {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (N : ℕ) : RSG I :=
  fun i t => (retentionExecution I x N i t).map fun z => z.2.1

noncomputable def retentionExpectedCost {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (N : ℕ) (i : Fin n) (t : Fin (I.types i+1)) : ℝ≥0∞ :=
  ∑' z : Bundle m × Score m × ℕ, retentionExecution I x N i t z * (z.2.2 : ℝ≥0∞)

/-- Fixed type and tentative bundle comparison, with other actual buyers and the
mechanism's reference profile independently generated from the same RSGs. -/
noncomputable def conditionalRetention {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (N : ℕ) (i : Fin n) (t : Fin (I.types i+1)) (A : Bundle m) : ℝ :=
  let φ := retentionRSG I x N
  ∫ Y, ∫ Z, ∫ U, ∫ V,
    I.valuation i t (allocated i (cappedSuccessor N i U V A) Y Z)
    ∂(referenceLaw I (capRSG I x N)).toMeasure
    ∂(referenceLaw I (capRSG I x N)).toMeasure
    ∂(referenceLaw I φ).toMeasure
    ∂(referenceLaw I φ).toMeasure

end SubadditiveProphet1456.Quarter


