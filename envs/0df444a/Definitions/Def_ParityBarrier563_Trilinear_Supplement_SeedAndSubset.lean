-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Supplement_SeedAndSubset
-- name    : ParityBarrier563_Trilinear_Supplement_SeedAndSubset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:42:03.502906+00:00
-- url     : https://prove2.me/theorems/1d51712f-b934-4861-a00d-c5cffe07ed0f
-- title:
--   Conditional seed averages and Bernoulli sumsets
-- statement:
--   Split a restriction τ of the published trilinear inputs into its data and seed parts. Average uniformly over all extensions a of the seed part and then independently draw a q-random restriction φ of remaining data bits:
--   $$\mathbb E_{a\mid\tau}\mathbb E_\varphi\operatorname{corr}_k((g^a)_{\tau\varphi}).$$
--   The conditioning is a nonempty finite cube of live seed assignments, with no division by an event probability. For a finite available set B of nonnegative integer positions, subsetProb assigns T⊆B product weight $\prod_{i\in B}(\eta\text{ if }i\in T\text{ else }1-\eta)$. The sumset is $A+T=\{a+t:a\in A,t\in T\}$, with ordinary integer addition. These definitions implement the distributions in Lemmas 6.5 and 6.6, including empty available sets.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemmas 6.5–6.6, printed pp.28–29 / PDF 30–31

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_TrilinearFunction
import Definitions.Def_ParityBarrier563_Trilinear_Correlation
import Definitions.Def_ParityBarrier563_Trilinear_Supplement_FiniteAverages

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- The data part and seed part of one restriction of all trilinear inputs. -/
def dataRestriction {n : ℕ} (τ : Restriction (TriVar n)) : Restriction (SliceVar n) :=
  fun v => τ (.inl v)
def seedRestriction {n : ℕ} (τ : Restriction (TriVar n)) : Restriction (Fin (2*n-1)) :=
  fun i => τ (.inr i)

/-- Finite uniform mean over the nonempty cube of seed extensions, followed by an
independent q-random restriction of remaining data variables. -/
noncomputable def seedCorrelation {n : ℕ} (τ : Restriction (TriVar n)) (q : ℝ) (k : ℕ) : ℝ :=
  avg (fun z =>
    let a := fill (seedRestriction τ) z
    restrExpect q (fun φ => corr k (restrict φ
      (restrict (dataRestriction τ) (sgn (slice n a))))))

/-- Bernoulli product probability on subsets of available positions B. -/
noncomputable def subsetProb (B : Finset ℕ) (η : ℝ) (P : Finset ℕ → Prop) : ℝ :=
  ∑ T ∈ B.powerset, (if P T then 1 else 0) *
    (∏ i ∈ B, if i ∈ T then η else 1-η)

/-- Integer sumset; natural coordinates embed into integers with the same additions
and cardinalities, including empty sets. -/
def sumset (A T : Finset ℕ) : Finset ℕ :=
  (A.product T).image (fun ij => ij.1 + ij.2)

end ParityBarrier563.Trilinear.Supplement


