-- Prove2me | Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden
-- name    : CalibratedMA_Randomized_Supplement_Hidden
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:23:13.477082+00:00
-- url     : https://prove2.me/theorems/3bc9027c-10e9-4686-b0e1-be8a6b317b34
-- title:
--   Sections 6–7 — hidden-offset laws, Hamming distance and public decoders
-- statement:
--   On a domain of $R$ points, let $\mu_i$ be Bernoulli means. The labeled data law is the actual finite mixture
--   $$D_\mu=\frac1R\sum_i\bigl(\mu_i\delta_{(i,1)}+(1-\mu_i)\delta_{(i,0)}\bigr),\qquad
--   D_\theta=D_{(t_i+\eta\theta_i)_i}.$$
--   Statements using this law require $R>0$ and valid means; no default value at invalid means is used as a statistical experiment. Hidden alphabets are either $\{0,1\}$ or $\{-1,1\}$. Hamming distance counts unequal coordinates. The randomized hard family has public points $x_i=i/k$ and baselines $b_i=1/4+x_i/2$ for $1\le i\le k$; its Lean carrier is relabeled as $\mathrm{Fin}\ k$.
--
--   Let $J(p)$ choose a nearest baseline, breaking ties by smaller index. The public decoder is
--   $$z_j=\frac{k}{\Delta}\frac1k\sum_i\int\mathbf1_{\{J(p)=j\}}(p-b_i)\,Q_i(dp),\qquad
--   \widehat\theta_j=\mathbf1_{\{z_j\ge1/2\}}.$$
--   It uses neither labels nor hidden bits. The deterministic decoder is $\widehat\theta_i=\operatorname{sign}(p_i-t_i)$, with either fixed tie sign, and the baseline error is $\bar e=R^{-1}\sum_i|p_i-t_i|$. These definitions provide the explicit experiments and decoders used in the lower-bound statements.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), pp.32–38, Lemmas 6.2, 6.4, 7.2 and their constructions

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Learning

open MeasureTheory
open scoped ENNReal

namespace CalibratedMA.Randomized.Supplement

/-- Sections 6–7: uniform context, Bernoulli labels with the supplied means. -/
noncomputable def bernoulliData (R : ℕ) (μ : Fin R → ℝ) : Measure (Fin R × ℝ) :=
  (R : ℝ≥0∞)⁻¹ • ∑ i : Fin R,
    (ENNReal.ofReal (μ i) • Measure.dirac (i, (1 : ℝ)) +
      ENNReal.ofReal (1 - μ i) • Measure.dirac (i, (0 : ℝ)))

noncomputable def offsetData {R : ℕ} (t : Fin R → ℝ) (η : ℝ)
    (θ : Fin R → ℝ) : Measure (Fin R × ℝ) :=
  bernoulliData R (fun i => t i + η * θ i)

noncomputable def hamming {R : ℕ} (a b : Fin R → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i ≠ b i)).card

def IsBit (x : ℝ) : Prop := x = 0 ∨ x = 1

def IsSign (x : ℝ) : Prop := x = -1 ∨ x = 1

def Alphabet (signed : Bool) : Set ℝ := {x | if signed then IsSign x else IsBit x}

noncomputable def contextPoint {k : ℕ} (i : Fin k) : ℝ := (i.val + 1 : ℝ) / k

noncomputable def baseline {k : ℕ} (i : Fin k) : ℝ := 1 / 4 + contextPoint i / 2

/-- Nearest public baseline; sorting lexicographically by distance and index fixes ties. -/
noncomputable def nearestBaseline (k : ℕ) (hk : 0 < k) (p : ℝ) : Fin k := by
  classical
  exact ((Finset.univ : Finset (Fin k)).toList.mergeSort (fun i j =>
    decide (|p - baseline i| < |p - baseline j| ∨
      (|p - baseline i| = |p - baseline j| ∧ i.val ≤ j.val)))).headD ⟨0, hk⟩

/-- Label-free decoder in Lemma 6.4: only Q, public baselines and Δ occur here. -/
noncomputable def bitDecoder (k : ℕ) (hk : 0 < k) (Δ : ℝ)
    (Q : Fin k → Measure ℝ) : Fin k → ℝ :=
  fun j => if (1 / 2 : ℝ) ≤ (k : ℝ) / Δ *
    ((k : ℝ)⁻¹ * ∑ i : Fin k,
      ∫ p, (if nearestBaseline k hk p = j then p - baseline i else 0) ∂Q i)
    then 1 else 0

/-- Either fixed tie sign is allowed; all nonzero differences have their ordinary sign. -/
noncomputable def signDecoder {R : ℕ} (tie : ℝ) (p t : Fin R → ℝ) : Fin R → ℝ :=
  fun i => if p i < t i then -1 else if t i < p i then 1 else tie

noncomputable def baselineError {R : ℕ} (p t : Fin R → ℝ) : ℝ :=
  (R : ℝ)⁻¹ * ∑ i : Fin R, |p i - t i|

end CalibratedMA.Randomized.Supplement


