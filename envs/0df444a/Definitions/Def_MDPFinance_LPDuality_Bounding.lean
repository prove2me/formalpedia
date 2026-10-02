-- Prove2me | Definitions.Def_MDPFinance_LPDuality_Bounding
-- name    : MDPFinance_LPDuality_Bounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:51:11.803643+00:00
-- url     : https://prove2.me/theorems/ba46edbb-5f34-4452-bd94-02e84b9e3fd0
-- title:
--   Bounding functions, IB_b spaces, and (SA) (restated from chunk 07a)
-- statement:
--   Restates chunk `07a`'s bounding-function vocabulary (upper bounding functions, bounding
--   functions, $IB_b$/$IB_b^+$, the weighted norm $\|\cdot\|_b$, and the Structure Assumption (SA)),
--   needed throughout §7.5 for Howard's algorithm's contracting-case clause (Theorem 7.5.1c) and for
--   this mission's own goal (Theorem 7.5.8), which cites chunk `07a`'s Theorem 7.3.5 by name.
--
--   **Moderation note.** $\int b\,dQ\le\alpha_b b$ as a Lebesgue integral; (SA) includes $IM\subset\mathbb M(E)$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 195/205, Definitions 7.1.2, 7.3.1 (restated for this chunk)

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- An upper bounding function for the infinite-horizon model (Bäuerle–Rieder, Definition 7.1.2,
p. 195, PDF 206): `b : E → ℝ_{\ge 0}` measurable with `r^+(x,a) \le c_r b(x)` and
`\int b(x')Q(dx'|x,a) \le \alpha_b b(x)` on `D` (a Lebesgue integral, `b ≥ 0`). -/
structure IsUpperBoundingFunction (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ) :
    Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hαb : 0 ≤ αb
  hr : ∀ xa ∈ M.D, max (M.r xa) 0 ≤ cr * b xa.1
  hQ : ∀ xa ∈ M.D, ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q xa) ≤ ENNReal.ofReal (αb * b xa.1)

/-- A bounding function (Bäuerle–Rieder, Definition 7.3.1, p. 205, PDF 216): the two-sided
version, `|r(x,a)| \le c_r b(x)`, that makes `(IB_b,\|\cdot\|_b)` a Banach space and `T`/`T_f`
contractions of modulus `\beta\alpha_b` (Lemma 7.3.3). -/
structure IsBoundingFunction (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ) : Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hαb : 0 ≤ αb
  hr : ∀ xa ∈ M.D, |M.r xa| ≤ cr * b xa.1
  hQ : ∀ xa ∈ M.D, ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q xa) ≤ ENNReal.ofReal (αb * b xa.1)

/-- `IB_b := \{v : E \to \mathbb R \mid v \text{ measurable}, \|v\|_b < \infty\}`, represented (as
`MDPFinance.Semicontinuous.IBb`, chunk `02b`, is) via the equivalent bound `|v(x)| \le c\,b(x)` —
this chapter's contracting-model value functions are genuinely real-valued (`(IB_b,\|\cdot\|_b)`
a Banach space, p. 205), unlike `IM(E)`'s `EReal`-valued functions used for the general theory. -/
def IBb (b : E → ℝ) : Set (E → ℝ) :=
  {v | Measurable v ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |v x| ≤ c * b x}

/-- `IB_b^+ := \{v \in IM(E) \mid v^+(x) \le c\,b(x)\}` (Bäuerle–Rieder, p. 29, PDF 44, restated),
the `EReal`-valued regularity class used by the semicontinuous existence theorems (7.2.1, 7.2.3). -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

/-- `\|v\|_b := \sup_x |v(x)|/b(x)` (Bäuerle–Rieder, p. 29/205, the weighted supremum norm),
restated for real-valued `v` (real `sSup`, total/junk-safe if unbounded, as elsewhere in this
series). -/
noncomputable def normb (b : E → ℝ) (v : E → ℝ) : ℝ :=
  ⨆ x, |v x| / b x

/-- `T_f'v(x) := r(x,f(x)) + \beta \int v(x') Q(dx'|x,f(x))`, the real-valued (Bochner-integral)
counterpart of `Tf` used on the Banach space `IB_b` (Bäuerle–Rieder, p. 206, PDF 217, Lemma
7.3.3), avoiding `EReal`/`erealIntegral` machinery for the genuinely real-valued contracting
theory. -/
noncomputable def Tf' (M : MarkovDecisionModel E A) (f : E → A) (v : E → ℝ) (x : E) : ℝ :=
  M.r (x, f x) + M.β * ∫ x', v x' ∂(M.Q (x, f x))

/-- `T'v(x) := \sup_{a \in D(x)} [r(x,a) + \beta \int v(x') Q(dx'|x,a)]`, the real-valued
counterpart of `T` (real `sSup`, total/junk-safe if unbounded, as elsewhere in this series). -/
noncomputable def T' (M : MarkovDecisionModel E A) (v : E → ℝ) (x : E) : ℝ :=
  ⨆ a ∈ M.Dx x, M.r (x, a) + M.β * ∫ x', v x' ∂(M.Q (x, a))

/-- The Structure Assumption (SA) (Bäuerle–Rieder, p. 199, PDF 211): `(i)`-`(iii)` are Section
2.5's Structure Assumption (`0 \in IM`, `T` maps `IM` into itself, every `v \in IM` has a
maximizer in `\Delta`); `(iv)` additionally pins the *limit* value function `J`. -/
def StructureAssumptionSA (M : MarkovDecisionModel E A) (IM' : Set (E → EReal)) (Δ : Set (E → A))
    (Jlim : E → EReal) : Prop :=
  IM' ⊆ IM E ∧
  (0 : E → EReal) ∈ IM' ∧
  (∀ v ∈ IM', T M v ∈ IM') ∧
  (∀ v ∈ IM', ∃ f ∈ Δ, IsMaximizerOf M v f) ∧
  Jlim ∈ IM' ∧ Jlim = T M Jlim

end MDPFinance.LPDuality


