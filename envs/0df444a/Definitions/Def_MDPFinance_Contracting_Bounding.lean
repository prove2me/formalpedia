-- Prove2me | Definitions.Def_MDPFinance_Contracting_Bounding
-- name    : MDPFinance_Contracting_Bounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:42:35.142976+00:00
-- url     : https://prove2.me/theorems/a2078bfb-0565-428b-9306-9a52ad188676
-- title:
--   Upper bounding and bounding functions, IB_b spaces, and the Structure Assumption (SA)
-- statement:
--   An **upper bounding function** (Definition 7.1.2) is a measurable $b : E \to \mathbb R_{\ge 0}$
--   with $r^+(x,a) \le c_rb(x)$ and $\int b(x')Q(dx'|x,a) \le \alpha_bb(x)$ on $D$ — enough to
--   guarantee Assumptions (A) and (C) when $\beta\alpha_b < 1$. A **bounding function** (Definition
--   7.3.1) strengthens this to a two-sided bound $|r(x,a)| \le c_rb(x)$, which makes $(IB_b,
--   \|\cdot\|_b)$, the space of real-valued functions with finite weighted supremum norm $\|v\|_b :=
--   \sup_x |v(x)|/b(x)$, into a genuine Banach space — the setting for this mission's contracting
--   theory (§7.3). $IB_b^+$ is the analogous $EReal$-valued class used by the semicontinuous
--   existence theorems (§7.2), where value functions are not a priori known to be finite.
--
--   The **Structure Assumption (SA)** strengthens Chapter 2's Structure Assumption (a closed class
--   $IM$ containing $0$, mapped into itself by $T$, on which maximizers always exist) with a fourth
--   condition pinning the *limit* value function: $J \in IM$ and $J = TJ$. This extra condition is
--   exactly what earlier general theory (SAN) lacks and what Example 7.2.4 shows can genuinely fail.
--
--   **Formalization Note.** `Tf'`/`T'` (the real-valued, Bochner-integral counterparts of `Tf`/`T`)
--   are introduced here alongside `IB_b` since Lemma 7.3.3's contraction inequalities are naturally
--   stated on real-valued (not `EReal`-valued) functions.
--
--   **Moderation note.** The bound $\int b\,dQ\le\alpha_b b$ is a Lebesgue integral ($b\ge 0$), so a $b$ without finite expectation cannot pass it with a default value; (SA) includes $IM\subset\mathbb M(E)$ (measurable, $<+\infty$), as in the book.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 195/199/205, Definitions 7.1.2, 7.3.1 and the Structure Assumption (SA)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Contracting

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
2.5's Structure Assumption (`IM ⊂ IM(E)`, `0 \in IM`, `T` maps `IM` into itself, every `v \in IM`
has a maximizer in `\Delta`); `(iv)` additionally pins the *limit* value function `J`. -/
def StructureAssumptionSA (M : MarkovDecisionModel E A) (IM' : Set (E → EReal)) (Δ : Set (E → A))
    (Jlim : E → EReal) : Prop :=
  IM' ⊆ IM E ∧
  (0 : E → EReal) ∈ IM' ∧
  (∀ v ∈ IM', T M v ∈ IM') ∧
  (∀ v ∈ IM', ∃ f ∈ Δ, IsMaximizerOf M v f) ∧
  Jlim ∈ IM' ∧ Jlim = T M Jlim

end MDPFinance.Contracting


