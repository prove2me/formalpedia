-- Prove2me | Definitions.Def_Fundraising_Competition_Setting
-- name    : Fundraising_Competition_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:02:35.602826+00:00
-- url     : https://prove2.me/theorems/f2cb4fe4-59fd-4d6a-b571-0f1f339cd629
-- title:
--   §3–§4 — the competition fundraising game: MNL shares (4), contact weights, expected donations (5), PPD, the lexicographic HO problem (6), Nash equilibrium, Assumption 1
-- statement:
--   This file sets up the competition game between $n$ humanitarian organizations (HOs) $i \in I = \{1,\dots,n\}$ that raise money from a continuum of donors after a disaster, in the base-utility coordinates of problem (6) of the paper.
--
--   **Primitives.** For each HO $i$: an interval $[a_i, b_i]$ of base utilities it can offer donors, a required funding $B_i$, a unit performance $\delta_i(s_i)$ (the fraction of each donated dollar usable now, as a function of the base utility $s_i$), and an effort cost $C_i(x_i)$ of contacting a fraction $x_i \in [0,1]$ of the donors. The mean donor budget is $z$.
--
--   **MNL shares (4).** If the HOs in a set $J \ni i$ contact a donor, HO $i$ receives the fraction
--   $$\theta^J_i(s) = \frac{e^{s_i}}{1 + \sum_{j \in J} e^{s_j}}$$
--   of the donor's budget (the $1$ is the outside option of not donating).
--
--   **Contact weights and expected donations (5).** For a contacting set $J \ni i$ (equivalently a vector $a \in A_i$ with $J = J_a$), the probability that the other HOs contacting the donor are exactly $J \setminus \{i\}$ is
--   $$w^J_i(x) = \prod_{j \in J,\, j \neq i} x_j \prod_{j \notin J} (1 - x_j),$$
--   and HO $i$'s expected donations are
--   $$\mathbb E[D_i(s;x)] = z \, x_i \sum_{J \ni i} w^J_i(x)\, \theta^J_i(s).$$
--   The unit performance per donor contacted is $PPD_i(s;x) = \delta_i(s_i)\, z \sum_{J \ni i} w^J_i(x)\, \theta^J_i(s)$.
--
--   **HO problem (6) and equilibrium.** Given the other HOs' strategies $(s_{-i}, x_{-i})$, HO $i$ chooses $(s_i, x_i) \in [a_i,b_i]\times[0,1]$ lexicographically: it first minimizes its funding gap $(B_i - \delta_i(s_i)\mathbb E[D_i(s;x)])^+$ over the box, and among the gap minimizers maximizes its utility
--   $$U_i(s_i, x_i) = \min\big(\delta_i(s_i)\mathbb E[D_i(s;x)],\, B_i\big) - C_i(x_i).$$
--   A (pure) Nash equilibrium is a profile $(s;x) \in \prod_i [a_i,b_i] \times [0,1]^n$ in which every HO's own strategy solves its problem (6).
--
--   **Standing hypotheses.** $n \ge 1$; $a_i \le b_i$; $B_i > 0$; $z > 0$; $C_i : [0,1] \to \mathbb R_+$ strictly increasing; $\delta_i$ twice continuously differentiable, with $0 < \delta_i \le 1$ on $[a_i, b_i]$.
--
--   **Assumption 1** (p. 16): for $s_i \in [a_i, b_i]$,
--   $$\frac{\partial^2 \log \delta_i(s_i)}{\partial s_i^2} \le -\frac14 + \frac{e^{s_i}}{(1 + e^{s_i})^2}.$$
--
--   **Formalization Note.** HOs are `Fin n`. The paper's sum over $a \in A_i = \{a \in \{0,1\}^n : a_i = 1\}$ is written as a sum over finite sets $J$ with $i \in J$ (the bijection $a \mapsto J_a$), and $w^a_i$ as products over $J \setminus\{i\}$ and the complement of $J$ (no real powers). $\delta_i$ is a primitive function of $s_i$ on all of $\mathbb R$ (the paper's $\delta_i \circ s_i^{-1}$); twice continuous differentiability on $\mathbb R$ stands for the paper's "twice differentiable". $B_i > 0$, $z > 0$ and $\delta_i > 0$ are made explicit (the paper's "required funding", "average budget", and the division by $\delta_i$ in (7)). Expected donations are taken as the formula (5); Lemma 1's Gumbel derivation is not formalized. Assumption 1 is a separate predicate, assumed only where the paper uses it.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), pp. 8–16, (1)–(6), Lemma 1 (4), Lemma 2 (5), Assumption 1, Proposition 1 (definition of PPD)

import Mathlib

namespace Fundraising.Competition

open Finset

/-- The primitives of the competition fundraising game among `n` humanitarian organizations
(HOs) `i : Fin n`, in base-utility coordinates (problem (6), p. 15): HO `i` chooses a base
utility `s i ∈ [a i, b i]` and an effort `x i ∈ [0, 1]`; `B i` is its required funding,
`δ i : ℝ → ℝ` its unit performance as a function of the base utility, `C i` its effort cost,
and `z` the mean donor budget. -/
structure Setting (n : ℕ) where
  a : Fin n → ℝ
  b : Fin n → ℝ
  B : Fin n → ℝ
  z : ℝ
  δ : Fin n → ℝ → ℝ
  C : Fin n → ℝ → ℝ

variable {n : ℕ}

/-- MNL share (4) of HO `i` among the contacting set `J` (with the outside option of base
utility 0): `θ^J_i(s) = exp(s_i) / (1 + Σ_{j ∈ J} exp(s_j))`. -/
noncomputable def theta (s : Fin n → ℝ) (J : Finset (Fin n)) (i : Fin n) : ℝ :=
  Real.exp (s i) / (1 + ∑ j ∈ J, Real.exp (s j))

/-- The contacting sets that contain HO `i`; `J ↔ a` with `J = J_a`, so this is `A_i`. -/
def contactSets (i : Fin n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun J => i ∈ J)

/-- Contact weight `w^a_i = Π_{j ≠ i} x_j^{a_j} (1 - x_j)^{1 - a_j}` written over the
contacting set `J = J_a`: the product of `x_j` over `j ∈ J, j ≠ i` and of `1 - x_j` over
`j ∉ J`. -/
noncomputable def weight (x : Fin n → ℝ) (i : Fin n) (J : Finset (Fin n)) : ℝ :=
  (∏ j ∈ J.erase i, x j) * ∏ j ∈ Jᶜ, (1 - x j)

/-- `Σ_{a ∈ A_i} w^a_i θ^{J_a}_i(s)`. -/
noncomputable def shareSum (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ J ∈ contactSets i, weight x i J * theta s J i

/-- Expected donations (5): `E[D_i(s; x)] = z · x_i · Σ_{a ∈ A_i} w^a_i θ^{J_a}_i(s)`. -/
noncomputable def expDonation (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  S.z * x i * shareSum s x i

/-- Unit performance per donor contacted (Proposition 1):
`PPD_i(s; x) = δ_i(s_i) · z · Σ_{a ∈ A_i} w^a_i θ^{J_a}_i(s)`. -/
noncomputable def PPD (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  S.δ i (s i) * S.z * shareSum s x i

/-- Funding gap of HO `i` in (6): `(B_i - δ_i(s_i) E[D_i(s; x)])^+`. -/
noncomputable def gap (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  max (S.B i - S.δ i (s i) * expDonation S s x i) 0

/-- Utility of HO `i` in (6): `U_i = min(δ_i(s_i) E[D_i(s; x)], B_i) - C_i(x_i)`. -/
noncomputable def utility (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  min (S.δ i (s i) * expDonation S s x i) (S.B i) - S.C i (x i)

/-- HO `i`'s strategy box `[a_i, b_i] × [0, 1]`. -/
def stratBox (S : Setting n) (i : Fin n) : Set (ℝ × ℝ) :=
  Set.Icc (S.a i) (S.b i) ×ˢ Set.Icc 0 1

/-- The constraint set of (6): strategies `(σ, ξ)` of HO `i` in its box that minimize the
funding gap over the box, the other HOs' strategies `(s_{-i}, x_{-i})` held fixed. -/
def gapMinimizers (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) : Set (ℝ × ℝ) :=
  {p | p ∈ stratBox S i ∧ ∀ q ∈ stratBox S i,
    gap S (Function.update s i p.1) (Function.update x i p.2) i ≤
      gap S (Function.update s i q.1) (Function.update x i q.2) i}

/-- `(σ, ξ)` solves HO `i`'s problem (6) against `(s_{-i}, x_{-i})`: it minimizes the funding
gap over the box and, among the gap minimizers, maximizes the utility `U_i`. -/
def IsBestResponse (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) (p : ℝ × ℝ) : Prop :=
  p ∈ gapMinimizers S s x i ∧ ∀ q ∈ gapMinimizers S s x i,
    utility S (Function.update s i q.1) (Function.update x i q.2) i ≤
      utility S (Function.update s i p.1) (Function.update x i p.2) i

/-- The profile `(s; x)` lies in `Π_i [a_i, b_i] × [0, 1]^n`. -/
def InProfileBox (S : Setting n) (s x : Fin n → ℝ) : Prop :=
  ∀ i, s i ∈ Set.Icc (S.a i) (S.b i) ∧ x i ∈ Set.Icc (0 : ℝ) 1

/-- Pure Nash equilibrium of the competition game: a profile in the box in which every HO's
own strategy `(s_i, x_i)` solves its problem (6). -/
def IsNE (S : Setting n) (s x : Fin n → ℝ) : Prop :=
  InProfileBox S s x ∧ ∀ i, IsBestResponse S s x i (s i, x i)

/-- Standing hypotheses of §3–§4: `n ≥ 1`; `a_i ≤ b_i`; required funding `B_i > 0`; mean donor budget
`z > 0`; effort cost `C_i : [0,1] → ℝ₊` strictly increasing; unit performance `δ_i` twice
continuously differentiable with values in `(0, 1]` on `[a_i, b_i]`. -/
structure Standing (S : Setting n) : Prop where
  n_pos : 0 < n
  a_le_b : ∀ i, S.a i ≤ S.b i
  B_pos : ∀ i, 0 < S.B i
  z_pos : 0 < S.z
  C_nonneg : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ S.C i t
  C_strictMonoOn : ∀ i, StrictMonoOn (S.C i) (Set.Icc 0 1)
  δ_contDiff : ∀ i, ContDiff ℝ 2 (S.δ i)
  δ_pos : ∀ i, ∀ t ∈ Set.Icc (S.a i) (S.b i), 0 < S.δ i t
  δ_le_one : ∀ i, ∀ t ∈ Set.Icc (S.a i) (S.b i), S.δ i t ≤ 1

/-- Assumption 1 (p. 16): `∂² log δ_i(s_i) / ∂s_i² ≤ -1/4 + exp(s_i)/(1 + exp(s_i))²` for
`s_i ∈ [a_i, b_i]`. -/
def Assumption1 (S : Setting n) : Prop :=
  ∀ i, ∀ t ∈ Set.Icc (S.a i) (S.b i),
    deriv (deriv (fun u => Real.log (S.δ i u))) t ≤ -1 / 4 + Real.exp t / (1 + Real.exp t) ^ 2

end Fundraising.Competition


