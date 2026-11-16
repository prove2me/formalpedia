-- Prove2me | Definitions.Def_HSOSetCover_FullCover_Supplement_Adaptive
-- name    : HSOSetCover_FullCover_Supplement_Adaptive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:12:07.735666+00:00
-- url     : https://prove2.me/theorems/ab0fce85-e734-4fff-a823-acf009a663ad
-- title:
--   Adaptive runs: filtrations, productive turns, revealed progress, upper-policy conditions and universal batch limitations
-- statement:
--   An adaptive run on a probability space has a filtration $(\mathcal F_t)$, where $\mathcal F_t$ is the information available after the batch of turn $t$ is selected and before its responses arrive. Along it are the events that each turn is reached, and each turn's token cost $\mathrm{TOK}_t$ and latency $\mathrm{Lat}_t$. The run of an adaptive policy $\pi$ also records its retained, locally dual-certified partial covers, and it continues while the residual is nonempty. The run of an arbitrary selection-only PTM records the candidate sets proposed in each turn and the returned family, which consists of proposed sets.
--
--   A reached turn is **productive** if a nonempty partial cover is retained. With $U^{\mathrm{seen}}_t$ the union of the candidate sets proposed through turn $t$ ($U^{\mathrm{seen}}_0=\emptyset$), a turn makes **revealed progress** if $U^{\mathrm{seen}}_t\setminus U^{\mathrm{seen}}_{t-1}\neq\emptyset$.
--
--   The **upper-policy conditions** $(a,\underline p,\overline c,\overline\ell)$ hold if, conditionally on $\mathcal F_t$ on every reached turn:
--   1. the turn is productive with probability at least $\underline p$;
--   2. almost surely, a productive turn covers at least $\min\{a,|R|\}$ residual elements;
--   3. the conditional expected token cost is at most $\overline c$;
--   4. the latency is at most $\overline\ell$ almost surely.
--
--   The **universal batch limitations** $(b,\overline p,\underline c,\underline\ell)$ hold if, conditionally on $\mathcal F_t$ on every reached turn:
--   1. the turn makes revealed progress with probability at most $\overline p$;
--   2. almost surely, its revealed coverage is at most $b$;
--   3. the conditional expected token cost is at least $\underline c$;
--   4. the latency is at least $\underline\ell$ almost surely.
--
--   A PTM is **deadline- and turn-feasible** with turn bound $u$ if it issues at most $u$ turns and receives responses only from turns finishing by $D$. Finally,
--   $$\eta_U(u)=\mathbb P[\mathrm{Bin}(u,\underline p)\ge r_a],\qquad \mathrm{TOK}_U(u)=\overline c\sum_{t=0}^{u-1}\mathbb P[\mathrm{Bin}(t,\underline p)<r_a].$$
--
--   These objects state Theorem 5.
--
--   **Formalization Note** Turns are numbered from $0$. A conditional bound given $\mathcal F_t$ on the reached event is written for every $A\in\mathcal F_t$ inside that event, as $\mu(A\cap E)\ge\underline p\,\mu(A)$ or $\int_A\mathrm{TOK}_t\,d\mu\le\overline c\,\mu(A)$. Binomial probabilities are explicit sums.
-- source:
--   Jie Wang, Computing Weighted Set Covers with Heterogeneous Stochastic Oracles: Deadline-Constrained Token Complexity, STOC 2027 submission #191 (October 2026), SHA-256 d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf, §6, PDF pp. 11–12 / printed pp. 10–11 (model, productive turn, U^seen, upper-policy conditions, universal batch limitations, η_U, TOK_U); §3, PDF p. 5 (deadline- and turn-feasible); proof of Theorem 5, PDF p. 16 (F_t)

import Mathlib
import Definitions.Def_HSOSetCover_FullCover_Supplement_WSC

open MeasureTheory

namespace HSOSetCover.FullCover.Supplement

variable {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι] [DecidableEq ι]

/-! ### §6: adaptive selection with partial-cover responses (PDF pp. 11–12)

Turns are numbered `t = 0, 1, 2, …` (the paper's turn `t + 1`). -/

/-- `ℙ[Bin(n, p) ≥ r]`, written as the explicit binomial sum. -/
noncomputable def binomTailGe (n : ℕ) (p : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range (n + 1)).filter (fun j => r ≤ j), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- `ℙ[Bin(n, p) < r]`, written as the explicit binomial sum. -/
noncomputable def binomTailLt (n : ℕ) (p : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j < r), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- `η_U(u) = ℙ[Bin(u, p̲) ≥ r_a]` (PDF p. 12). -/
noncomputable def etaU (u : ℕ) (pLow : ℝ) (ra : ℕ) : ℝ := binomTailGe u pLow ra

/-- `TOK_U(u) = c̄ ∑_{t=0}^{u-1} ℙ[Bin(t, p̲) < r_a]` (PDF p. 12). -/
noncomputable def tokU (u : ℕ) (pLow cHigh : ℝ) (ra : ℕ) : ℝ :=
  cHigh * ∑ t ∈ Finset.range u, binomTailLt t pLow ra

/-- The common part of an adaptive run of a PTM on a probability space `Ω` (PDF pp. 11–12, 15–16):
a filtration `F`, where `F t` is the information available after the batch of turn `t` is
selected and before its responses are received; the event that turn `t` is reached (its batch is
issued); and the token cost and latency of the batch of turn `t`. Whether turn `t` is reached is
known at time `t`; the responses, token cost and latency of turn `t` are known at time `t + 1`.
An unreached turn costs nothing and takes no time. -/
structure TurnProcess (Ω : Type*) [m0 : MeasurableSpace Ω] where
  /-- The information after the batch of turn `t` is selected, before its responses. -/
  F : Filtration ℕ m0
  /-- Turn `t` is reached. -/
  reached : ℕ → Set Ω
  /-- The token cost `TOK_t` of the batch of turn `t`. -/
  tok : ℕ → Ω → ENNReal
  /-- The latency `Lat_t` of the batch of turn `t`. -/
  lat : ℕ → Ω → ℝ
  measurableSet_reached : ∀ t, MeasurableSet[F t] (reached t)
  reached_succ_subset : ∀ t, reached (t + 1) ⊆ reached t
  measurable_tok : ∀ t, Measurable[F (t + 1)] (tok t)
  measurable_lat : ∀ t, Measurable[F (t + 1)] (lat t)
  tok_eq_zero : ∀ t ω, ω ∉ reached t → tok t ω = 0
  lat_eq_zero : ∀ t ω, ω ∉ reached t → lat t ω = 0

/-- The run of an adaptive selection-only policy `π` that retains only locally dual-certified
partial covers and keeps selecting batches until the cover is complete (PDF pp. 11–12):
`ret t` is the partial cover retained at turn `t` (empty if nothing is retained), turn `0` is
reached, and turn `t + 1` is reached exactly when turn `t` was reached and the residual is still
nonempty. -/
structure PolicyRun (W : WSCInstance U ι) (ρ : ℝ) (y : U → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    extends TurnProcess Ω where
  /-- The partial cover retained at turn `t`. -/
  ret : ℕ → Ω → Finset ι
  measurableSet_ret : ∀ t P, MeasurableSet[F (t + 1)] {ω | ret t ω = P}
  ret_eq_empty : ∀ t ω, ω ∉ reached t → ret t ω = ∅
  /-- Only locally dual-certified partial covers are retained. -/
  ret_cert : ∀ t ω, (ret t ω).Nonempty →
    W.LocalDualCert ρ y (ret t ω) (W.residual (prefixUnion (fun s => ret s ω) t))
  reached_zero : reached 0 = Set.univ
  reached_succ : ∀ t, reached (t + 1) =
    reached t ∩ {ω | (W.residual (prefixUnion (fun s => ret s ω) (t + 1))).Nonempty}

namespace PolicyRun

variable {W : WSCInstance U ι} {ρ : ℝ} {y : U → ℝ} {Ω : Type*} [MeasurableSpace Ω]
variable (π : PolicyRun W ρ y Ω)

/-- The residual `R` before turn `t`. -/
def resid (t : ℕ) (ω : Ω) : Finset U := W.residual (prefixUnion (fun s => π.ret s ω) t)

/-- Turn `t` is **productive** (PDF p. 12): it is reached and a nonempty partial cover is
retained. -/
def productive (t : ℕ) : Set Ω := π.reached t ∩ {ω | (π.ret t ω).Nonempty}

/-- The **upper-policy conditions** (PDF p. 12) with parameters `a`, `p̲`, `c̄`, `ℓ̄`, conditional on
the information `F t` on every reached turn `t` (multiplicative form over the events of `F t`
inside the reached event): the turn is productive with conditional probability at least `p̲`;
almost surely, a productive turn covers at least `min{a, |R|}` residual elements; the conditional
expected token cost is at most `c̄`; and the latency is at most `ℓ̄` almost surely. -/
def UpperPolicyConditions (μ : Measure Ω) (a : ℕ) (pLow cHigh lHigh : ℝ) : Prop :=
  (∀ t A, MeasurableSet[π.F t] A → A ⊆ π.reached t →
      ENNReal.ofReal pLow * μ A ≤ μ (A ∩ π.productive t)) ∧
  (∀ t, ∀ᵐ ω ∂μ, ω ∈ π.productive t →
      min a (π.resid t ω).card ≤ (W.newlyCovered (π.ret t ω) (π.resid t ω)).card) ∧
  (∀ t A, MeasurableSet[π.F t] A → A ⊆ π.reached t →
      ∫⁻ ω in A, π.tok t ω ∂μ ≤ ENNReal.ofReal cHigh * μ A) ∧
  (∀ t, ∀ᵐ ω ∂μ, ω ∈ π.reached t → π.lat t ω ≤ lHigh)

/-- Running `π` until it completes or has used `u` turns returns a certified `ρ`-cover by `D`:
the partial covers retained in the first `u` turns form a certified `ρ`-cover and these turns
finish by `D`. -/
def successWithin (u : ℕ) (D : ℝ) : Set Ω :=
  {ω | W.CertifiedCover ρ (prefixUnion (fun s => π.ret s ω) u) ∧
    ∑ t ∈ Finset.range u, π.lat t ω ≤ D}

/-- The token cost `TOK_M = ∑_{t < u} TOK_t` of running `π` for at most `u` turns. -/
noncomputable def costWithin (u : ℕ) (ω : Ω) : ENNReal := ∑ t ∈ Finset.range u, π.tok t ω

end PolicyRun

/-- The run of an arbitrary selection-only PTM (PDF pp. 4–5, 12): `proposed t` indexes the valid
candidate sets proposed in the responses of turn `t` (retained or not), and `out` is the family the
PTM returns; selection-only means it consists of proposed sets. -/
structure SelectionRun (W : WSCInstance U ι) (Ω : Type*) [MeasurableSpace Ω]
    extends TurnProcess Ω where
  /-- The candidate sets proposed in the responses of turn `t`. -/
  proposed : ℕ → Ω → Finset ι
  /-- The returned family. -/
  out : Ω → Finset ι
  measurableSet_proposed : ∀ t P, MeasurableSet[F (t + 1)] {ω | proposed t ω = P}
  measurableSet_out : ∀ C, MeasurableSet {ω | out ω = C}
  proposed_eq_empty : ∀ t ω, ω ∉ reached t → proposed t ω = ∅
  /-- Selection-only: every returned set was proposed in some turn. -/
  out_subset : ∀ ω j, j ∈ out ω → ∃ t, j ∈ proposed t ω

namespace SelectionRun

variable {W : WSCInstance U ι} {Ω : Type*} [MeasurableSpace Ω] (M : SelectionRun W Ω)

/-- `U^seen_t`, the union of all candidate sets proposed through turn `t` (PDF p. 12). -/
def seen (t : ℕ) (ω : Ω) : Finset U := (Finset.range (t + 1)).biUnion fun s => W.covered (M.proposed s ω)

/-- `U^seen_{t-1}`, the union of all candidate sets proposed before turn `t` (`∅` before turn `0`). -/
def seenBefore (t : ℕ) (ω : Ω) : Finset U := (Finset.range t).biUnion fun s => W.covered (M.proposed s ω)

/-- Turn `t` makes **revealed progress** (PDF p. 12): `U^seen_t ∖ U^seen_{t-1} ≠ ∅`. -/
def revealedProgress (t : ℕ) : Set Ω := {ω | (M.seen t ω \ M.seenBefore t ω).Nonempty}

/-- The PTM is **deadline- and turn-feasible** with turn bound `u` and deadline `D` (PDF p. 5):
it issues at most `u` turns, and responses are received only from batches that finish by `D`
(turn `t` finishes at `∑_{s ≤ t} Lat_s`); calls unfinished at `D` are canceled. -/
def DeadlineTurnFeasible (u : ℕ) (D : ℝ) : Prop :=
  (∀ t, u ≤ t → M.reached t = ∅) ∧
    ∀ t ω, (M.proposed t ω).Nonempty → ∑ s ∈ Finset.range (t + 1), M.lat s ω ≤ D

/-- The **universal batch limitations** (PDF p. 12) with parameters `b`, `p̄`, `c̲`, `ℓ̲`,
conditional on the information `F t` on every reached turn `t`: the turn makes revealed progress
with conditional probability at most `p̄`; almost surely its revealed coverage is at most `b`;
its conditional expected token cost is at least `c̲`; and its latency is at least `ℓ̲` almost
surely. -/
def UniversalBatchLimitations (μ : Measure Ω) (b : ℕ) (pHigh cLow lLow : ℝ) : Prop :=
  (∀ t A, MeasurableSet[M.F t] A → A ⊆ M.reached t →
      μ (A ∩ M.revealedProgress t) ≤ ENNReal.ofReal pHigh * μ A) ∧
  (∀ t, ∀ᵐ ω ∂μ, ω ∈ M.reached t → (M.seen t ω \ M.seenBefore t ω).card ≤ b) ∧
  (∀ t A, MeasurableSet[M.F t] A → A ⊆ M.reached t →
      ENNReal.ofReal cLow * μ A ≤ ∫⁻ ω in A, M.tok t ω ∂μ) ∧
  (∀ t, ∀ᵐ ω ∂μ, ω ∈ M.reached t → lLow ≤ M.lat t ω)

/-- The event that the PTM returns a certified `ρ`-cover (by `D`, under `DeadlineTurnFeasible`). -/
def successEvent (ρ : ℝ) : Set Ω := {ω | W.CertifiedCover ρ (M.out ω)}

/-- The total token cost `TOK_M = ∑_{t < u} TOK_t` of a PTM issuing at most `u` turns. -/
noncomputable def totalCost (u : ℕ) (ω : Ω) : ENNReal := ∑ t ∈ Finset.range u, M.tok t ω

end SelectionRun

end HSOSetCover.FullCover.Supplement


