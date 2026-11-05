-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_model
-- name    : BauerleRiederMDP_Indifference_Market_model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:53.47923+00:00
-- url     : https://prove2.me/theorems/920a1986-e96b-42fd-b061-737cf6ad730d
-- title:
--   The Markov Decision Model of the multiperiod indifference problem
-- statement:
--   For a horizon $N$ and a claim $H$, the utility maximization problem of Section 4.9 is the Markov Decision Model with
--
--   1. states $(x,s,\hat s)$, the wealth and the two prices;
--   2. actions $a\in\mathbb R$, the amount invested in the traded asset, all admissible in every state;
--   3. transition function $T((x,s,\hat s),a,(z_1,z_2))=(x+a(z_1-1),\,sz_1,\,\hat sz_2)$;
--   4. disturbance law $Q^Z$, the joint distribution of $(\tilde R_{n+1},\hat R_{n+1})$ given by $(p_1,p_2,p_3,p_4)$, independent of the state and the action;
--   5. rewards $r_n\equiv 0$ and $g_N(x,s,\hat s)=-e^{-\gamma(x-h(s,\hat s))}$.
--
--   The transition kernel is the image of $\mathbb P$ on $\Omega$ under $\omega\mapsto T((x,s,\hat s),a,(\tilde R(\omega),\hat R(\omega)))$. The module also defines this next-state map and shows that it is measurable.
--
--   **Formalization Note** The model is an instance of the book's Definition 2.1.1 as published on the platform. Its state type is $\mathbb R^3$, which contains the book's $E=\mathbb R\times\mathbb R_+^2$. Because $d>0$ and $\hat d\ge 0$, a process started in $E$ stays in $E$, so the behaviour of a decision rule outside $E$ affects no value on $E$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.138, the model bullets

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_BauerleRiederMDP_Indifference_Market
import Definitions.Def_BauerleRiederMDP_Indifference_Claim

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.Indifference

namespace Market

/-- The transition function `T((x, s, ŝ), a, (z₁, z₂)) := (x + a(z₁ - 1), s z₁, ŝ z₂)`
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.138,
PDF 152). -/
def transition (e : ℝ × ℝ × ℝ) (a z₁ z₂ : ℝ) : ℝ × ℝ × ℝ :=
  (e.1 + a * (z₁ - 1), e.2.1 * z₁, e.2.2 * z₂)

/-- The next-state map of §4.9: the state `T((x, s, ŝ), a, (R̃(ω), R̂(ω)))` reached from
`((x, s, ŝ), a)` at the sample point `ω` of `Ω`. -/
def nextState (M : Market) (z : ((ℝ × ℝ × ℝ) × ℝ) × Fin 4) : ℝ × ℝ × ℝ :=
  transition z.1.1 z.1.2 (M.Rt z.2) (M.Rh z.2)

theorem measurable_nextState (M : Market) : Measurable M.nextState :=
  measurable_from_prod_countable_left fun k => by
    unfold nextState transition
    fun_prop

/-- The transition kernel of the model of §4.9 (p.138, PDF 152): from `((x, s, ŝ), a)` the next
state is `T((x, s, ŝ), a, (z₁, z₂))` with `(z₁, z₂)` distributed by `Q^Z`, the joint distribution
of `(R̃_{n+1}, R̂_{n+1})` given by `(p₁, p₂, p₃, p₄)`, independent of `((x, s, ŝ), a)`. It is the
image of `ℙ` on `Ω` under `ω ↦ T((x, s, ŝ), a, (R̃(ω), R̂(ω)))`. -/
noncomputable def kernel (M : Market) : Kernel ((ℝ × ℝ × ℝ) × ℝ) (ℝ × ℝ × ℝ) :=
  (Kernel.id ×ₖ Kernel.const _ M.P).map M.nextState

instance (M : Market) : IsMarkovKernel M.kernel :=
  Kernel.IsMarkovKernel.map _ M.measurable_nextState

/-- The Markov Decision Model of §4.9 with horizon `N` and claim `H` (Bäuerle & Rieder (2011),
p.138, PDF 152): `A := ℝ`, `D(x, s, ŝ) := A`, transition `T`, `Q^Z`, `r_n ≡ 0` and
`g_N(x, s, ŝ) := -e^{-γ(x - h(s, ŝ))}`.

**Formalization Note.** The model is an instance of the book's Definition 2.1.1
(`MDPFinance.Bellman.MarkovDecisionModel`). Its state type is all of `ℝ × ℝ × ℝ`, which contains the
book's `E = ℝ × ℝ₊²`: since `d > 0`, and `d̂ ≥ 0` (the book's `𝒵 := ℝ₊ × ℝ₊`, a hypothesis of every
statement about this model), a process started in `E` stays in `E`, so what a
decision rule does outside `E` does not affect any value at a state of `E`, and every measurable
decision rule on `E` extends to one on `ℝ × ℝ × ℝ`. -/
noncomputable def model (M : Market) (N : ℕ) (H : Claim) :
    MDPFinance.Bellman.MarkovDecisionModel (ℝ × ℝ × ℝ) ℝ N where
  D := fun _ => Set.univ
  hD_meas := fun _ _ => MeasurableSet.univ
  hD_sel := fun _ _ => ⟨fun _ => 0, measurable_const, fun _ => Set.mem_univ _⟩
  Q := fun _ => M.kernel
  hQ_prob := fun _ _ xa => inferInstance
  r := fun _ _ => 0
  hr_meas := fun _ _ => measurable_const
  g := fun e => -Real.exp (-M.γ * (e.1 - H e.2.1 e.2.2))
  hg_meas := by
    have hH : Measurable fun e : ℝ × ℝ × ℝ => H e.2.1 e.2.2 :=
      H.measurable.comp (measurable_snd.fst.prodMk measurable_snd.snd)
    exact ((measurable_const.mul (measurable_fst.sub hH)).exp).neg

end Market

end BauerleRiederMDP.Indifference


