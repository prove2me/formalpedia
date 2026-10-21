-- Prove2me | Definitions.Def_StableFees_UserGain_Model
-- name    : StableFees_UserGain_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:38.845026+00:00
-- url     : https://prove2.me/theorems/3ef6a290-4272-4ede-8c64-c83a9e6623f1
-- title:
--   §3–§4, pp. 10–16 — user values and the minimum included fee protocol
-- statement:
--   A block has $K$ transaction slots, and an active user's value and bid lie in $[0,\bar V]$. The other $m$ active users have bids $x=(x_j)_{j=1}^m$. Write $V_k(x)$ for their $k$th highest bid, counting ties. The considered bidder with value $v$ and bid $b$ wins exactly when $b>V_K(x)$; on winning, they pay the lowest included fee, $\min\{b,V_{K-1}(x)\}$, and otherwise pay nothing. Their payoff is therefore
--
--   $$u_K(v,b;x)=\begin{cases}v-\min\{b,V_{K-1}(x)\},&b>V_K(x),\\0,&b\le V_K(x).\end{cases}$$
--
--   For a fixed profile $x$, the gain from strategic bidding is $G_{K,\bar V}(v;x)=\sup_{b\in[0,\bar V]}u_K(v,b;x)-u_K(v,v;x)$. It measures the best improvement over truthful bidding, rather than assigning the gain a closed form. The common law $\mu$ of other users' values has density $g$ on $[0,\bar V]$: $g$ is continuous, $g(z)\ge\epsilon>0$ there, and $\int_0^{\bar V}g(z)\,dz=1$. Since a user chooses a bid without seeing the others' bids, the expected gain from strategic bidding against $m$ truthful others with i.i.d. values $X\sim\mu^{\otimes m}$ is
--
--   $$\mathcal G_{K,\bar V}(v;m)=\sup_{b\in[0,\bar V]}\mathbb E[u_K(v,b;X)]-\mathbb E[u_K(v,v;X)].$$
--
--   This is the model shared by the mission's statements.
--
--   **Formalization Note** The order statistic is defined by a real supremum and used only for $1\le k\le m$. A bid tied with $V_K(x)$ loses. Other users' values are i.i.d. under the product of the density law. The payoff concerns the current block.
-- source:
--   Basu, Easley, O'Hara, Sirer, Towards a Functional Fee Market for Cryptocurrencies, arXiv:1901.06830v1, pp. 10–16, §3 Model and §4 Protocol

import Mathlib
open MeasureTheory

namespace StableFees.UserGain

/-- The k-th highest of a finite vector, counting repeated entries. Used with `1 ≤ k ≤ m`. -/
noncomputable def kthHighest {m : ℕ} (x : Fin m → ℝ) (k : ℕ) : ℝ :=
  sSup {t : ℝ | k ≤ (Finset.univ.filter (fun j => t ≤ x j)).card}

/-- A bidder wins precisely when their bid beats the K-th highest other bid.
The uniform price is the lowest winning bid. -/
noncomputable def payoff (K : ℕ) {m : ℕ} (v b : ℝ) (x : Fin m → ℝ) : ℝ :=
  if kthHighest x K < b then v - min b (kthHighest x (K - 1)) else 0

/-- Best attainable payoff over admissible bids, less the truthful payoff. -/
noncomputable def gain (K : ℕ) (Vbar : ℝ) {m : ℕ} (v : ℝ) (x : Fin m → ℝ) : ℝ :=
  (⨆ b : Set.Icc (0 : ℝ) Vbar, payoff K v (b : ℝ) x) - payoff K v v x

/-- Expected gain from strategic bidding of a bidder with value `v` facing `m` other active
users whose values are i.i.d. with law `μ` and who bid truthfully: the best expected payoff over
bids `b ∈ [0, V̄]`, chosen without seeing the others' bids, less the expected truthful payoff. -/
noncomputable def expectedGain (K : ℕ) (Vbar : ℝ) (μ : Measure ℝ) (m : ℕ) (v : ℝ) : ℝ :=
  (⨆ b : Set.Icc (0 : ℝ) Vbar,
      ∫ x, payoff K v (b : ℝ) x ∂(Measure.pi fun _ : Fin m => μ)) -
    ∫ x, payoff K v v x ∂(Measure.pi fun _ : Fin m => μ)

/-- Distribution of one active user's value. -/
noncomputable def valueLaw (Vbar : ℝ) (g : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 Vbar)).withDensity (fun v => ENNReal.ofReal (g v))

/-- The paper's standing assumptions on a continuous, strictly positive density. -/
def ValueDensity (Vbar : ℝ) (g : ℝ → ℝ) (ε : ℝ) : Prop :=
  0 < Vbar ∧ ContinuousOn g (Set.Icc 0 Vbar) ∧ 0 < ε ∧
    (∀ v ∈ Set.Icc 0 Vbar, ε ≤ g v) ∧ ∫ v in Set.Icc 0 Vbar, g v = 1

end StableFees.UserGain


