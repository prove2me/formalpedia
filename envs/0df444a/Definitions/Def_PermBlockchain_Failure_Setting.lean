-- Prove2me | Definitions.Def_PermBlockchain_Failure_Setting
-- name    : PermBlockchain_Failure_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:49.001897+00:00
-- url     : https://prove2.me/theorems/2883c11b-68fd-4a6e-be2c-cb01f2e8c2e5
-- title:
--   §3, §4.1, App. A.1 — reduced-form blockchain supply chain: parameters, Assumption 1, Proposition A.1 outcomes, welfare (10)–(13), adoption game (8)
-- statement:
--   This file sets up the supply chain model of Iyengar, Saleh, Sethuraman and Wang in the reduced form that the paper's own proofs use: every welfare quantity is evaluated at the closed-form equilibrium outcome of Proposition A.1.
--
--   **Agents and parameters.** There are two vendors $h$ and $l$ and a set $M$ of $4m$ manufacturers, $m$ of each type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$. A consumer gets utility $H$ from a good of her own horizontal type and $L$ otherwise, plus a vertical utility $\xi_i\in\{h,l\}$. Write $\Delta := H-L$, so $H = L+\Delta$; the parameter $L$ is fixed and $\Delta$ varies. The high type vendor has cost $c_h(x)=\gamma x$, the low type vendor has cost $c_l$ with derivative $c_l'$, the outside option $\varphi_k$ of a consumer has distribution function $G$ (the cdf of a law $\mu$ on $\mathbb R$), and manufacturer $i$ pays $\chi_i$ to join the blockchain.
--
--   **Standing assumptions.** $m\ge 2$; $0\le L$; $h>l\ge 0$; $\gamma>0$; $\chi_i>0$ for all $i$; $\mu$ is a probability measure without atoms, with $\mu((-\infty,0))=0$ and $\mu((a,b))>0$ whenever $0\le a<b$ (a continuous distribution supported on $[0,\infty)$); $\varphi$ has a finite mean; $c_l$ is strictly increasing and convex on $[0,\infty)$ with $c_l(0)=0$, and has there a strictly increasing derivative $c_l'$.
--
--   **Assumption 1, item 3** at $\Delta$ reads
--   $$c_l'(0)<\gamma<c_l'\Big(G\big(\tfrac{H+L+h+l}{2}-\gamma\big)\Big),\qquad H=L+\Delta .$$
--
--   **Extended inverse.** $(c_l')^{-1}(x):=\sup\{s\ge 0: c_l'(s)\le x\}$, which is $0$ for $x<c_l'(0)$.
--
--   **Scenarios and outcomes (Proposition A.1).** In full adoption $F$ every manufacturer adopts, in partial adoption $P$ exactly the high type manufacturers adopt, in non-adoption $N$ nobody adopts. The consumer utilities are $u^F=u^P=H+h-\gamma$ and $u^N=\frac{H+L+h+l}{2}-\gamma$; the vendor prices are $\Psi_h=\gamma$ and
--   $$\Psi^F_l=\max\{\gamma-(h-l),0\},\quad \Psi^P_l=\max\{\gamma-(h-l)-\tfrac{H-L}{2},0\},\quad \Psi^N_l=\gamma;$$
--   the low type market shares are $s^F_l=(c_l')^{-1}(\gamma-(h-l))$, $s^P_l=(c_l')^{-1}(\gamma-(h-l)-\frac{H-L}{2})$, $s^N_l=(c_l')^{-1}(\gamma)$, and $s^X_h=G(u^X)-s^X_l$.
--
--   **Welfare.** At scenario $X\in\{F,P,N\}$,
--   $$W_C^X=\mathbb E\big[\max\{u^X,\varphi\}\big],\qquad W_V^X=(\Psi_h s^X_h-\gamma s^X_h)+(\Psi^X_l s^X_l-c_l(s^X_l)),$$
--   $$W_M^X=\sum_{i\in M}\big(\Pi(a^X_i,a^X_{-i})-\chi_i a^X_i\big),\qquad W^X=W_V^X+W_M^X+W_C^X,$$
--   where $a^X$ is the adoption profile of the scenario and the gross profit $\Pi$ is $0$ for every profile (Bertrand competition, as the paper's proofs use).
--
--   **Adoption game.** Manufacturer $i$ chooses $a_i\in\{0,1\}$ with payoff $\Pi(a_i,a_{-i})-\chi_i a_i$ as in (8); a profile is an *equilibrium* if it is a pure Nash equilibrium of this game. An *adoption failure* at $\Delta$ means $W^N<W^F$ while full adoption is not an equilibrium.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Manufacturers are triples in $\mathrm{Fin}\,2\times\mathrm{Bool}\times\mathrm{Fin}\,m$ (the Boolean is "$\xi_i=h$"), adoption profiles are Boolean functions, and the pure Nash condition is `AGT.IsPureNash` of the published `agt_games` vocabulary. $G$ is `ProbabilityTheory.cdf μ`. The welfare quantities are those of Proposition A.1's closed forms, not of an equilibrium of the full signalling game, which the paper does not define precisely; $\Pi\equiv 0$ is the paper's statement on p. 34. The finite mean of $\varphi$ is an addition that the paper uses without stating it.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), pp. 8–15, 28, 34, displays (1)–(2), (8)–(13), Assumption 1, Proposition A.1, proof of Proposition 4.3

import Mathlib
import Definitions.Def_agt_games

namespace PermBlockchain.Failure

open MeasureTheory ProbabilityTheory

/-- **Manufacturers** (Iyengar–Saleh–Sethuraman–Wang, §3.1, p. 8). The set `M` of `4m`
manufacturers, `m` of each type in `{A, B} × {h, l}`: a manufacturer is a triple
(horizontal type `q_i ∈ {A, B}` as `Fin 2`, vertical type `ξ_i` with `true` = `h` and
`false` = `l`, copy index in `Fin m`), so that `|M_i| = m` for every type by construction. -/
abbrev Mfr (m : ℕ) := Fin 2 × Bool × Fin m

/-- `ξ_i = h`: manufacturer `i` is of the high vertical type, i.e. `i ∈ M_h`. -/
def Mfr.IsHigh {m : ℕ} (i : Mfr m) : Prop := i.2.1 = true

instance {m : ℕ} (i : Mfr m) : Decidable i.IsHigh := by
  unfold Mfr.IsHigh; infer_instance

/-- **Parameters of the supply chain** (§3.1, pp. 8–10; App. A, p. 28).
* `L` — horizontal utility `L` of a good of the other horizontal type (2); the own-type utility
  is `H = L + Δ`, and `Δ` is not a field: every statement takes it as a separate argument;
* `h`, `l` — vertical utilities `ξ_i ∈ {h, l}` of high and low type goods (1);
* `γ` — slope of the high type vendor's linear cost `c_h(x) = γ x` (p. 28);
* `cl`, `cl'` — the low type vendor's cost `c_l` and its derivative `c_l'`;
* `μ` — the law of the consumers' outside option `φ_k`, whose cdf is `G`;
* `χ i` — manufacturer `i`'s blockchain adoption cost `χ_i` (p. 12).
The signal accuracy is `α = 1/2` throughout (p. 9) and enters only through Proposition A.1's
closed forms below. -/
structure Model (m : ℕ) where
  L : ℝ
  h : ℝ
  l : ℝ
  γ : ℝ
  cl : ℝ → ℝ
  cl' : ℝ → ℝ
  μ : Measure ℝ
  χ : Mfr m → ℝ

namespace Model

variable {m : ℕ} (M : Model m)

/-- `G`, the cumulative distribution function of the outside option `φ_k` (p. 9). -/
noncomputable def G (x : ℝ) : ℝ := ProbabilityTheory.cdf M.μ x

/-- **Standing assumptions** of §3 and App. A:
* `m ≥ 2` (p. 8); `0 ≤ L` (p. 9, "0 ≤ L < H"; `L < H` is `0 < Δ`, stated where needed);
  `h > l ≥ 0` (p. 8); `c_h(x) = γ x` with `γ > 0` (p. 28); `χ_i > 0` (p. 12);
* `G` is a continuous distribution supported on `[0, ∞)` (p. 9): `μ` is a probability measure
  without atoms, `μ((-∞, 0)) = 0`, and every open interval `(a, b) ⊆ [0, ∞)` has positive mass;
* the outside option has a finite mean (`Integrable id μ`) — a disclosed addition, implicit in
  the proof of Proposition 4.1 (p. 33), without which the consumer welfare (12) is not finite;
* `c_l` is strictly increasing and convex (p. 10), `c_l(0) = 0` (Assumption 1.1, p. 28), and
  `c_l` has on `[0, ∞)` a strictly increasing derivative `c_l'` (Assumption 1.2, p. 28),
  one-sided at `0`. -/
structure Standing : Prop where
  two_le_m : 2 ≤ m
  L_nonneg : 0 ≤ M.L
  l_nonneg : 0 ≤ M.l
  l_lt_h : M.l < M.h
  γ_pos : 0 < M.γ
  χ_pos : ∀ i, 0 < M.χ i
  isProbabilityMeasure : IsProbabilityMeasure M.μ
  noAtoms : NullSingletonClass M.μ
  μ_Iio_zero : M.μ (Set.Iio 0) = 0
  μ_Ioo_pos : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < M.μ (Set.Ioo a b)
  integrable_id : Integrable id M.μ
  cl_zero : M.cl 0 = 0
  cl_strictMonoOn : StrictMonoOn M.cl (Set.Ici 0)
  cl_convexOn : ConvexOn ℝ (Set.Ici 0) M.cl
  hasDerivWithinAt_cl : ∀ x : ℝ, 0 ≤ x → HasDerivWithinAt M.cl (M.cl' x) (Set.Ici 0) x
  cl'_strictMonoOn : StrictMonoOn M.cl' (Set.Ici 0)

/-- **Assumption 1, item 3** (p. 28) at `H = L + Δ`:
`c_l'(0) < γ < c_l'(G((H + L + h + l)/2 − γ))`. It depends on `Δ` through `H`. -/
def Assumption1 (Δ : ℝ) : Prop :=
  M.cl' 0 < M.γ ∧ M.γ < M.cl' (M.G ((M.L + Δ + M.L + M.h + M.l) / 2 - M.γ))

/-- The **extended inverse** `(c_l')⁻¹` (App. A, p. 28): `sup {s ≥ 0 | c_l'(s) ≤ x}`. It is `0`
for `x < c_l'(0)` (the supremum of the empty set), which is the paper's extension, and the unique
`s ≥ 0` with `c_l'(s) = x` when `x` is a value of `c_l'` on `[0, ∞)`. -/
noncomputable def cinv (x : ℝ) : ℝ := sSup {s : ℝ | 0 ≤ s ∧ M.cl' s ≤ x}

end Model

/-- The three **adoption scenarios** of §4 (p. 14): full adoption `F`, partial adoption `P`,
non-adoption `N`. -/
inductive Scenario
  | F
  | P
  | N
  deriving DecidableEq

/-- The **adoption profile** `(a_i)_{i ∈ M}` of a scenario (p. 14), `true` meaning `a_i = 1`:
* `F`: `a_i = 1` for all `i ∈ M`;
* `P`: `a_i = 1` for all `i` with `ξ_i = h` and `a_i = 0` for all `i` with `ξ_i = l`;
* `N`: `a_i = 0` for all `i ∈ M`. -/
def Scenario.profile {m : ℕ} : Scenario → Mfr m → Bool
  | .F => fun _ => true
  | .P => fun i => i.2.1
  | .N => fun _ => false

namespace Model

variable {m : ℕ} (M : Model m)

/-- Expected utility `u_{i(k)k}` of every consumer at the equilibrium of scenario `X`
(Proposition A.1, p. 28), with `H = L + Δ`:
`u^F = u^P = H + h − γ`, `u^N = (H + L + h + l)/2 − γ`. -/
noncomputable def u : Scenario → ℝ → ℝ
  | .F, Δ => M.L + Δ + M.h - M.γ
  | .P, Δ => M.L + Δ + M.h - M.γ
  | .N, Δ => (M.L + Δ + M.L + M.h + M.l) / 2 - M.γ

/-- Vendor price `Ψ_h = γ` paid by every high type manufacturer, in all three scenarios
(Proposition A.1, p. 28). -/
def Ψh : ℝ := M.γ

/-- Vendor price `Ψ_l` paid by every low type manufacturer (Proposition A.1, p. 28), with
`H − L = Δ`: `Ψ^F_l = max{γ − (h − l), 0}`, `Ψ^P_l = max{γ − (h − l) − (H − L)/2, 0}`,
`Ψ^N_l = γ`. -/
noncomputable def Ψl : Scenario → ℝ → ℝ
  | .F, _ => max (M.γ - (M.h - M.l)) 0
  | .P, Δ => max (M.γ - (M.h - M.l) - Δ / 2) 0
  | .N, _ => M.γ

/-- Total low type market share `s_l = Σ_{i ∈ M_l} s_i` (Proposition A.1, p. 28):
`s^F_l = (c_l')⁻¹(γ − (h − l))`, `s^P_l = (c_l')⁻¹(γ − (h − l) − (H − L)/2)`,
`s^N_l = (c_l')⁻¹(γ)`. -/
noncomputable def sl : Scenario → ℝ → ℝ
  | .F, _ => M.cinv (M.γ - (M.h - M.l))
  | .P, Δ => M.cinv (M.γ - (M.h - M.l) - Δ / 2)
  | .N, _ => M.cinv M.γ

/-- Total high type market share `s_h = Σ_{i ∈ M_h} s_i` (Proposition A.1, p. 28):
`s^X_h = G(u^X) − s^X_l`. -/
noncomputable def sh (X : Scenario) (Δ : ℝ) : ℝ := M.G (M.u X Δ) - M.sl X Δ

/-- **Consumer welfare** (12), p. 15, at scenario `X`: since every consumer's best manufacturer
offers `u^X` (Proposition A.1), `W_C^X = ∫_0^1 E[max{u^X, φ_k}] dk = E[max{u^X, φ}]`. -/
noncomputable def WC (X : Scenario) (Δ : ℝ) : ℝ := ∫ φ, max (M.u X Δ) φ ∂M.μ

/-- **Vendor welfare** (10), p. 15, at scenario `X`, with fulfilment `σ_i = s_i` and
`c_h(x) = γ x`: `W_V^X = (Ψ_h s^X_h − γ s^X_h) + (Ψ^X_l s^X_l − c_l(s^X_l))`. -/
noncomputable def WV (X : Scenario) (Δ : ℝ) : ℝ :=
  (M.Ψh * M.sh X Δ - M.γ * M.sh X Δ) + (M.Ψl X Δ * M.sl X Δ - M.cl (M.sl X Δ))

/-- Manufacturer `i`'s **gross expected profit** `Π(a_i, a_{−i})` of (9). By Proposition A.1 it
is `0` in every subgame, whatever the adoption profile, because of price competition (proof of
Proposition 4.3, p. 34; proof of Proposition 4.7, p. 36). -/
def grossProfit (_a : Mfr m → Bool) (_i : Mfr m) : ℝ := 0

/-- Manufacturer `i`'s **adoption payoff** `Π(a_i, a_{−i}) − χ_i a_i` of (8), p. 13. -/
def payoff (a : Mfr m → Bool) (i : Mfr m) : ℝ :=
  grossProfit a i - M.χ i * (if a i then 1 else 0)

/-- **Manufacturer welfare** at scenario `X`: `W_M^X = Σ_{i ∈ M} (Π(a_i, a_{−i}) − χ_i a_i)` at
the scenario's fixed profile (the reading of (11), p. 15, used in the proof of Proposition 4.3,
p. 34). -/
noncomputable def WM (X : Scenario) : ℝ := ∑ i, M.payoff X.profile i

/-- **Total welfare** (13), p. 15: `W^X = W_V^X + W_M^X + W_C^X`. -/
noncomputable def W (X : Scenario) (Δ : ℝ) : ℝ := M.WV X Δ + M.WM X + M.WC X Δ

/-- An adoption profile `a` is an **equilibrium** of the adoption stage: a pure Nash equilibrium
of the game (8) in which each manufacturer `i` chooses `a_i ∈ {0, 1}` with payoff
`Π(a_i, a_{−i}) − χ_i a_i`, i.e. no manufacturer gains by a unilateral switch of `a_i`. -/
def IsEquilibrium (a : Mfr m → Bool) : Prop :=
  AGT.IsPureNash (S := fun _ : Mfr m => Bool) (fun i b => M.payoff b i) a

/-- **Adoption failure** at `Δ` (p. 14, p. 19): full blockchain adoption enhances global welfare,
`W^N < W^F`, yet full adoption is not an equilibrium. -/
def AdoptionFailure (Δ : ℝ) : Prop :=
  M.W .N Δ < M.W .F Δ ∧ ¬ M.IsEquilibrium Scenario.F.profile

/-- The same model with the adoption costs replaced by `χ'`. -/
def withχ (χ' : Mfr m → ℝ) : Model m := { M with χ := χ' }

end Model

end PermBlockchain.Failure


