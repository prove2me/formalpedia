-- Prove2me | Definitions.Def_ImpatientQPTAS_Coupling
-- name    : ImpatientQPTAS_Coupling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:45.679201+00:00
-- url     : https://prove2.me/theorems/5f429eea-347d-4663-906b-35b93e53511f
-- title:
--   §§3.2–3.5, pp.15–21 — milestones, the map $\mu$, the coupling $(\mathcal Y^\downarrow,\mathcal Y^\uparrow)$ and the two processes
-- statement:
--   Fix $\epsilon=1/m$ and a shifting parameter $\gamma\in\{1,\dots,m\}$. The **milestones** are $t_k=(k-1)m+\gamma$, $k\ge1$, with the convention $t_0=0$; every other stage is **regular**, and $\mu(t)$ is the $t$-th regular stage.
--
--   On a probability space take mutually independent Bernoulli variables: $Y^\uparrow_{i,t}$ with mean $p^\uparrow_i$; $Z_{i,\tau}$, $\tau$ regular, with mean $p^\downarrow_i/p^\uparrow_i$; $W_{i,\tau}$, $\tau=t_k$, with mean $(p^\downarrow_i-\xi_{i,\tau})/(1-\xi_{i,\tau})$, where $\xi_{i,\tau}=1-\big((1-p^\uparrow_i)/(1-p^\downarrow_i)\big)^{t_k-t_{k-1}-1}$; and $V_{i,\tau}$, $\tau$ a milestone, with mean $p^\downarrow_i$.
--
--   The variables $Y^\downarrow_{i,\tau}$ are defined inductively: $Y^\downarrow_{i,\tau}=Y^\uparrow_{i,\mu^{-1}(\tau)}Z_{i,\tau}$ for regular $\tau$, and for $\tau=t_k$,
--   $$
--   Y^\downarrow_{i,\tau}=1-(1-W_{i,\tau})\prod_{s=t_{k-1}+1}^{t_k-1}\big(1-Y^\uparrow_{i,\mu^{-1}(s)}\big)
--   $$
--   if $Y^\downarrow_{i,1}=\dots=Y^\downarrow_{i,\tau-1}=0$, and $V_{i,\tau}$ otherwise.
--
--   Under a policy $S$ from a start set $B$, $A^{\downarrow}_\tau$ is the rounded-down process driven by $\mathcal Y^\downarrow$. The process $A^{\uparrow}_t$ is the rounded-up process of eq. (10): in stage $t$ it serves $S(\mu(t),A^\downarrow_{\mu(t)})$ if that customer is available, and no one otherwise, and then the customers with $Y^\uparrow_{i,t}=1$ depart.
--
--   This coupling is the main tool in the proof of Theorem 2.6.
--
--   **Formalization Note** Coins are `Bool`-valued, `true` being the outcome $1$, and `Coupling` asks for independence over exactly the index sets of the page. `regCount τ` counts the regular stages at most $\tau$: it is $\mu^{-1}(\tau)$ on a regular stage and $\mu^{-1}(\tau-1)$ on a milestone, $0$ being the empty history at $\tau=1\in M_\gamma$. `Admissible` collects the setting of §3: $m>4$, $1\le\gamma\le m$, and every customer average. Stages are $1$-based, and $t_0=0$ is not a stage.
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §3.2, p.15; §3.3, pp.16–17, eqs. (2), (3); §3.4, p.18; §3.5, pp.20–21, eq. (10)

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS

open MeasureTheory ProbabilityTheory

/-- `τ` is a milestone of `M_γ`, §3.2, Segev, arXiv:2209.13878v1, p.15: `τ = (k−1)·m + γ` for some
`k ≥ 1`, where `m = 1/ε`. The 0-th milestone `t₀ = 0` is "not a concrete stage" and is not one here. -/
def isMilestone (m γ τ : ℕ) : Prop := γ ≤ τ ∧ m ∣ τ - γ

instance (m γ τ : ℕ) : Decidable (isMilestone m γ τ) := by
  unfold isMilestone; infer_instance

/-- A regular stage, §3.2, p.15: a stage `τ ≥ 1` that is not a milestone. -/
def IsRegular (m γ τ : ℕ) : Prop := 1 ≤ τ ∧ ¬ isMilestone m γ τ

instance (m γ : ℕ) : DecidablePred (IsRegular m γ) := fun τ => by
  unfold IsRegular; infer_instance

/-- The milestone `t_k`: `t₀ = 0` and `t_k = (k−1)·m + γ` for `k ≥ 1`, §3.2, p.15. -/
def tk (m γ : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => k * m + γ

/-- For a milestone `τ = t_k`, the previous milestone `t_{k−1}`. -/
def prevMs (m γ τ : ℕ) : ℕ := tk m γ ((τ - γ) / m)

/-- For a stage `τ`, the largest `t_j ≤ τ`, `j ≥ 0`. For a regular `τ ∈ (t_{k−1}, t_k)` this is
`t_{k−1}`. -/
def lastMs (m γ τ : ℕ) : ℕ := if τ < γ then 0 else τ - (τ - γ) % m

/-- The map `μ`, §3.2, p.15: "μ(t) is simply the t-th regular stage". Stages start at `1`, and
`Nat.nth` counts from `0`. -/
noncomputable def mu (m γ t : ℕ) : ℕ := Nat.nth (IsRegular m γ) (t - 1)

/-- The number of regular stages at most `τ`. On a regular stage this is `μ⁻¹(τ)`, §3.2, p.15. On a
milestone `τ` it is `μ⁻¹(τ − 1)`, and it is `0`, the empty history, at `τ = 1 ∈ M_γ`. -/
def regCount (m γ τ : ℕ) : ℕ := Nat.count (IsRegular m γ) (τ + 1)

/-- The elementary coins of the coupling, §3.3, pp.16–17: `Y↑_{i,t}`, `Z_{i,τ}`, `W_{i,τ}`,
`V_{i,τ}`. -/
inductive Coin (n : ℕ)
  | up (i : Fin n) (t : ℕ)
  | z (i : Fin n) (τ : ℕ)
  | w (i : Fin n) (τ : ℕ)
  | v (i : Fin n) (τ : ℕ)

/-- The index sets of §3.3: `Y↑` over stages `t ≥ 1`, `Z` over regular stages, `W` and `V` over
milestones. -/
def Coin.Valid {n : ℕ} (m γ : ℕ) : Coin n → Prop
  | .up _ t => 1 ≤ t
  | .z _ τ => IsRegular m γ τ
  | .w _ τ => isMilestone m γ τ
  | .v _ τ => isMilestone m γ τ

/-- `ξ_{i,τ} = 1 − ((1 − p↑_i)/(1 − p↓_i))^(t_k − t_{k−1} − 1)` for `τ = t_k`, §3.3, p.16. -/
noncomputable def xi (m γ : ℕ) (x : ℝ) (τ : ℕ) : ℝ :=
  1 - ((1 - pUp (1 / (m : ℝ)) x) / (1 - pDown (1 / (m : ℝ)) x)) ^ (τ - prevMs m γ τ - 1)

/-- The success probabilities of §3.3, pp.16–17, for the departure probabilities `p`, at
`ε = 1/m`: `p↑_i` for `Y↑`; `p↓_i/p↑_i` for `Z`; `(p↓_i − ξ_{i,τ})/(1 − ξ_{i,τ})` for `W`; `p↓_i`
for `V`. -/
noncomputable def bias {n : ℕ} (m γ : ℕ) (p : Fin n → ℝ) : Coin n → ℝ
  | .up i _ => pUp (1 / (m : ℝ)) (p i)
  | .z i _ => pDown (1 / (m : ℝ)) (p i) / pUp (1 / (m : ℝ)) (p i)
  | .w i τ => (pDown (1 / (m : ℝ)) (p i) - xi m γ (p i) τ) / (1 - xi m γ (p i) τ)
  | .v i _ => pDown (1 / (m : ℝ)) (p i)

/-- The setting of §3: `ε = 1/m ∈ (0, 1/4)`, the shifting parameter `γ ∈ {1, …, 1/ε}`, and every
customer average, `p_i ∈ [ε/n², 1 − ε/n]` (§2.3, p.10). -/
def Admissible {n : ℕ} (m γ : ℕ) (p : Fin n → ℝ) : Prop :=
  4 < m ∧ 1 ≤ γ ∧ γ ≤ m ∧
    ∀ i, 1 / (m : ℝ) / (n : ℝ) ^ 2 ≤ p i ∧ p i ≤ 1 - 1 / (m : ℝ) / (n : ℝ)

/-- **The initial sampling of the coupling**, §3.3, Segev, arXiv:2209.13878v1, pp.16–17: on a
probability space, the coins with the laws of `bias`, mutually independent over the index sets of
`Coin.Valid`.

**Formalization Note.** A coin takes values in `Bool`, `true` being the outcome `1`. Coins outside the
index sets exist in the type and are never read by `Ydown`, `downSet`, `upSet`. -/
structure Coupling {n : ℕ} (m γ : ℕ) (p : Fin n → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) where
  coin : Coin n → Ω → Bool
  measurable_coin : ∀ c, Measurable (coin c)
  law : ∀ c, c.Valid m γ → P {ω | coin c ω = true} = ENNReal.ofReal (bias m γ p c)
  indep : iIndepFun (fun c : {c : Coin n // c.Valid m γ} => coin c.1) P

namespace Coupling

variable {n m γ : ℕ} {p : Fin n → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- One step of the inductive construction of `Y↓`, §3.3, p.17. `b` says whether `Y↓_{i,1}, …,
Y↓_{i,τ−1}` all vanish. Regular `τ`: eq. (2), `Y↑_{i,μ⁻¹(τ)}·Z_{i,τ}`. Milestone `τ = t_k`: eq. (3),
`1 − (1 − W_{i,τ})·Π_{s=t_{k−1}+1}^{t_k−1} (1 − Y↑_{i,μ⁻¹(s)})` if `b`, and `V_{i,τ}` otherwise. -/
noncomputable def stepDown (C : Coupling m γ p P) (i : Fin n) (τ : ℕ) (ω : Ω) (b : Bool) : Bool :=
  if isMilestone m γ τ then
    if b = true then
      C.coin (.w i τ) ω ||
        decide (∃ s ∈ Finset.Ioo (prevMs m γ τ) τ, C.coin (.up i (regCount m γ s)) ω = true)
    else C.coin (.v i τ) ω
  else C.coin (.up i (regCount m γ τ)) ω && C.coin (.z i τ) ω

/-- Whether `Y↓_{i,1} = ⋯ = Y↓_{i,τ} = 0`. -/
noncomputable def noDep (C : Coupling m γ p P) (i : Fin n) (ω : Ω) : ℕ → Bool
  | 0 => true
  | τ + 1 => C.noDep i ω τ && !(C.stepDown i (τ + 1) ω (C.noDep i ω τ))

/-- `Y↓_{i,τ}`, stage `τ ≥ 1`, eqs. (2)–(3), p.17. -/
noncomputable def Ydown (C : Coupling m γ p P) (i : Fin n) (τ : ℕ) (ω : Ω) : Bool :=
  C.stepDown i τ ω (C.noDep i ω (τ - 1))

/-- The rounded-down process driven by `Y↓`, recursion on `τ − 1`; see `downSet`. -/
noncomputable def downAux (C : Coupling m γ p P) (S : Policy n) (B : Finset (Fin n)) (ω : Ω) :
    ℕ → Finset (Fin n)
  | 0 => B
  | k + 1 =>
    (C.downAux S B ω k \ (S (k + 1) (C.downAux S B ω k)).toFinset) \
      Finset.univ.filter fun i => C.Ydown i (k + 1) ω = true

/-- `A^{Y↓}_τ`, §3.2, p.16: the customers available at the beginning of stage `τ ≥ 1` of the
rounded-down process, under `S`, from the start set `B`. -/
noncomputable def downSet (C : Coupling m γ p P) (S : Policy n) (B : Finset (Fin n)) (ω : Ω)
    (τ : ℕ) : Finset (Fin n) :=
  C.downAux S B ω (τ - 1)

/-- The action of `S` at stage `μ(t)` of the simulated rounded-down process. -/
noncomputable def simAction (C : Coupling m γ p P) (S : Policy n) (B : Finset (Fin n)) (ω : Ω)
    (t : ℕ) : Option (Fin n) :=
  S (mu m γ t) (C.downSet S B ω (mu m γ t))

/-- The rounded-up process under the policy `S^γ↑` of eq. (10), recursion on `t − 1`; see `upSet`. -/
noncomputable def upAux (C : Coupling m γ p P) (S : Policy n) (B : Finset (Fin n)) (ω : Ω) :
    ℕ → Finset (Fin n)
  | 0 => B
  | k + 1 =>
    (C.upAux S B ω k \ (C.simAction S B ω (k + 1)).toFinset) \
      Finset.univ.filter fun i => C.coin (.up i (k + 1)) ω = true

/-- `A^{Y↑}_t`, §3.5, p.20: the customers available at the beginning of stage `t ≥ 1` of the
rounded-up process. In stage `t`, eq. (10) serves the customer `S(μ(t), A^{Y↓}_{μ(t)})` if that customer
is available, and otherwise no one; then the customers with `Y↑_{i,t} = 1` depart.

**Formalization Note.** The two clocks stay apart: `upSet` runs on `t`, `downSet` on `μ(t)`. Removing
an unavailable customer changes nothing, so `upAux` needs no test. -/
noncomputable def upSet (C : Coupling m γ p P) (S : Policy n) (B : Finset (Fin n)) (ω : Ω)
    (t : ℕ) : Finset (Fin n) :=
  C.upAux S B ω (t - 1)

end Coupling

/-- The coins of the history up to `τ`, §3.4, p.18: `Z^{≤τ}`, `W^{≤τ}`, `V^{≤τ}` and `Y↑^{≤ regCount τ}`,
where `regCount τ` is `μ⁻¹(τ)` on a regular stage and `μ⁻¹(τ − 1)` on a milestone. -/
def Coin.Past {n : ℕ} (m γ τ : ℕ) : Coin n → Prop
  | .up _ t => t ≤ regCount m γ τ
  | .z _ s => s ≤ τ
  | .w _ s => s ≤ τ
  | .v _ s => s ≤ τ

end ImpatientQPTAS


