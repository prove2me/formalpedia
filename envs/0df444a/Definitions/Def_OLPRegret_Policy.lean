-- Prove2me | Definitions.Def_OLPRegret_Policy
-- name    : OLPRegret_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:40.659965+00:00
-- url     : https://prove2.me/theorems/7e10a307-1755-4329-8367-5d0b9cf4ea6f
-- title:
--   Samples, non-anticipating policies, inventory and online value
-- statement:
--   A sample of horizon $n$ lists the customers $(u_t,a_t)$ of periods $t=n,n-1,\dots,1$, i.i.d. from $\mu$. You begin with stock $n\beta$. In period $t$ you see $(u_t,a_t)$ and decide $x_t\in\{0,1\}$; you may accept only if $a_t$ fits into the stock $tb_t$. The stock then becomes $tb_t-x_ta_t$, so that
--   $$
--   b_n=\beta,\qquad b_{t-1}=\psi_t^{b_t}(x_ta_t),\qquad \psi_t^b(a)=\begin{cases}(tb-a)/(t-1)&t>1,\\0&t=1.\end{cases}
--   $$
--   The online value is $\sum_t x_tu_t$.
--
--   A **non-anticipating policy** chooses, in each period $t$, a decision bit that is a measurable function of the customers of periods $n,n-1,\dots,t$ only. The realized decision $x_t$ is that bit masked by feasibility, so every policy is feasible and every feasible non-anticipating deterministic policy arises this way. These objects carry both the optimal policy and Algorithm 2.
--
--   **Formalization Note** The index $t$ of `Fin n` holds the customer of period $t+1$, so the first $k$ entries are periods $1,\dots,k$. A `Scheme` is a raw decision bit depending on the index, the stock and the sample; `Policy.scheme` and `ruleScheme` are its two sources, and only the first is the quantified policy class. Non-anticipation is in the type of `Policy.decide`.
-- source:
--   Bray, arXiv:1912.08917v6, §4.1, pp.17–18: the model, (13), (15)

import Mathlib
import Definitions.Def_OLPRegret_Assumptions

set_option autoImplicit false

open MeasureTheory

namespace OLPRegret

/-- A sample of horizon `n`: the customers of periods `n, …, 1`.

**Formalization Note** The paper counts periods backward from `n` to `1`
(Bray, arXiv:1912.08917v6, §4.1, p.17). The index `t : Fin n` holds the customer of period
`t + 1`, so periods are processed from the top index down, and the first `k` entries of a sample
are the customers of periods `1, …, k`. -/
abbrev Sample (m n : ℕ) := Fin n → Customer m

/-- The period `t + 1` carried by the index `t : Fin n`. -/
abbrev period {n : ℕ} (t : Fin n) : ℕ := t.val + 1

/-- The law of a sample of horizon `n`: Assumption 1, i.i.d. customers from `μ`
(Bray, arXiv:1912.08917v6, p.17). -/
noncomputable def sampleLaw {m : ℕ} (μ : Measure (Customer m)) [SigmaFinite μ] (n : ℕ) :
    Measure (Sample m n) :=
  Measure.pi fun _ => μ

/-- The inventory update `ψₜᵇ(a) = (tb − a)/(t − 1)` for `t > 1`, and `0` for `t = 1`
(Bray, arXiv:1912.08917v6, (13), p.18). -/
noncomputable def psi {m : ℕ} (t : ℕ) (b a : E m) : E m :=
  if 1 < t then ((t : ℝ) - 1)⁻¹ • ((t : ℝ) • b - a) else 0

/-- A raw decision scheme of horizon `n`: for a period index, the current stock and the sample, the
bit "accept if the customer fits". Non-anticipation is not part of this type; see `Policy` and
`ruleScheme` for the two ways schemes arise. -/
abbrev Scheme (m n : ℕ) := Fin n → E m → Sample m n → Bool

/-- The period-`t` customer is accepted from stock `s`: the scheme says so and the bundle fits,
`aₜ ≤ s` (the constraint `xₜaₜ ≤ tb` of Bray, arXiv:1912.08917v6, (12), p.18). -/
def Accepts {m n : ℕ} (D : Scheme m n) (ω : Sample m n) (t : Fin n) (s : E m) : Prop :=
  D t s ω = true ∧ VLe (ω t).2 s

open scoped Classical in
/-- The stock left after `k` decisions: `nβ` initially, and each decision for the period `n − k`
subtracts the accepted bundle (Bray, arXiv:1912.08917v6, §4.1, p.17).

**Formalization Note** The natural-number subtraction `n - 1 - k` is guarded by `k < n`. -/
noncomputable def remaining {m n : ℕ} (D : Scheme m n) (β : E m) (ω : Sample m n) : ℕ → E m
  | 0 => (n : ℝ) • β
  | k + 1 =>
    if h : k < n then
      if Accepts D ω ⟨n - 1 - k, by omega⟩ (remaining D β ω k) then
        remaining D β ω k - (ω ⟨n - 1 - k, by omega⟩).2
      else remaining D β ω k
    else remaining D β ω k

/-- The stock `t bₜ` available at the beginning of period `t`, for `t ≤ n`. -/
noncomputable def stock {m n : ℕ} (D : Scheme m n) (β : E m) (ω : Sample m n) (t : ℕ) : E m :=
  remaining D β ω (n - t)

/-- The inventory vector `bₜ` per remaining period, in the paper's scaling: `bₜ = stockₜ / t`, so
`bₙ = β` and `bₜ₋₁ = ψₜ^{bₜ}(xₜaₜ)` for `t > 1` (Bray, arXiv:1912.08917v6, §4.1, p.17; §4.5, p.30). -/
noncomputable def inventory {m n : ℕ} (D : Scheme m n) (β : E m) (ω : Sample m n) (t : ℕ) : E m :=
  (t : ℝ)⁻¹ • stock D β ω t

open scoped Classical in
/-- The realized decision `xₜ ∈ {0, 1}` of period `t`: the scheme's bit masked by feasibility. -/
noncomputable def decision {m n : ℕ} (D : Scheme m n) (β : E m) (ω : Sample m n) (t : Fin n) : ℝ :=
  if Accepts D ω t (stock D β ω (period t)) then 1 else 0

/-- The online value `Σₜ xₜuₜ` collected by a scheme (Bray, arXiv:1912.08917v6, (15), p.18;
(26), p.26). -/
noncomputable def onlineValue {m n : ℕ} (D : Scheme m n) (β : E m) (ω : Sample m n) : ℝ :=
  ∑ t, decision D β ω t * (ω t).1

/-- What is visible when period `t` is decided: the customers of periods `n, n − 1, …, t`. -/
abbrev History (m n : ℕ) (t : Fin n) := {s : Fin n // t ≤ s} → Customer m

/-- The visible part of a sample at period `t`. -/
def history {m n : ℕ} (ω : Sample m n) (t : Fin n) : History m n t := fun s => ω s.1

/-- A **non-anticipating policy** of horizon `n`: the decision bit of each period is a measurable
function of the customers of that period and of the earlier-decided periods `n, …, t`
(Bray, arXiv:1912.08917v6, §4.1, pp.17–18: "you don't observe variables uₜ and aₜ until the
beginning of period t").

**Formalization Note** Non-anticipation is in the type: `decide t` cannot read a period below `t`.
The realized decision is this bit masked by feasibility (`Accepts`), so every masked policy is
feasible for (16), and every feasible non-anticipating deterministic policy arises this way. -/
structure Policy (m n : ℕ) where
  /-- The decision bit of each period, read off the visible customers. -/
  decide : (t : Fin n) → History m n t → Bool
  /-- The decision bit is measurable. -/
  measurable_decide : ∀ t, Measurable (decide t)

/-- The scheme of a non-anticipating policy. -/
def Policy.scheme {m n : ℕ} (π : Policy m n) : Scheme m n :=
  fun t _ ω => π.decide t (history ω t)

/-- The scheme of a feedback rule `r t bₜ (uₜ, aₜ)`, which decides from the period, the inventory
`bₜ` and the current customer. -/
noncomputable def ruleScheme {m n : ℕ} (r : ℕ → E m → Customer m → Bool) : Scheme m n :=
  fun t s ω => r (period t) (((period t : ℕ) : ℝ)⁻¹ • s) (ω t)

end OLPRegret


