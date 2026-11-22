-- Prove2me | Definitions.Def_PreservePast_Supplement_RandAchievesAvg
-- name    : PreservePast_Supplement_RandAchievesAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:25:01.262087+00:00
-- url     : https://prove2.me/theorems/9f8bc665-f431-44d5-b32d-e5780d5167ce
-- title:
--   Average protection of $K$ regression tasks: promise, success and $B$-bit protocols
-- statement:
--   Let $W_0\in\mathbb R^{m\times n}$ be the public checkpoint and let a history consist of $K\ge 1$ regression tasks with loss increments $f_1,\dots,f_K$ (the published `PreservePast.Task`). The **average loss increment** of an update $H$ is
--   $$\bar f(H)=\frac1K\sum_{i=1}^K f_i(H).$$
--
--   Under **average protection** the loss being protected is $\bar f$:
--
--   1. a unit query $(x,p)$ is **promised** if some $H^\ast$ with $\operatorname{rank}H^\ast\le r$, $\|H^\ast\|_F\le R$ and $H^\ast x=p$ has $\bar f(H^\ast)\le 0$;
--   2. a response $H$ is **successful** if $\operatorname{rank}H\le r$, $\|H\|_F\le R$, $\tfrac12\|Hx-p\|^2\le\xi$ and $\bar f(H)\le\epsilon$;
--   3. a randomized $B$-bit retained-state protocol **achieves** average protection if, for every fixed history and every promised query, its response is successful with probability at least $1-\beta$ over its coins; a deterministic code achieves it if the response is always successful.
--
--   These are the contracts of $B_{\mathrm{average}}$ in Theorem 7; individual protection (every $f_i(H)\le\epsilon$ separately) is the published contract `PreservePast.RandAchieves` applied to a $K$-tuple.
--
--   **Formalization Note** The protocol model is the one of the published mission: one coin space, an encoder that sees the history and the coins and writes one of $2^B$ messages before the query, and a decoder that sees the message, the coins and the query.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §3.3, p.9 (PDF p.11); Appendix G, p.44 (PDF p.46), eq. (138)

import Mathlib
import Definitions.Def_PreservePast_IsPromised
import Definitions.Def_PreservePast_IsSuccess

open MeasureTheory Matrix

namespace PreservePast.Supplement

/-- The **average loss increment** `K⁻¹ Σ_i f_i(H)` of an update on a `K`-tuple of tasks.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.3, p.9 (PDF p.11) and Appendix G, p.44 (PDF p.46): "The uniform task mixture obeys the
same energy bounds and has increment K⁻¹ Σ_i f_i". Used for `K ≥ 1`. -/
noncomputable def avgLossInc {m n K : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} (h : Fin K → Task W₀)
    (H : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ((K : ℝ))⁻¹ * ∑ i, (h i).lossInc H

/-- The **promise under average protection**: unit `x`, `p` and an exactly fitting update of rank
`≤ r`, Frobenius norm `≤ R`, with nonpositive *average* increment. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.3, p.9 (PDF p.11): "we
compare individual and average protection under the same rank, radius, and new-task fit
constraints. Let the promise be an exactly fitting update with nonpositive increment in the loss
being protected". Under individual protection the loss being protected is each `f_i` (the
published `PreservePast.IsPromised`); here it is the average. -/
def IsPromisedAvg {m n K : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} (r : ℕ) (R : ℝ)
    (h : Fin K → Task W₀) (x : Fin n → ℝ) (p : Fin m → ℝ) : Prop :=
  ∑ i, x i ^ 2 = 1 ∧ ∑ j, p j ^ 2 = 1 ∧
    ∃ Hs : Matrix (Fin m) (Fin n) ℝ, Hs.rank ≤ r ∧ LowRankMEG.frobNorm Hs ≤ R ∧ Hs *ᵥ x = p ∧
      avgLossInc h Hs ≤ 0

/-- **Success under average protection**: rank `≤ r`, `‖H‖_F ≤ R`, new-task error
`½‖Hx − p‖² ≤ ξ`, and average old increment `≤ ε` (§3.3, p.9: "allow new-task error
‖Hx − p‖²/2 ≤ ξ"). -/
def IsSuccessAvg {m n K : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} (r : ℕ) (R ξ ε : ℝ)
    (h : Fin K → Task W₀) (x : Fin n → ℝ) (p : Fin m → ℝ) (H : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  H.rank ≤ r ∧ LowRankMEG.frobNorm H ≤ R ∧ (1 / 2) * ∑ j, (H *ᵥ x - p) j ^ 2 ≤ ξ ∧
    avgLossInc h H ≤ ε

/-- **A randomized B-bit retained-state protocol achieving average protection** (the contract of
`B_average` in Theorem 7). P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.3, p.9 (PDF p.11), with the retained-state convention of §1.2,
p.2 (PDF p.4).

**Formalization Note.** Identical to the published `PreservePast.RandAchieves` (one coin space
`Ω`, encoder `history → Ω → Fin (2^B)` before the query, decoder `Fin (2^B) → Ω → query → update`,
success with probability `≥ 1 − β` for every fixed history and every promised query), with the
promise and the success contract of average protection. -/
def RandAchievesAvg {m n K B : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (enc : (Fin K → Task W₀) → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (r : ℕ) (ε ξ R β : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ h, Measurable (enc h)) ∧
    (∀ M x p, Measurable (fun ω => Matrix.of.symm (dec M ω x p))) ∧
    ∀ h x p, IsPromisedAvg r R h x p →
      ENNReal.ofReal (1 - β) ≤ P {ω | IsSuccessAvg r R ξ ε h x p (dec (enc h ω) ω x p)}

/-- **A deterministic B-bit code achieving average protection with certainty** (Theorem 7, p.9:
"The upper bounds are deterministic"). The analogue of the published `PreservePast.DetAchieves`. -/
def DetAchievesAvg {m n K B : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ}
    (enc : (Fin K → Task W₀) → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (r : ℕ) (ε ξ R : ℝ) : Prop :=
  ∀ h x p, IsPromisedAvg r R h x p → IsSuccessAvg r R ξ ε h x p (dec (enc h) x p)

end PreservePast.Supplement


