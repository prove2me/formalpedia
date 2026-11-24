-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Supplement_Process
-- name    : ReusableAssort_Hybrid_Supplement_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:15:22.832866+00:00
-- url     : https://prove2.me/theorems/8e5e0410-a009-418b-a758-b851577e864a
-- title:
--   Four-step template with a history-dependent discarding rule, and the state J (pp. 11, 20)
-- statement:
--   The online process of the paper's four-step template (p. 11), with a discarding rule that may depend on the history. At each time $t = t_0, \dots, T$: the type $z_t \sim F_t$ is revealed; $\hat S_t \sim \{y_{S,t,z_t}\}_{S \in \mathcal S}$ is sampled; each $i \in \hat S_t$ is kept independently with probability $a_t(i)$, giving $\bar S_t$; the offered set $\tilde S_t$ is drawn by Sub-assortment Sampling (Procedure 1) on $(\phi^{z_t}, \bar S_t, \{\phi^{z_t}(\hat S_t, i)\})$; the consumer rents $i \in \tilde S_t$ with probability $\phi^{z_t}(\tilde S_t, i)$ and keeps it for a duration $d \sim g^{z_t}_i$. The keep probability $a_t(i)$ may depend on the realized history before time $t$ and on $z_t$.
--
--   1. **Path law and revenue.** The probability of a sample path is the product of these one-step kernels, and the expected revenue is the sum over products and times of the fee $r^{z_t}_i$ of each rental.
--   2. **State.** The state $J$ at time $t$ records, for every product $i$ and every later time $s > t$, the number of units of $i$ that are out and come back at time $s$ (a unit rented at time $\tau$ with duration $d$ comes back at $\tau + d$). Together with $c_i$ it gives the number of units on hand.
--
--   With a fixed rule per product this is exactly the base mission's process; Sim+Hybrid(ii) and Algorithm 4 need the history-dependent form.
--
--   **Formalization Note** Step $k$ of a path is time $t_0 + k$; a start state lists the outstanding returns, as in the base `Process`. A product with no unit on hand is removed by the rule itself (each algorithm sets its keep probability to $0$).
--
--   The generic kernel is an algebraic weight for an arbitrary function of the full path. It is a probability kernel only for causal keep rules valued in $[0,1]$. Both algorithms in this supplement use such rules; their value at step $k$ reads only earlier choices and durations and the current type. No probability-law claim is made for other inputs.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 11 (four-step template); p. 20 (state J in the proof sketch of Theorem 4)

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Algorithms

namespace ReusableAssort.Hybrid.Supplement

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

/-- Algebraic step weight for the online process of the four-step template (p. 11) with a history-dependent discarding
rule. It is the base `kernel` with the keep probability of product `i` at step `k` (time
`t₀ + k`) given by `a k v i`, an arbitrary function of the path `v`; the algorithms below only
read the steps `j < k` and the current type `(v k).1`. A probability-kernel interpretation requires
a causal rule valued in `[0,1]` (as for both algorithms below). Type `z ∼ F_t`; `Ŝ ∼ y_{·,t,z}` over `𝒮`;
each `i ∈ Ŝ` kept independently with probability `a k v i`; `S̃ ∼` Procedure 1 on
`(ϕ^z, S̄, {ϕ^z(Ŝ, i)})`; the consumer picks `i ∈ S̃` w.p. `ϕ^z(S̃, i)`; the duration is drawn
from `g^z_i`. -/
noncomputable def kernelA (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (t₀ : ℕ) (a : Fin (T + 1 - t₀) → (Fin (T + 1 - t₀) → Step n T Z) → Fin n → ℝ)
    (v : Fin (T + 1 - t₀) → Step n T Z) (k : Fin (T + 1 - t₀)) : ℝ :=
  let t := t₀ + k.1
  let z := (v k).1
  let Shat := (v k).2.1
  let Sbar := (v k).2.2.1
  let Stil := (v k).2.2.2.1
  let ch := (v k).2.2.2.2.1
  let d := (v k).2.2.2.2.2
  I.F t z * y t z Shat * (if Shat ∈ I.feas then 1 else 0)
    * ((if Sbar ⊆ Shat then 1 else 0) * (∏ i ∈ Sbar, a k v i) * ∏ i ∈ Shat \ Sbar, (1 - a k v i))
    * subAssort (I.phi z) Sbar (fun i => I.phi z Shat i) Stil
    * (match ch with
        | some i => if i ∈ Stil then I.phi z Stil i else 0
        | none => 1 - ∑ i ∈ Stil, I.phi z Stil i)
    * (match ch with
        | some i => I.g z i (d : ℕ)
        | none => if (d : ℕ) = 0 then 1 else 0)

/-- Product of step weights along `v` (times `t₀, …, T`); a path probability for a causal
keep rule `a` valued in `[0,1]` and valid normalized model inputs. -/
noncomputable def pathProbA (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (t₀ : ℕ) (a : Fin (T + 1 - t₀) → (Fin (T + 1 - t₀) → Step n T Z) → Fin n → ℝ)
    (v : Fin (T + 1 - t₀) → Step n T Z) : ℝ :=
  ∏ k, kernelA I y t₀ a v k

/-- Total expected revenue over times `t₀, …, T` under the keep rule `a`. -/
noncomputable def expRevA (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (t₀ : ℕ) (a : Fin (T + 1 - t₀) → (Fin (T + 1 - t₀) → Step n T Z) → Fin n → ℝ) : ℝ :=
  ∑ v, pathProbA I y t₀ a v *
    ∑ i, ∑ k ∈ Finset.range (T + 1 - t₀), revAt I t₀ i k v

/-- The state `J` at the beginning of step `k` (time `t = t₀ + k`) of a run started at `t₀` with
outstanding returns `ret`: `retState … i s` is the number of units of product `i` that are out at
time `t` and come back at time `s > t` — those of `ret`, plus those rented at earlier steps
`j < k` (a unit rented at step `j` with duration `d` comes back at time `t₀ + j + d`). Together
with `c_i` it gives the on-hand units, so it is the state "number of available units of each
product, and the return time of each allocated unit" of the proof of Theorem 4 (p. 20). -/
def retState (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t₀) → Step n T Z)
    (k : ℕ) : Fin n → ℕ → ℕ :=
  fun i s =>
    if t₀ + k < s then
      ret i s + (Finset.univ.filter (fun j : Fin (T + 1 - t₀) =>
        j.1 < k ∧ (v j).2.2.2.2.1 = some i ∧ t₀ + j.1 + ((v j).2.2.2.2.2 : ℕ) = s)).card
    else 0

end ReusableAssort.Hybrid.Supplement


