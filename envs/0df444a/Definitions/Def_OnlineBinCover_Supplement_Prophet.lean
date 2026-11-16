-- Prove2me | Definitions.Def_OnlineBinCover_Supplement_Prophet
-- name    : OnlineBinCover_Supplement_Prophet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:36:04.195001+00:00
-- url     : https://prove2.me/theorems/8e664a22-c65c-4ccd-bb1a-d1567d76e525
-- title:
--   Randomized programs and the single-sample prophet protocol
-- statement:
--   A **randomized program** is a program of the exact real RAM with rational literals and no real-power instruction; it may flip fair coins, all read from one coin tape $\omega$ shared by the whole run.
--
--   In the **single-sample prophet** model, independent distributions $D_1,\dots,D_n$ on $(0,1]$ and an arrival order $\tau$ are fixed in advance. The algorithm receives one labelled sample $S_i\sim D_i$ per distribution; then item $\tau(t)$ arrives at time $t$ with size $X_{\tau(t)}\sim D_{\tau(t)}$ and must be assigned at once. All samples and sizes are independent. On the real RAM: the initial memory holds $n$ and $S_0,\dots,S_{n-1}$; at time $t$ the size $X_{\tau(t)}$ and the label $\tau(t)$ are written, the program runs $F$ steps, and integer cell $-1$ is the bin. $A_{sp}(X;S)$ counts the bins covered by the online items only; the samples never count.
--
--   $$\mathbb E[A_{sp}(X;S)]\ \text{over}\ S,X\sim\textstyle\prod_i D_i\ \text{and the coin tape},\qquad \mathbb E[\mathrm{OPT}(X)]\ \text{over}\ X\sim\textstyle\prod_i D_i.$$
--
--   **Formalization Note** Distributions are `ProbabilityMeasure ℝ`; expectations are lower Lebesgue integrals of counts bounded by $n$, as real numbers.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §1.1, p.5 (PDF p.6), the single-sample prophet model; Algorithm 1, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_OnlineBinCover_Online

namespace OnlineBinCover.Supplement

/-!
# Randomized programs and the single-sample prophet protocol

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §1.1 p.5 (PDF p.6, "From order-oblivious to
single-sample prophet"), Theorem 1.4, and Algorithm 1 p.14.

The paper: "an adversary specifies independent distributions `D_1, …, D_n` on `(0, 1]` and an
arrival order that is fixed before the values are drawn. Item `i` has size `X_i ∼ D_i` and must be
assigned immediately upon arrival. … the algorithm receives labeled samples `S_i ∼ D_i`, one per
distribution, with all samples and online realizations being mutually independent. The sample set
`S` provides information only; the objective only counts the bins that are covered by the online
items `X`."

**Formalization Note.**
* *Randomized programs.* `RandProgram P`: a program of the published real RAM `PNormReg.Machine`
  with rational literals (`Admissible`) and no `rpow`; the fair `coin` is allowed. One coin tape
  `ω` serves the whole run (the cursor is kept from item to item).
* *Advance information.* Integer cell `0` holds `n`; real cell `i` holds the sample `S_i`
  (labels `0, …, n − 1`); every other cell is `0`.
* *Online feed.* At time `t` item `τ t` arrives: its size `X_{τ t}` goes to real cell `−2` (the
  published `feedLoad`) and its label `τ t` to integer cell `−2`; the run lasts `F` steps; the bin
  label is integer cell `−1` after the run.
* *Objective.* `spValue` is the number of bins covered by the online items `X` under these labels
  (published `covered`); samples never count.
* *Expectations.* Distributions are probability measures on `ℝ` (`ProbabilityMeasure ℝ`).
  `spExp` is `E[A_sp(X; S)]` over `S ∼ ∏ D_i`, `X ∼ ∏ D_i` and the coin tape, independent; `optExp`
  is `E[OPT(X)]` over `X ∼ ∏ D_i`. Both are lower Lebesgue integrals of `ofReal` of a count at most
  `n`, converted to reals (finite); the lower integral never overstates the algorithm's value.
-/

open MeasureTheory

/-- A randomized program: admissible (rational literals, halts only through `halt`), no `rpow`. -/
def RandProgram (P : PNormReg.Program) : Prop :=
  PNormReg.Admissible P ∧ ∀ op ∈ P, ∀ r a e, op ≠ PNormReg.Instr.rpow r a e

/-- `feedLoad` followed by writing the arriving item's label `i` into integer cell `−2`. -/
noncomputable def feedLoadLab (st : PNormReg.State) (x : ℝ) (i : ℤ) : PNormReg.State :=
  { feedLoad st x with integerMemory := Function.update st.integerMemory (-2) i }

/-- The single-sample initial state: integer memory `[n]`, real memory `S_0, …, S_{n−1}`. -/
noncomputable def spInit {n : ℕ} (S : Fin n → ℝ) : PNormReg.State :=
  PNormReg.initState [(n : ℤ)] (List.ofFn S)

/-- The state after the first `t` online arrivals of the order `τ`, on coin tape `ω`. -/
noncomputable def spState (P : PNormReg.Program) (F : ℕ) (ω : ℕ → Bool) {n : ℕ}
    (S X : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) (t : ℕ) : PNormReg.State :=
  ((List.ofFn fun j : Fin n => (X (τ j), ((τ j : ℕ) : ℤ))).take t).foldl
    (fun st y => PNormReg.run P (feedLoadLab st y.1 y.2) ω F) (spInit S)

/-- `A_sp(X; S)` on coin tape `ω` and arrival order `τ`: the bins covered by the online items. -/
noncomputable def spValue (P : PNormReg.Program) (F : ℕ) (ω : ℕ → Bool) {n : ℕ}
    (S X : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : ℕ :=
  covered X (fun i => (spState P F ω S X τ ((τ.symm i : ℕ) + 1)).integerMemory (-1))

/-- The product law `∏ D_i` of independent sizes. -/
noncomputable def piLaw {n : ℕ} (D : Fin n → ProbabilityMeasure ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => (D i : Measure ℝ)

/-- `E[A_sp(X; S)]`, over independent `S ∼ ∏ D_i`, `X ∼ ∏ D_i` and the fair-coin tape. -/
noncomputable def spExp (P : PNormReg.Program) (F : ℕ) {n : ℕ} (D : Fin n → ProbabilityMeasure ℝ)
    (τ : Equiv.Perm (Fin n)) : ℝ :=
  (∫⁻ z, ENNReal.ofReal (spValue P F z.2.2 z.1 z.2.1 τ : ℝ)
    ∂((piLaw D).prod ((piLaw D).prod PNormReg.coinTape))).toReal

/-- `E[OPT(X)]` for `X ∼ ∏ D_i`. -/
noncomputable def optExp {n : ℕ} (D : Fin n → ProbabilityMeasure ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (OPT x : ℝ) ∂(piLaw D)).toReal

end OnlineBinCover.Supplement


