-- Prove2me | Definitions.Def_SublinearSteiner_Retention
-- name    : SublinearSteiner_Retention
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:40:51.497192+00:00
-- url     : https://prove2.me/theorems/ad07bf8f-c309-4d90-83d9-b99d9cf556f5
-- title:
--   The retention law of terminal covers and the on-demand draws
-- statement:
--   At scale $a$ put $\rho=\delta a$, $h=\lceil\log(k+2)\rceil$, $r_c=\rho/h$ and $\psi=\lceil e\log(4kI/\beta)\rceil$. For a terminal $x$, $d_x$ is the number of other terminals within $r_c$ of $x$, and $x$ is retained independently with probability
--   $$q_x=1-\Bigl(\frac{d_x}{d_x+1}\Bigr)^{\psi};$$
--   one fixed terminal is always retained. $N_i$ is the retained set at scale $i$. Also $H_c=2+2\psi+\log(2I/\beta)$.
--
--   The bit of $x$ is resolved on demand: draw uniform terminals, retaining $x$ if $x$ is drawn before $\psi$ other terminals within $r_c$, and rejecting it otherwise. Each pair of a terminal and a scale has private randomness.
--
--   **Formalization Note.** The product law of the bits is an explicit finite weighted sum. The on-demand process runs on private streams of a finite length $H$, uniform over the function space. An adaptive procedure is a strategy that sees the completed resolutions with their draws, and picks the next unresolved pair or stops. It never sees the draws of an unfinished resolution. $W$ (`draws`) is the total number of draws and $A$ (`found`) the number of completed resolutions whose target was drawn.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 4.3, pp.22–23

import Mathlib
import Definitions.Def_SublinearSteiner_Constants
import Definitions.Def_SublinearSteiner_FinMetric

open scoped Classical

namespace SublinearSteiner

/-!
# Independent terminal covers: the retention law and the on-demand draws

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 4.3, pp.22–23.

At scale `a` put `ρ = δa`, `h = ⌈log(k + 2)⌉`, `r_c = ρ/h`, `ψ = ⌈e log(4kI/β)⌉`. Every terminal `x` is retained
independently with probability `q_x = 1 − (d_x/(d_x + 1))^ψ`, where `d_x` is the number of other terminals within
`r_c`; one fixed terminal is always retained. The bit of `x` is resolved on demand: draw uniform terminals, retaining
`x` if `x` itself is drawn before `ψ` other terminals within `r_c`, and rejecting it otherwise. The draws for different
pairs of a terminal and a scale use private independent randomness.

**Formalization Note.**
* `log` is the natural logarithm. The arguments are positive whenever `k, I ≥ 1` and `0 < β`.
* The product law of the bits is a finite weighted sum over `Bits T I`. This describes (4.6). The bit of the fixed
  terminal is present in the law and has no effect.
* The private streams are finite: `DrawStream T I H` gives each (terminal, scale) pair `H` draws, uniformly over the
  finite function space. The event "at some time" of (4.7), for infinite streams, is the increasing limit of its finite
  horizon versions, so bounding every horizon is equivalent. A pair whose stream runs out stops the procedure.
* An adaptive procedure is a strategy `σ` that sees exactly the completed resolutions, with their draws, and picks the
  next unresolved pair or stops. It sees neither the active pair's draws nor the unread draws. Its draw count is a function of what it sees.
  A randomized procedure is a mixture of strategies. Choosing a pair that is already resolved stops the procedure
  (the page caches resolved bits).
-/

variable {n : ℕ}

/-- `h = ⌈log(k + 2)⌉` (p.22). -/
noncomputable def hopBound (k : ℕ) : ℕ := ⌈Real.log ((k : ℝ) + 2)⌉₊

/-- `ψ = ⌈e log(4kI/β)⌉` (p.22). -/
noncomputable def psiBound (k I : ℕ) (β : ℝ) : ℕ := ⌈Real.exp 1 * Real.log (4 * k * I / β)⌉₊

/-- `H_c = 2 + 2ψ + log(2I/β)` (4.6). -/
noncomputable def coverHc (ψ I : ℕ) (β : ℝ) : ℝ := 2 + 2 * ψ + Real.log (2 * I / β)

/-- `d_x`: the number of other terminals within distance `r` of `x` (p.22). -/
noncomputable def nearCount (w : FinMetric n) (T : Finset (Fin n)) (r : ℝ) (x : Fin n) : ℕ :=
  ((T.erase x).filter fun y => w.d x y ≤ r).card

/-- `q_x = 1 − (d_x/(d_x + 1))^ψ` (p.22). -/
noncomputable def retentionProb (w : FinMetric n) (T : Finset (Fin n)) (r : ℝ) (ψ : ℕ) (x : Fin n) : ℝ :=
  1 - ((nearCount w T r x : ℝ) / ((nearCount w T r x : ℝ) + 1)) ^ ψ

/-- A retention bit for each pair of a terminal and a scale. -/
abbrev Bits (T : Finset (Fin n)) (I : ℕ) := (↥T × Fin I) → Bool

/-- The probability of a bit vector under independent retention with probabilities `q`. -/
noncomputable def bitsWeight {T : Finset (Fin n)} {I : ℕ} (q : ↥T × Fin I → ℝ) (ω : Bits T I) : ℝ :=
  ∏ p, if ω p then q p else 1 - q p

/-- `q` at the scales `a`: the probability of retaining the terminal at scale `i`, with `r_c = δ a_i / h`. -/
noncomputable def scaleRetention (w : FinMetric n) (T : Finset (Fin n)) {I : ℕ} (a : Fin I → ℝ) (ψ h : ℕ)
    (p : ↥T × Fin I) : ℝ :=
  retentionProb w T (delta * a p.2 / h) ψ p.1

/-- `N_i`: the retained set at scale `i`, always containing the fixed terminal `x₀`. -/
noncomputable def retainedSet {T : Finset (Fin n)} {I : ℕ} (x₀ : Fin n) (ω : Bits T I) (i : Fin I) :
    Finset (Fin n) :=
  insert x₀ (T.filter fun x => ∃ hx : x ∈ T, ω (⟨x, hx⟩, i) = true)

/-- A (terminal, scale) pair. -/
abbrev DrawPair (T : Finset (Fin n)) (I : ℕ) := ↥T × Fin I

/-- Private draw streams of length `H`: `ω p j` is the `j`-th uniform terminal drawn for the pair `p`. -/
abbrev DrawStream (T : Finset (Fin n)) (I H : ℕ) := DrawPair T I → Fin H → ↥T

/-- The state of an adaptive procedure: its completed resolutions, each with its draws, and the active resolution with
the draws so far. -/
structure DrawState (T : Finset (Fin n)) (I : ℕ) where
  /-- The completed resolutions. -/
  completed : List (DrawPair T I × List ↥T)
  /-- The active resolution, if any. -/
  active : Option (DrawPair T I × List ↥T)

/-- The state at the start. -/
def DrawState.init (T : Finset (Fin n)) (I : ℕ) : DrawState T I := ⟨[], none⟩

/-- A strategy: from the completed resolutions, the next pair, or stop. -/
abbrev DrawStrategy (T : Finset (Fin n)) (I : ℕ) := List (DrawPair T I × List ↥T) → Option (DrawPair T I)

/-- The number of drawn terminals other than the target within distance `r` of the target. -/
noncomputable def nearDraws (w : FinMetric n) {T : Finset (Fin n)} (x : ↥T) (r : ℝ) (ds : List ↥T) : ℕ :=
  (ds.filter fun z => z ≠ x ∧ w.d x.1 z.1 ≤ r).length

/-- A resolution is complete once the target is drawn, or `ψ` other terminals within `r` have been drawn. -/
def DrawsResolved (w : FinMetric n) {T : Finset (Fin n)} (x : ↥T) (r : ℝ) (ψ : ℕ) (ds : List ↥T) : Prop :=
  x ∈ ds ∨ ψ ≤ nearDraws w x r ds

/-- One draw of the procedure. It stutters when the strategy stops or a stream runs out. -/
noncomputable def drawStep (w : FinMetric n) {T : Finset (Fin n)} {I H : ℕ} (r : Fin I → ℝ) (ψ : ℕ)
    (σ : DrawStrategy T I) (ω : DrawStream T I H) (s : DrawState T I) : DrawState T I :=
  let tgt : Option (DrawPair T I × List ↥T) :=
    match s.active with
    | some a => some a
    | none =>
        match σ s.completed with
        | none => none
        | some p => if p ∈ s.completed.map Prod.fst then none else some (p, [])
  match tgt with
  | none => s
  | some (p, ds) =>
      if h : ds.length < H then
        let ds' := ds ++ [ω p ⟨ds.length, h⟩]
        if DrawsResolved w p.1 (r p.2) ψ ds' then ⟨s.completed ++ [(p, ds')], none⟩
        else ⟨s.completed, some (p, ds')⟩
      else s

/-- The state after `t` steps. -/
noncomputable def drawRun (w : FinMetric n) {T : Finset (Fin n)} {I H : ℕ} (r : Fin I → ℝ) (ψ : ℕ)
    (σ : DrawStrategy T I) (ω : DrawStream T I H) (t : ℕ) : DrawState T I :=
  (drawStep w r ψ σ ω)^[t] (DrawState.init T I)

/-- `W`: the total number of draws. -/
def DrawState.draws {T : Finset (Fin n)} {I : ℕ} (s : DrawState T I) : ℕ :=
  (s.completed.map fun c => c.2.length).sum + (s.active.elim 0 fun a => a.2.length)

/-- `A`: the number of retained terminals found, that is, completed resolutions whose target was drawn. -/
noncomputable def DrawState.found {T : Finset (Fin n)} {I : ℕ} (s : DrawState T I) : ℕ :=
  (s.completed.filter fun c => c.1.1 ∈ c.2).length

end SublinearSteiner


