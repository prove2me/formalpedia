-- Prove2me | Definitions.Def_SuperlatSVP_Supplement_Admissible
-- name    : SuperlatSVP_Supplement_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:36:21.562823+00:00
-- url     : https://prove2.me/theorems/62e066cf-3432-42d6-8fd4-e6946b5a93a8
-- title:
--   Randomized adaptive restriction procedures on $\mathbb Z^n$, their success probability, and expected numbers of samples and calls
-- statement:
--   This definition models the procedures of Theorem 3.6. They try to obtain a point of $\mathbb Z^n$ by drawing discrete Gaussian samples from superlattices of $\mathbb Z^n$ and keeping one that lands in $\mathbb Z^n$.
--
--   At each step, the procedure looks at its history: every superlattice it has chosen and every sample it has received. It then either **stops**, outputting one point or nothing, or makes a **call**. A call chooses a superlattice $\Lambda\supseteq\mathbb Z^n$ and a number $k$, and returns $k$ fresh samples from $D_{\Lambda,r}$, independent of everything before. The procedure may be randomized: it is given by the probability of each next action as a function of the history. The number of calls is unbounded.
--
--   For a width $r$ and history $h$, the probability of reaching $h$ is the product over its calls of the probability of making that call and the probabilities of the samples received. From it we define:
--
--   1. the **success probability**: the probability that the procedure stops and outputs a sample it has received that lies in $\mathbb Z^n$;
--   2. $\mathbb E[M]$, the expected total number of samples received;
--   3. the expected number of calls.
--
--   Both expectations take values in $[0,\infty]$.
--
--   A procedure is **admissible** for $t$ and $N$ when its action probabilities at each history sum to at most $1$ (the rest is an abort), and every call it makes with positive probability names a superlattice $\Lambda\supseteq\mathbb Z^n$ with $\eta_{1/2}(\Lambda)\le t$ and asks for at most $N$ samples. Here
--   $$\eta_\varepsilon(\Lambda)=\inf\{s>0:\rho_{1/s}(\Lambda^*\setminus\{0\})\le\varepsilon\}$$
--   is the smoothing parameter.
--
--   **Formalization Note** A superlattice is given by an invertible rational basis $C$. Every superlattice of $\mathbb Z^n$ has one, and all its points are rational, so samples are rational vectors. A history is listed newest call first. Randomness that persists across steps is captured by the behavioural form, because the history contains everything the procedure has observed. The smoothing parameter is the published `RegevLWE.GaussConv.smoothingParam`.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Theorem 3.6, p.28 (PDF p.28); (2.6), p.16; §2.2, p.16

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice

open scoped ENNReal

namespace SuperlatSVP.Supplement

/-- A rational vector `v ∈ ℚⁿ` as a point of `ℝⁿ`. -/
noncomputable def ratPoint {n : ℕ} (v : Fin n → ℚ) : E n := vecE (fun i => (v i : ℝ))

/-- The lattice `L(C) = Cℤⁿ` of a rational matrix `C`. -/
noncomputable def latQ {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) : Submodule ℤ (E n) :=
  lat (C.map (fun q : ℚ => (q : ℝ)))

/-- One action of a restriction procedure: stop with an output (`none` = no output), or make a
call that requests `k` fresh samples from the discrete Gaussian on the superlattice `L(C)`. -/
inductive RAct (n : ℕ) where
  | stop (o : Option (Fin n → ℚ))
  | call (C : Matrix (Fin n) (Fin n) ℚ) (k : ℕ)

/-- A history, **newest call first**: for each call made, the basis `C` of the superlattice chosen
and the list of samples received. -/
abbrev RHist (n : ℕ) := List (Matrix (Fin n) (Fin n) ℚ × List (Fin n → ℚ))

/-- A (behavioural) randomized adaptive procedure: given the history, the probability of each next
action. -/
abbrev RStrategy (n : ℕ) := RHist n → RAct n → ℝ≥0∞

/-- The discrete Gaussian `D_{L(C),r}` (§2.2, p.16) as a mass function on rational points:
`ρ_r(v)/ρ_r(L(C))` for `v ∈ L(C)`, `0` otherwise. -/
noncomputable def dgMass {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (r : ℝ) (v : Fin n → ℚ) : ℝ≥0∞ :=
  ({v | ratPoint v ∈ latQ C} : Set (Fin n → ℚ)).indicator
    (fun v => ENNReal.ofReal (RegevLWE.GaussConv.rho r (ratPoint v)) /
      rhoSet r (latQ C : Set (E n))) v

/-- The probability that the procedure `σ`, served samples of width `r`, produces the history `h`:
the product over its calls of the probability of the call given the earlier history and of the
probabilities of the samples received. -/
noncomputable def histWeight {n : ℕ} (σ : RStrategy n) (r : ℝ) : RHist n → ℝ≥0∞
  | [] => 1
  | (C, xs) :: h => histWeight σ r h * σ h (RAct.call C xs.length) * (xs.map (dgMass C r)).prod

/-- All samples received in the history `h`. -/
def received {n : ℕ} (h : RHist n) : List (Fin n → ℚ) := h.flatMap Prod.snd

/-- The success probability: the procedure stops and outputs a **received** sample lying in
`ℤⁿ = L(I)`. -/
noncomputable def successProb {n : ℕ} (σ : RStrategy n) (r : ℝ) : ℝ≥0∞ :=
  ∑' h : RHist n, histWeight σ r h *
    ∑' v : Fin n → ℚ,
      ({v | v ∈ received h ∧ ratPoint v ∈ lat (1 : Matrix (Fin n) (Fin n) ℝ)} :
        Set (Fin n → ℚ)).indicator (fun v => σ h (RAct.stop (some v))) v

/-- The expected total number `E[M]` of received samples (in `[0, ∞]`). -/
noncomputable def expSamples {n : ℕ} (σ : RStrategy n) (r : ℝ) : ℝ≥0∞ :=
  ∑' h : RHist n, histWeight σ r h *
    ∑' a : Matrix (Fin n) (Fin n) ℚ × ℕ, σ h (RAct.call a.1 a.2) * (a.2 : ℝ≥0∞)

/-- The expected number of calls (in `[0, ∞]`). -/
noncomputable def expCalls {n : ℕ} (σ : RStrategy n) (r : ℝ) : ℝ≥0∞ :=
  ∑' h : RHist n, histWeight σ r h *
    ∑' a : Matrix (Fin n) (Fin n) ℚ × ℕ, σ h (RAct.call a.1 a.2)

/-- The admissible restriction procedures of Theorem 3.6. Hhan, Kim, Kim, Laarhoven, *Superlattice
methods for the shortest vector problem and discrete Gaussian sampling*, STOC 2027 submission
(manuscript sha256 fcf5b14f…ba), Theorem 3.6, p.28 (PDF p.28): "Consider a procedure that adaptively
chooses superlattices Λi ⊇ L with η1/2(Λi) ≤ t, receives at most N fresh independent samples from
DΛi,χt per call, and outputs only a received sample in L." Here `L = ℤⁿ`.

1. at every history the action probabilities sum to at most `1` (the missing mass is an abort
   without output);
2. every call made with positive probability names an invertible rational `C` whose lattice
   `Λ = L(C)` contains `ℤⁿ` and has `η_{1/2}(Λ) ≤ t`, and asks for `k ≤ N` samples.

**Formalization Note.** A randomized adaptive procedure is given by its behavioural strategy
`σ`: the law of its next action given everything it has seen (its earlier choices and all received
samples); internal randomness that persists across steps adds nothing, since the history records
everything it has observed. The number of calls is unbounded and the procedure may run forever.
Every superlattice of `ℤⁿ` has a rational basis, so `Λ = L(C)` with `C ∈ ℚ^{n×n}` covers all of
them, and its points are rational. `η_{1/2}` is the published `RegevLWE.GaussConv.smoothingParam`
(`inf {s > 0 : ρ_{1/s}(Λ* ∖ {0}) ≤ 1/2}`, (2.6) p.16). Samples are drawn with `dgMass`
(`histWeight`), success is `successProb`, and `E[M]`, `E[#calls]` are `expSamples`, `expCalls`. -/
def Admissible {n : ℕ} (σ : RStrategy n) (t : ℝ) (N : ℕ) : Prop :=
  (∀ h : RHist n, ∑' a : RAct n, σ h a ≤ 1) ∧
    ∀ (h : RHist n) (C : Matrix (Fin n) (Fin n) ℚ) (k : ℕ), σ h (RAct.call C k) ≠ 0 →
      C.det ≠ 0 ∧ lat (1 : Matrix (Fin n) (Fin n) ℝ) ≤ latQ C ∧
        RegevLWE.GaussConv.smoothingParam (latQ C) (1 / 2) ≤ t ∧ k ≤ N

end SuperlatSVP.Supplement


