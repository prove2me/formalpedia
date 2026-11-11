-- Prove2me | Definitions.Def_CubicPermFPRAS_sampler
-- name    : CubicPermFPRAS_sampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:57:35.029279+00:00
-- url     : https://prove2.me/theorems/12f31198-83b3-4049-b879-1a6acc9e3c25
-- title:
--   The stage simulation of the assignment Glauber dynamics and the perfect-matching sampler
-- statement:
--   **Stage simulation** (proof of Proposition 15 and of Lemma 49): from $\sigma_0$ at time $0$, repeatedly draw an exponential clock of rate $W(\sigma)=\sum_u\theta_u(\sigma)$; if it rings after time $T$, output the current configuration; otherwise count the ring, output $\sigma^*$ if this is ring number $R+1$, and otherwise choose $u$ with probability $\theta_u(\sigma)/W(\sigma)$ and resample $\sigma_u\sim q_u$. The simulation also reports the number of rings observed.
--
--   **Sampler** (proof of Lemma 49): with constants $(J_\alpha,K,C_\alpha)$, $J=J_\alpha n^2$, the activity schedule $a_0<\dots<a_m=J$, $\delta=\eta/(8(m+1))$, $T=\log(2/\delta)$, $R_k=\lceil C_\alpha n(1+\sqrt{a_k})(T+\log(2n))^2\rceil$ and $b=\lceil\log(2/\eta)/\log(3/2)\rceil$: run the stages $k=0,\dots,m$ in turn from $\sigma^*$, repeat up to $b$ times, and return the first perfect matching, or the identity matching if all runs fail. The full sampler first builds the activity schedule and $B$.
--
--   Charges: $n+1$ per stage initialization, $4$ per clock draw, $\lceil\log_2(2n)\rceil+3$ per resampling (segment trees, Claim 48), $n+1$ per perfect-matching test, $m+6$ per sampler call, $n^2+1$ for building $B$, and (tests $+m+2$) for the activity schedule.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), proof of Proposition 15, p.50 (PDF 52); proof of Lemma 49, pp.53–54 (PDF 55–56); Lemma 10, p.13 (PDF 15)

import Mathlib
import Definitions.Def_CubicPermFPRAS_nuAux
import Definitions.Def_CubicPermFPRAS_activitySchedule
import Definitions.Def_CubicPermFPRAS_Prog

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

variable {n : ℕ}

/-- Index `0` of `Fin (n+1)` stands for `∗` (unassigned), index `j+1` for the right vertex `j`. -/
def optOfFin : Fin (n + 1) → Option (Fin n) := Fin.cases none some

/-- The resampling law `q_u` (p.14) indexed by `Fin (n+1)`. -/
def qIdx (B : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (u : Fin n) : Fin (n + 1) → ℝ :=
  fun i => qRes B a u (optOfFin i)

/-- One resampling event of the assignment Glauber dynamics (Remark 12, p.14; proof of
Proposition 15, p.50 (PDF 52); arXiv:2609.20717, held version sha256 9e14f335…): choose `u` with
probability `θ_u(σ)/W(σ)` from the uniform `U₁`, then draw the new value of `σ_u` from `q_u`
using the uniform `U₂`. -/
def glauberMove (B : Matrix (Fin n) (Fin n) ℝ) (J a : ℝ) (σ : Asg n) (U₁ U₂ : ℝ) : Asg n :=
  match pickIdx (fun u => theta J σ u) U₁ with
  | none => σ
  | some u =>
    match pickIdx (qIdx B a u) U₂ with
    | none => σ
    | some i => Function.update σ u (optOfFin i)

/-- The charge `⌈log₂(2n)⌉ + 1` for one segment-tree operation round (Claim 48, p.50): sampling
`u` from the tree `T_θ`, sampling `v` from the row tree `T_u`, and the `O(1)` tree updates. -/
def treeCharge (n : ℕ) : ℕ := Nat.clog 2 (2 * n) + 1

/-- **Stage simulation** of the assignment Glauber dynamics at activity `a` up to time `T`
with at most `R` resamplings (proof of Proposition 15, p.50; proof of Lemma 49, p.53 (PDF 55)).

Starting at `σ₀` and time `t = 0`: draw an exponential clock of rate `W(σ) = ∑_u θ_u(σ)`
as `τ = −log(U)/W(σ)` (`U = 0` means no ring); if `t + τ > T`, return the current
configuration; otherwise advance `t`, count the ring, and if this is ring number `R + 1`
("if another resampling would exceed this limit, use `σ*` as the stage output", p.53)
return `σ*`; otherwise perform one resampling event. The second component of the value is the
number of rings observed, `min(Q_T, R + 1)`.

Charges: `n + 1` for initializing the tree `T_θ` (p.50); per clock draw `1` (the uniform) plus
`3` (logarithm, division, comparison); per resampling `⌈log₂(2n)⌉ + 1` plus the two uniforms. -/
def stage (B : Matrix (Fin n) (Fin n) ℝ) (J a T : ℝ) (R : ℕ) (σ₀ : Asg n) :
    Prog (Asg n × ℕ) := do
  tick (n + 1)
  let mut σ := σ₀
  let mut t : ℝ := 0
  for j in List.range (R + 1) do
    let U ← unif
    tick 3
    let W : ℝ := ∑ u, theta J σ u
    if U ≤ 0 ∨ T < t - Real.log U / W then
      return (σ, j)
    t := t - Real.log U / W
    if j = R then
      return (sigmaStar n, R + 1)
    tick (treeCharge n)
    let U₁ ← unif
    let U₂ ← unif
    σ := glauberMove B J a σ U₁ U₂
  return (sigmaStar n, R + 1)

/-- The sampler's constants, the paper's "sufficiently large" constants for a fixed roughness
`α` (§5.1, p.12; proof of Lemma 10, p.43; Proposition 16 / proof of Lemma 49, p.53):
`J_α` (so that `J = J_α n²`), the constant `K` of the activity schedule, and the constant `C_α`
of the resampling limits `R_k`. -/
structure SamplerParams where
  Jα : ℝ
  K : ℝ
  Cα : ℝ

/-- `J = J_α n²` (p.12). -/
def SamplerParams.J (prm : SamplerParams) (n : ℕ) : ℝ := prm.Jα * (n : ℝ) ^ 2

/-- One run through all stages of the activity schedule, starting at `σ*` (proof of Lemma 49,
p.53–54). Each entry of `stages` is an activity `a_k` with its resampling limit `R_k`. -/
def samplerRun (B : Matrix (Fin n) (Fin n) ℝ) (J T : ℝ) (stages : List (ℝ × ℕ)) :
    Prog (Asg n) :=
  stages.foldlM (fun σ p => do
    let r ← stage B J p.1 T p.2 σ
    pure r.1) (sigmaStar n)

/-- **The perfect-matching sampler after preprocessing** (proof of Lemma 49, p.53–54), for a
precomputed rescaled matrix `B` and error tolerance `η`: with `m` the index of the last
activity, `δ = η/(8(m+1))`, `T = log(2/δ)`, `R_k = ⌈C_α n(1 + √a_k)(T + log(2n))²⌉`,
`b = ⌈log(2/η)/log(3/2)⌉`; make up to `b` independent runs through all stages and return the
first final configuration that is a perfect matching, or the fixed perfect matching (the
identity) if all runs fail. Charges: `m + 6` for computing `δ, T, b` and the limits; `n + 1` for
testing whether a run's output is a perfect matching. -/
def samplerCore (prm : SamplerParams) (B : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) : Prog (Asg n) := do
  let J := prm.J n
  let m := actLen prm.K J n
  let δ : ℝ := η / (8 * ((m : ℝ) + 1))
  let T : ℝ := Real.log (2 / δ)
  let stages : List (ℝ × ℕ) := (List.range (m + 1)).map fun k =>
    let a := actSeq prm.K J n k
    (a, ⌈prm.Cα * n * (1 + Real.sqrt a) * (T + Real.log (2 * n)) ^ 2⌉₊)
  let b : ℕ := ⌈Real.log (2 / η) / Real.log (3 / 2)⌉₊
  tick (m + 6)
  for _ in List.range b do
    let σ ← samplerRun B J T stages
    tick (n + 1)
    if IsPerfect σ then return σ
  return idMatching n

/-- Build the rescaled matrix `B` of Eq. (10) together with its column sums, the values
`W(u,v)` and the row/column sampling trees: charge `n² + 1` ("computed in `O(n²)` time",
p.16; preprocessing, p.50). -/
def buildB (lam : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : Prog (Matrix (Fin n) (Fin n) ℝ) := do
  tick (n ^ 2 + 1)
  return Bmat lam w

/-- Construct the activity schedule (proof of Lemma 10, step 4, p.44–45): charge the number of
inequality tests, plus `m + 1` for writing the activities, plus `1`. -/
def buildSchedule (prm : SamplerParams) (n : ℕ) : Prog Unit :=
  tick (actTests prm.K (prm.J n) n + actLen prm.K (prm.J n) n + 2)

/-- **The sampler of Lemma 49** (and of Lemma 8 with `η = 1/16`), p.53 (PDF 55), including its
preprocessing: build the activity schedule and `B` from the activities `λ` and the anchor
weights `w(r,·)`, then run `samplerCore`. -/
def sampler (prm : SamplerParams) (lam : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) (η : ℝ) :
    Prog (Asg n) := do
  buildSchedule prm n
  let B ← buildB lam w
  samplerCore prm B η

end

end CubicPermFPRAS


