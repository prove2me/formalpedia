-- Prove2me | Definitions.Def_CubicPermFPRAS_permFPRAS
-- name    : CubicPermFPRAS_permFPRAS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:58:56.869306+00:00
-- url     : https://prove2.me/theorems/2a840f48-b045-4890-b7ad-06ebe94cd279
-- title:
--   The algorithm of Theorem 1: FAR learning, the whole-product estimator and the operation cap
-- statement:
--   On an $n\times n$ 0/1 matrix $A$ and $\varepsilon\in(0,1)$, with constants $\mathrm{prm}$:
--
--   1. If $A$ has no perfect matching, output $0$ (charge $n^3+1$).
--   2. Compute the cooling schedule $\lambda_0=1>\dots>\lambda_L$ (charge $n+L+2$) and the activity schedule.
--   3. **Phase 1** ($\delta=1/8$, anchor $r=0$, $w'_0(r,\cdot)=n$): at each $\lambda_i$, $1\le i\le L$, build $B$ from $\lambda_i$ and $w'_{i-1}(r,\cdot)$; run $R=2\lceil c_R\log(2n(L+1)/\delta)\rceil+1$ independent batches, each a sampler call with error $1/16$ followed by FAR transitions up to length $T_F=\lceil c_Tn^2\log(2n)\rceil$, recording the frequencies of $\mathcal N(r,v)$; take coordinatewise medians $\hat p_v$; if some $\hat p_v=0$, output $0$; otherwise update by Eq. (15):
--   $$\tilde w(r,v)=\frac{w(r,v)W(r,v)}{\hat p_v},\qquad w'(r,v)=\tilde w(r,v)\sum_z\frac{\lambda(r,z)}{\tilde w(r,z)}.$$
--   4. **Phase 2** ($N=\lceil128\varepsilon^{-2}\rceil$, $\eta=1/(32(L+1)N)$): draw independent samples $M_{i,t}$ from the sampler at $(\lambda_i,w'_i)$ and output $\hat p=N^{-1}\sum_tX_t$ with
--   $$X_t=n!\,\mathbf 1\{M_{L,t}\subseteq E\}\prod_{i<L}\frac{\lambda_{i+1}(M_{i,t})}{\lambda_i(M_{i,t})}.$$
--   5. The run is capped at $\lceil\mathrm{cap}\cdot n^3\varepsilon^{-2}\log^6(2n/\varepsilon)\rceil$ operations; exceeding the cap outputs $0$.
--
--   **Formalization Note** The paper's "sufficiently large" constants ($J_\alpha$, $K$, $C_\alpha$ for $\alpha=2$, and $c_R$, $c_T$, cap) are fields of `Params`; the printed constants $128$, $32$, $1/8$, $1/16$, $\alpha=2$ are fixed. The fixed choices the paper leaves open are the anchor $r=0$, the identity fallback matching, an odd number of batches, and the batch length.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), §5.5, pp.18–19 (PDF 20–21); §4.3, p.10 (PDF 12); proof of Theorem 1, p.56 (PDF 58)

import Mathlib
import Definitions.Def_CubicPermFPRAS_sampler
import Definitions.Def_CubicPermFPRAS_farChain
import Definitions.Def_CubicPermFPRAS_coolingSchedule

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

variable {n : ℕ}

/-- The holes `(u,v)` of a near-perfect matching: the first unassigned left vertex and the
first right vertex assigned to no left vertex (`none` if either does not exist). -/
def nearHoles (σ : Asg n) : Option (Fin n × Fin n) :=
  match (List.finRange n).find? (fun u => decide (σ u = none)),
      (List.finRange n).find? (fun v => decide (∀ u, σ u ≠ some v)) with
  | some u, some v => some (u, v)
  | _, _ => none

/-- The FAR action weights from `N ∈ N(u,v)` (§5.5, p.16; Remark 18, p.17), indexed by
`Fin (2n+2)`: `0` hold (rate `1`), `1` add `(u,v)` (rate `nB(u,v)`), `2 + y` left slide of the
edge `(y,σ_y)` (rate `B(u,σ_y)s_v`), `n + 2 + y` right slide of `(y,σ_y)` (rate `B(y,v)`).
Unassigned `y` get rate `0`. The rates sum to `W(u,v)`. -/
def farActW (B : Matrix (Fin n) (Fin n) ℝ) (σ : Asg n) (u v : Fin n) : Fin (2 * n + 2) → ℝ :=
  fun i =>
    if h0 : i.val = 0 then 1
    else if h1 : i.val = 1 then (n : ℝ) * B u v
    else if h : i.val < n + 2 then
      match σ ⟨i.val - 2, by omega⟩ with
      | none => 0
      | some z => B u z * colSum B v
    else
      match σ ⟨i.val - n - 2, by have := i.isLt; omega⟩ with
      | none => 0
      | some _ => B ⟨i.val - n - 2, by have := i.isLt; omega⟩ v

/-- Perform the FAR action with index `i` (see `farActW`) from `N ∈ N(u,v)`. -/
def applyFarAct (σ : Asg n) (u v : Fin n) (i : Fin (2 * n + 2)) : Asg n :=
  if h0 : i.val = 0 then σ
  else if h1 : i.val = 1 then Function.update σ u (some v)
  else if h : i.val < n + 2 then
    match σ ⟨i.val - 2, by omega⟩ with
    | none => σ
    | some z => slideLeft σ u ⟨i.val - 2, by omega⟩ z
  else
    match σ ⟨i.val - n - 2, by have := i.isLt; omega⟩ with
    | none => σ
    | some _ => Function.update σ ⟨i.val - n - 2, by have := i.isLt; omega⟩ (some v)

/-- One FAR transition from two uniforms (§5.5, p.16; Remark 18, p.17): with probability `1/2`
stay; otherwise from `M ∈ P` delete a uniformly chosen edge, and from `N ∈ N(u,v)` choose an
action with probability (rate)/`W(u,v)` and perform it. -/
def farMove (B : Matrix (Fin n) (Fin n) ℝ) (σ : Asg n) (U U' : ℝ) : Asg n :=
  if U < 1 / 2 then σ
  else if IsPerfect σ then
    match pickIdx (fun _ : Fin n => (1 : ℝ)) U' with
    | none => σ
    | some u => Function.update σ u none
  else
    match nearHoles σ with
    | none => σ
    | some (u, v) =>
      match pickIdx (farActW B σ u v) U' with
      | none => σ
      | some i => applyFarAct σ u v i

/-- One FAR transition as a program: charge `⌈log₂(2n)⌉ + 1` ("each transition takes `O(log n)`
time", p.16) plus the two uniforms. -/
def farStep (B : Matrix (Fin n) (Fin n) ℝ) (σ : Asg n) : Prog (Asg n) := do
  tick (treeCharge n)
  let U ← unif
  let U' ← unif
  return farMove B σ U U'

/-- One Phase-1 learning batch at a fixed temperature (§5.5, p.18–19): `X₀` is a sampler output
with error tolerance `1/16` (Lemma 8), `X_t` is a FAR transition from `X_{t−1}` for
`1 ≤ t < T_F`, and the value is the vector of frequencies
`p̂_v = |{t < T_F : X_t ∈ N(r,v)}| / T_F`. Charges: `1` per recorded state, `n` for the
divisions. -/
def farBatch (prm : SamplerParams) (B : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (TF : ℕ) :
    Prog (Fin n → ℝ) := do
  let X₀ ← samplerCore prm B (1 / 16)
  let mut X := X₀
  let mut cnt : Fin n → ℕ := fun _ => 0
  for t in List.range TF do
    if t ≠ 0 then
      X ← farStep B X
    tick 1
    match nearHoles X with
    | some (u, v) => if u = r then cnt := Function.update cnt v (cnt v + 1)
    | none => pure ()
  tick n
  return fun v => (cnt v : ℝ) / TF

/-- The anchor-weight update, Eq. (15), p.18 (PDF 20): from supplied anchor weights
`w(r,·)`, the rescaled matrix `B` and positive frequency estimates `p̂_v`,
`w̃(r,v) = w(r,v)W(r,v)/p̂_v` and `w'(r,v) = w̃(r,v) ∑_{z ∈ V₂} λ(r,z)/w̃(r,z)`. -/
def anchorUpdate (lam B : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (w phat : Fin n → ℝ) :
    Fin n → ℝ :=
  let wtil : Fin n → ℝ := fun v => w v * Wfar B r v / phat v
  fun v => wtil v * ∑ z, lam r z / wtil z

/-- The median of a list (the `((R+1)/2)`-th order statistic for a list of odd length `R`). -/
def median (l : List ℝ) : ℝ := (l.insertionSort (· ≤ ·)).getD ((l.length - 1) / 2) 0

/-- The constants of the whole algorithm: the sampler's constants for roughness `α = 2`, and
the constants `c_R` (number of batches `R = 2⌈c_R log(2n(L+1)/δ)⌉ + 1`), `c_T` (batch length
`T_F = ⌈c_T n² log(2n)⌉`) and `cap` (operation cap `⌈cap · n³ε⁻²log⁶(2n/ε)⌉`). These are the
paper's "sufficiently large" constants (pp.18–19, p.56). -/
structure Params extends SamplerParams where
  cR : ℝ
  cT : ℝ
  cap : ℝ

/-- The operation cap `⌈cap · n³ ε⁻² log⁶(2n/ε)⌉` (proof of Theorem 1, p.56). -/
def budget (prm : Params) (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈prm.cap * (n : ℝ) ^ 3 * ε⁻¹ ^ 2 * Real.log (2 * n / ε) ^ 6⌉₊

open Classical in
/-- The main body of the algorithm for `n ≥ 1` with anchor `r` (see `fprasProg`). -/
def fprasMain (prm : Params) (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (r : Fin n) : Prog ℝ := do
  tick (n ^ 3 + 1)
  if ¬ HasPM A then return 0
  let L := coolLen n
  tick (n + L + 2)
  let lamM : ℕ → Matrix (Fin n) (Fin n) ℝ := fun i => tempAct A (coolLam n i)
  buildSchedule prm.toSamplerParams n
  -- Phase 1
  let δ : ℝ := 1 / 8
  let Rb : ℕ := 2 * ⌈prm.cR * Real.log (2 * n * ((L : ℝ) + 1) / δ)⌉₊ + 1
  let TF : ℕ := ⌈prm.cT * (n : ℝ) ^ 2 * Real.log (2 * n)⌉₊
  tick 4
  let mut ws : List (Fin n → ℝ) := [fun _ => (n : ℝ)]
  let mut w : Fin n → ℝ := fun _ => (n : ℝ)
  for i in List.range L do
    let lam := lamM (i + 1)
    let B ← buildB lam w
    let mut ests : List (Fin n → ℝ) := []
    for _ in List.range Rb do
      let e ← farBatch prm.toSamplerParams B r TF
      ests := ests ++ [e]
    tick (Rb * n * Nat.clog 2 (2 * Rb) + 1)
    let phat : Fin n → ℝ := fun v => median (ests.map fun e => e v)
    if ∃ v, phat v = 0 then return 0
    tick (3 * n + 1)
    let w' : Fin n → ℝ := anchorUpdate lam B r w phat
    w := w'
    ws := ws ++ [w']
  -- Phase 2
  let N : ℕ := ⌈128 * ε⁻¹ ^ 2⌉₊
  let η : ℝ := 1 / (32 * ((L : ℝ) + 1) * N)
  tick 3
  let mut samples : List (List (Asg n)) := []
  for i in List.range (L + 1) do
    let B ← buildB (lamM i) (ws.getD i fun _ => (n : ℝ))
    let mut row : List (Asg n) := []
    for _ in List.range N do
      let M ← samplerCore prm.toSamplerParams B η
      row := row ++ [M]
    samples := samples ++ [row]
  tick (N * ((L + 1) * (n + 1) + n) + 1)
  let Ms : ℕ → ℕ → Asg n := fun i t => (samples.getD i []).getD t (idMatching n)
  let X : ℕ → ℝ := fun t =>
    (n.factorial : ℝ) * (if (∀ u v, Ms L t u = some v → A u v = 1) then 1 else 0) *
      ∏ i ∈ Finset.range L, matchWeight (lamM (i + 1)) (Ms i t) / matchWeight (lamM i) (Ms i t)
  return (1 / (N : ℝ)) * ∑ t ∈ Finset.range N, X t

/-- **The algorithm of Theorem 1 as a charged program** (§5.5, pp.18–19; proof of Theorem 1,
p.56 (PDF 58); arXiv:2609.20717, held version sha256 9e14f335…).

1. If `A` has no perfect matching, output `0` (charge `n³ + 1`, "This takes `O(n³)` time").
2. Cooling schedule `λ_i = e^{−β_i}`, `0 ≤ i ≤ L` (Lemma 7; charge `n + L + 2`), and the
   activity schedule (Lemma 10).
3. Phase 1 with `δ = 1/8`, anchor `r = 0`, `w'₀(r,·) = n`: at each `λ_i`, `1 ≤ i ≤ L`, build `B`
   from `(λ_i, w'_{i−1}(r,·))`, run `R = 2⌈c_R log(2n(L+1)/δ)⌉ + 1` independent batches, take
   coordinatewise medians `p̂_v`; if some median is `0`, output `0`; else update by Eq. (15):
   `w̃(r,v) = w(r,v)W(r,v)/p̂_v`, `w'_i(r,v) = w̃(r,v) ∑_z λ_i(r,z)/w̃(r,z)`.
4. Phase 2 with `N = ⌈128ε⁻²⌉`, `η = 1/(32(L+1)N)`: independent samples `M_{i,t}` from the
   sampler at `(λ_i, w'_i)`, and output `p̂ = N⁻¹ ∑_t X_t` with
   `X_t = n! · 1{M_{L,t} ⊆ E} · ∏_{i<L} λ_{i+1}(M_{i,t})/λ_i(M_{i,t})` (§4.3, p.10).

**Formalization Note.** `n = 0` (excluded by every statement) outputs `1 = per`. The fixed
choices the paper leaves open are: anchor `r = 0`, the identity as fallback matching, the odd
number of batches, the batch length, and `η = 1/16` for the Phase-1 sampler calls. -/
def fprasProg (prm : Params) (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) : Prog ℝ :=
  if h : n = 0 then pure 1 else fprasMain prm A ε ⟨0, by omega⟩

/-- **The algorithm of Theorem 1** on input `A`, `ε` and tape `ω`, with the operation cap
(proof of Theorem 1, p.56: "return zero if the total number of operations exceeds
`Cn³ε⁻²log⁶(n/ε)`"): the output `p̂` and the number of operations charged. -/
def permFPRAS (prm : Params) (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (ω : Tape) : Result :=
  runCapped (budget prm n ε) (fprasProg prm A ε) ω

end

end CubicPermFPRAS


