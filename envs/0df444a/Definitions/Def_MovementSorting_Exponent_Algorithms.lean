-- Prove2me | Definitions.Def_MovementSorting_Exponent_Algorithms
-- name    : MovementSorting_Exponent_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:03:03.234692+00:00
-- url     : https://prove2.me/theorems/e6c37f3c-bee9-4f9b-b36b-97aae5d3011b
-- title:
--   Algorithms 2, 3 and 4 with the paper's parameters and admissible route procedures
-- statement:
--   The three instances of Algorithm 1, with splitters, samples and rates exactly as in the paper. **Algorithm 2** ($d=1$, $r\ge 2$): refinement round $j+1$ draws one sample of intervals of length $h_j = \lceil\sqrt{n/b_{j-1}}\rceil$ at rate $p_j = n^{-a_j}$. **Algorithm 3** ($d \ge 2$, $r = 3$): round 2 draws a cube sample (cubes of side $H = \lceil n^{(1-a_0)/D}\rceil$, rate $p = n^{-a_1}$) and a key sample (single positions, rate $\sigma = n^{-(a_0-a_1)}$). **Algorithm 4** ($d \ge 2$, $r \ge 4$): refinement round $j+1$ draws, for every dyadic spatial scale $y \le x_\star = a_0/(2-c)$, $c = 1/d$, a sample on the scale-$y$ boxes (Definition 6.5: every axis halved $i$ times, or single positions for $y=0$) at rate $n^{-f_j(y)}$, where $f_0(x) = \min\{a_0, 1-x\}$ and $f_j = \Phi f_{j-1}$ with $(\Phi f)(y) = \sup_{0 \le x \le x_\star} \min\{f(x)+cx-\delta,\ a_0-(1-c)x-\min\{x,y\}\}$, $\delta = \beta-1$.
--
--   The route procedures are the template's parameters. `Alg2Admissible`, `Alg3Admissible` and `Alg4Admissible r m CR procs` require valid routes (`RoutesValid`) and, for every coin outcome, current configuration and state, a movement of at most `CR` times the per-instance quantity the paper bounds for its own route: $n(|S|+1)$ for the splitter round; for Algorithm 2, $n(\#\text{selected}+1) + h\sum_{J\text{ selected}}\sum_I\sqrt{Q_{I,J}}$ (Lines 4–6, Lemma 5.9) and $h(k\sqrt{P}+k) + h\sum_{I,J}\sqrt{Q_{I,J}}$ for the cleanup (Line 10, Lemma 5.10); for Algorithm 3, $n + \sum_{J\text{ selected}} m P_J^{1-1/d} + H\sum_{J\text{ selected}}\sum_I Q_{I,J} + m(|W_{\text{key}}|^{1-1/D}+1)$ (Lemma 6.3 and the key-sample bound) and $m(P^{1-1/D}+1) + H\sum Q_{I,J}$ for the cleanup; for Algorithm 4, the Lemma 6.6 bound $m + \sum_x n^{cx} N_x(W)$ for each sample's required set (summed over the samples of the round) and for the cleanup's. The list of dyadic scales includes scale zero exactly once, including when m is a power of two. The cube-tour, cube-visit and key-sample terms in Algorithm 3 are separate additive terms.
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Algorithm 2 and Section 5.4, p. 27; Algorithm 3, Definition 6.2, p. 30; Definitions 6.5, 6.8, Algorithm 4, pp. 32–33; Lemmas 5.9, 5.10, 6.3, 6.6

import Definitions.Def_MovementSorting_Exponent_Sampling
import Definitions.Def_MovementSorting_Exponent_Beta

set_option autoImplicit false

namespace MovementSorting.Exponent

/-! # Algorithms 2, 3 and 4 (Wang 2026, §5.4 p. 27, §6.2 p. 30, §6.3 pp. 32–33)

Each instance fixes the paper's splitters, samples and rates exactly. Its route procedures are
the parameters of the template (Algorithm 1, p. 25): an admissible procedure family returns
valid routes visiting all required configurations (`Template.RoutesValid`) and, round by round,
has movement at most `CR` times the per-instance quantity that the paper's own route (built from
Lemma 5.1(i) / Lemma 6.6) is shown to move in the proofs of Lemmas 5.9, 5.10, 6.3, 6.6 and
Theorem 6.4. -/

/-- The number of splitters `⌈n / b_0⌉` (real schedule). -/
noncomputable def splitterCount (d r m : ℕ) : ℕ := ⌈nR d m / realScale d r m 0⌉₊

/-- The partition of `[m]^d` into cubes of side `H` (0-based; the last cube along an axis may be
shorter). For `d = 1` these are the intervals of length `H`; for `H = 1`, single positions. -/
def cubeBox (d m H : ℕ) : Pos d m → (Fin d → ℕ) := fun x i => (x i : ℕ) / H

/-- The scale boxes of Definition 6.5: every axis halved `i` times, the box of `x` along axis
`a` being `⌊x_a 2^i / m⌋` (sides `⌊m/2^i⌋` or `⌈m/2^i⌉`; the partitions are nested). -/
def levelBox (d m i : ℕ) : Pos d m → (Fin d → ℕ) := fun x a => (x a : ℕ) * 2 ^ i / m

/-! ## Algorithm 2 (the line, `d = 1`, `r ≥ 2`) -/

/-- `h_j = ⌈√(n / b_{j-1})⌉`, `1 ≤ j ≤ r - 1`. -/
noncomputable def hLine (r m j : ℕ) : ℕ := ⌈Real.sqrt (nR 1 m / realScale 1 r m (j - 1))⌉₊

/-- `p_j = n^{-a_j}`, `1 ≤ j ≤ r - 2`. -/
noncomputable def pLine (r m j : ℕ) : ℝ := nR 1 m ^ (-(schedExp 1 r j))

/-- Algorithm 2: `⌈n/b_0⌉` splitters; refinement round `j + 1` draws one sample of intervals of
length `h_j` at rate `p_j`. -/
noncomputable def alg2Plan (r m : ℕ) : Plan 1 m :=
  ⟨r, splitterCount 1 r m, fun j => [⟨cubeBox 1 m (hLine r m j), pLine r m j⟩]⟩

/-- Admissible route procedures for Algorithm 2 with constant `CR`: valid routes, and movement at
most `CR` times: `n(|S| + 1)` for the splitter round (Line 2); `n(#selected + 1) +
h Σ_{J selected} Σ_I √Q_{I,J}` for refinement round `j + 1` (Lines 4–6, proof of Lemma 5.9);
`h(k √P + k) + h Σ_{I,J} √Q_{I,J}` for the cleanup (Line 10, proof of Lemma 5.10), where `k` is
the number of intervals of length `h = h_{r-1}` and `P` the number of occupied product boxes. -/
def Alg2Admissible (r m : ℕ) (CR : ℝ) (procs : Coins 1 m → ℕ → RouteProc 1 m) : Prop :=
  (∀ ω, ((alg2Plan r m).template procs ω).RoutesValid r) ∧
  ∀ (ω : Coins 1 m) (cur : Option (Config 1 m)) (st : State 1 m),
    ((movement (procs ω 0 cur st) : ℝ) ≤ CR * (nR 1 m * (ω.1.card + 1))) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ r - 2 →
      (movement (procs ω j cur st) : ℝ) ≤ CR * (nR 1 m * ((Plan.selOf ω j 0).card + 1) +
        (hLine r m j : ℝ) * ∑ J ∈ Plan.selOf ω j 0, ∑ I ∈ boxes (cubeBox 1 m (hLine r m j)),
          Real.sqrt (Qbox st (cubeBox 1 m (hLine r m j)) I J))) ∧
    ((movement (procs ω (r - 1) cur st) : ℝ) ≤ CR *
      ((hLine r m (r - 1) : ℝ) *
        ((boxes (cubeBox 1 m (hLine r m (r - 1)))).card *
            Real.sqrt (occupied st (cubeBox 1 m (hLine r m (r - 1)))).card +
          (boxes (cubeBox 1 m (hLine r m (r - 1)))).card) +
       (hLine r m (r - 1) : ℝ) *
        ∑ IJ ∈ boxes (cubeBox 1 m (hLine r m (r - 1))) ×ˢ boxes (cubeBox 1 m (hLine r m (r - 1))),
          Real.sqrt (Qbox st (cubeBox 1 m (hLine r m (r - 1))) IJ.1 IJ.2)))

/-! ## Algorithm 3 (`d ≥ 2`, `r = 3`) -/

/-- `H = ⌈n^{(1 - a_0)/D}⌉` (exponents of Lemma 2.5 at `r = 3`). -/
noncomputable def Hcube (d m : ℕ) : ℕ := ⌈nR d m ^ ((1 - schedExp d 3 0) / (2 * d : ℝ))⌉₊

/-- `p = n^{-a_1}`. -/
noncomputable def pCube (d m : ℕ) : ℝ := nR d m ^ (-(schedExp d 3 1))

/-- `σ = n^{-(a_0 - a_1)}`. -/
noncomputable def sigmaKey (d m : ℕ) : ℝ := nR d m ^ (-(schedExp d 3 0 - schedExp d 3 1))

/-- Algorithm 3: `⌈n/b_0⌉` splitters; round 2 draws a cube sample (side `H`, rate `p`) and a key
sample (single positions, rate `σ`), independently. -/
noncomputable def alg3Plan (d m : ℕ) : Plan d m :=
  ⟨3, splitterCount d 3 m, fun _ => [⟨cubeBox d m (Hcube d m), pCube d m⟩, ⟨cubeBox d m 1, sigmaKey d m⟩]⟩

/-- `P_J`: the number of cubes `I` with `Q_{I,J} > 0`. -/
def PJ {d m : ℕ} (st : State d m) (box : Pos d m → (Fin d → ℕ)) (J : Fin d → ℕ) : ℕ :=
  ((boxes box).filter (fun I => 0 < Qbox st box I J)).card

/-- Admissible route procedures for Algorithm 3 with constant `CR` (`m = n^{1/d}`, `D = 2d`):
valid routes; splitter round `n(|S| + 1)`; round 2 (Lines 3–7, proof of Lemma 6.3 and the key
sample bound before Theorem 6.4) `n + Σ_{J selected} m P_J^{1-1/d} + H Σ_{J selected} Σ_I Q_{I,J}
+ m(|W_key|^{1-1/D} + 1)`; cleanup (Line 9, proof of Theorem 6.4) `m(P^{1-1/D} + 1) + H Σ Q_{I,J}`. -/
def Alg3Admissible (d m : ℕ) (CR : ℝ) (procs : Coins d m → ℕ → RouteProc d m) : Prop :=
  (∀ ω, ((alg3Plan d m).template procs ω).RoutesValid 3) ∧
  ∀ (ω : Coins d m) (cur : Option (Config d m)) (st : State d m),
    ((movement (procs ω 0 cur st) : ℝ) ≤ CR * (nR d m * (ω.1.card + 1))) ∧
    ((movement (procs ω 1 cur st) : ℝ) ≤ CR * (nR d m +
      (∑ J ∈ Plan.selOf ω 1 0,
        (m : ℝ) * ((PJ st (cubeBox d m (Hcube d m)) J : ℕ) : ℝ) ^ (1 - 1 / (d : ℝ))) +
      (Hcube d m : ℝ) * (∑ J ∈ Plan.selOf ω 1 0, ∑ I ∈ boxes (cubeBox d m (Hcube d m)),
        (Qbox st (cubeBox d m (Hcube d m)) I J : ℝ)) +
      (m : ℝ) * (((refineReq (selectedPositions ⟨cubeBox d m 1, sigmaKey d m⟩ (Plan.selOf ω 1 1))
          st).card : ℝ) ^ (1 - 1 / (2 * d : ℝ)) + 1))) ∧
    ((movement (procs ω 2 cur st) : ℝ) ≤ CR *
      ((m : ℝ) * (((occupied st (cubeBox d m (Hcube d m))).card : ℝ) ^ (1 - 1 / (2 * d : ℝ)) + 1) +
       (Hcube d m : ℝ) *
        ∑ IJ ∈ boxes (cubeBox d m (Hcube d m)) ×ˢ boxes (cubeBox d m (Hcube d m)),
          (Qbox st (cubeBox d m (Hcube d m)) IJ.1 IJ.2 : ℝ)))

/-! ## Algorithm 4 (`d ≥ 2`, `r ≥ 4`) -/

/-- A spatial scale `x` of Definition 6.5: its box partition and its exponent `x`
(`n^x` = the volume of its boxes). -/
structure SpatialScale (d m : ℕ) where
  box : Pos d m → (Fin d → ℕ)
  expo : ℝ

/-- The dyadic spatial scales: `x = 0` (single positions) and, for `0 ≤ i ≤ ⌊log₂ m⌋`
with `2^i < m`, the scale with `n^x = (m/2^i)^d` (boxes `levelBox i`). The strict inequality
avoids listing scale zero twice when `m` is a power of two. -/
noncomputable def dyadicScales (d m : ℕ) : List (SpatialScale d m) :=
  ⟨cubeBox d m 1, 0⟩ :: ((List.range (Nat.log 2 m + 1)).filter (fun i => 2 ^ i < m)).map
    (fun i => ⟨levelBox d m i, Real.logb (nR d m) (((m : ℝ) / 2 ^ i) ^ d)⟩)

/-- `x⋆ = a_0/(2 - c)`, `c = 1/d`. -/
noncomputable def xStar (d r : ℕ) : ℝ := schedExp d r 0 / (2 - 1 / (d : ℝ))

/-- `φ_f(x) = f(x) + c x - (β - 1)`. -/
noncomputable def phiF (d r : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ := f x + x / d - (beta d r - 1)

/-- `ψ_y(x) = a_0 - (1 - c) x - min{x, y}`. -/
noncomputable def psiY (d r : ℕ) (y x : ℝ) : ℝ :=
  schedExp d r 0 - (1 - 1 / (d : ℝ)) * x - min x y

/-- `(Φ f)(y) = sup_{0 ≤ x ≤ x⋆} min{φ_f(x), ψ_y(x)}` (Definition 6.8). -/
noncomputable def PhiOp (d r : ℕ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ⨆ x : Set.Icc (0 : ℝ) (xStar d r), min (phiF d r f x) (psiY d r y x)

/-- The profiles `f_0(x) = min{a_0, 1 - x}`, `f_j = Φ f_{j-1}`. -/
noncomputable def profile (d r : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun x => min (schedExp d r 0) (1 - x)
  | j + 1 => PhiOp d r (profile d r j)

/-- The samples of refinement round `j + 1`: for every dyadic `y ≤ x⋆` a sample at scale `y` with
rate `n^{-f_j(y)}`. -/
noncomputable def alg4Samples (d r m j : ℕ) : List (Sample d m) :=
  ((dyadicScales d m).filter (fun s => decide (s.expo ≤ xStar d r))).map
    (fun s => ⟨s.box, nR d m ^ (-(profile d r j s.expo))⟩)

/-- Algorithm 4: `⌈n/b_0⌉` splitters; refinement round `j + 1` draws the samples
`alg4Samples d r m j`, independently. -/
noncomputable def alg4Plan (d r m : ℕ) : Plan d m := ⟨r, splitterCount d r m, alg4Samples d r m⟩

/-- The route bound of Lemma 6.6 for a set `W`: `m + Σ_x n^{cx} N_x(W)` over the dyadic `x`
(`n^{cx} = n^{x/d}` the side of a scale-`x` box, `m = n^{1/d}`). -/
noncomputable def lemma66Bound (d m : ℕ) (W : Finset (Config d m)) : ℝ :=
  (m : ℝ) + ((dyadicScales d m).map (fun s => nR d m ^ (s.expo / (d : ℝ)) * (productCount W s.box : ℝ))).sum

/-- Admissible route procedures for Algorithm 4 with constant `CR`: valid routes; splitter round
`n(|S| + 1)`; refinement round `j + 1` (Line 4) the sum over its samples of the Lemma 6.6 bound
for that sample's required configurations `W_y`; cleanup (Line 7) the Lemma 6.6 bound for its
required configurations. -/
def Alg4Admissible (d r m : ℕ) (CR : ℝ) (procs : Coins d m → ℕ → RouteProc d m) : Prop :=
  (∀ ω, ((alg4Plan d r m).template procs ω).RoutesValid r) ∧
  ∀ (ω : Coins d m) (cur : Option (Config d m)) (st : State d m),
    ((movement (procs ω 0 cur st) : ℝ) ≤ CR * (nR d m * (ω.1.card + 1))) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ r - 2 →
      (movement (procs ω j cur st) : ℝ) ≤ CR *
        (((alg4Samples d r m j).zip (ω.2.getD (j - 1) [])).map (fun sk =>
          lemma66Bound d m (refineReq (selectedPositions sk.1 sk.2) st))).sum) ∧
    ((movement (procs ω (r - 1) cur st) : ℝ) ≤ CR * lemma66Bound d m (cleanupReq st))

end MovementSorting.Exponent


