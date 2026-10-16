-- Prove2me | Definitions.Def_SpatialPricing_ABC_Control
-- name    : SpatialPricing_ABC_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:34.94501+00:00
-- url     : https://prove2.me/theorems/3bd877a0-2063-4695-bfda-c51fb5e2cd9f
-- title:
--   §5 — Arc Balancing Control, batches (14), correction (15)–(16), parameters, and event A
-- statement:
--   Arc Balancing Control uses an optimal $\mathrm{DCP}(\zeta)$ schedule as a baseline. On each arc, it divides the horizon into consecutive batches whose cumulative baseline variance weight $\lambda^{\zeta,D}_{t,ij}(1-\lambda^{\zeta,D}_{t,ij})$ reaches the target $b$. In a batch, it offsets the previous batch's realized demand surplus, distributing the adjustment in proportion to those weights. The proposed rate is projected to $[0,1]$ and is posted when the origin has at least $N$ available servers; otherwise the posted rate is zero.
--
--   For the scaled system, the theorem's parameters are
--
--   $$b_n=(\underline\tau^n)^{2/3},\qquad \epsilon_n=(\underline\tau^n)^{-1}\!\left(1+16\sqrt{2(b_n+1)\log T^n}\right),\qquad \zeta_n=2\epsilon_n,$$
--
--   where $\underline\tau^n=n\underline\tau$ and $T^n=nT$. The good event $\mathcal A$ bounds each within-batch partial sum of realized demand minus posted rate by $\eta_n=(\epsilon_n\underline\tau^n-1)/4$. The definition also gives the normalized ABC loss $L^{ABC}(n)$.
--
--   This is the control analyzed in Theorem 3 and Lemma 4.
--
--   **Formalization Note** The last batch is merged with a short trailing batch when the latter cannot reach $b$, completing (14) at the horizon. The server test uses $C_{t,i}\ge N$; the printed box has $C_{t,i}>N$, while Lemma 4 and its base case require equality to permit service. Rates are constructed by structural recursion on time. The surplus always uses realized demand and the rates actually posted, including zero during shutdown. If the DCP is infeasible, its baseline and the resulting ABC rates are zero. A zero variance denominator likewise yields correction weight zero.
-- source:
--   Chen, Lei, Jasin, accepted manuscript, LBS Research Online eprint 2845, PDF sha256 7310a8a1…480a, pp. 20–25, (14)–(16), ABC box, Theorem 3 parameters, C2 and event A

import Mathlib
import Definitions.Def_SpatialPricing_ABC_Setting

noncomputable section

namespace SpatialPricing.ABC

/-- Variance proxy of the DCP baseline on an arc and period. -/
def Instance.weight (P : Instance) (ζ : ℝ) (t : ℕ)
    (i j : Fin P.N) : ℝ :=
  P.lamD ζ t i j * (1 - P.lamD ζ t i j)

/-- The completed endpoint of batch k. A trailing batch too small to reach b is merged. -/
def Instance.batchEnd (P : Instance) (ζ b : ℝ) (i j : Fin P.N) : ℕ → ℕ
  | 0 => 0
  | k + 1 => by
      classical
      let prev := P.batchEnd ζ b i j k
      exact if h : ∃ s : ℕ, prev < s ∧ s ≤ P.T ∧
          b ≤ ∑ v ∈ Finset.Icc (prev + 1) s, P.weight ζ v i j then
        let s := Nat.find h
        if (∑ v ∈ Finset.Icc (s + 1) P.T, P.weight ζ v i j) < b then P.T else s
      else P.T

/-- The periods of batch k; batch zero and all batches after the final one are empty. -/
def Instance.batch (P : Instance) (ζ b : ℝ) (i j : Fin P.N) (k : ℕ) : Finset ℕ :=
  Finset.Icc (P.batchEnd ζ b i j (k - 1) + 1) (P.batchEnd ζ b i j k)

/-- The batch containing period t, for t in the planning horizon. -/
def Instance.kappa (P : Instance) (ζ b : ℝ) (t : ℕ) (i j : Fin P.N) : ℕ :=
  1 + ((Finset.Icc 1 P.T).filter (fun k => P.batchEnd ζ b i j k < t)).card

/-- Proportional correction weight (16). -/
def Instance.u (P : Instance) (ζ b : ℝ) (t : ℕ) (i j : Fin P.N) : ℝ :=
  P.weight ζ t i j /
    (∑ v ∈ P.batch ζ b i j (P.kappa ζ b t i j), P.weight ζ v i j)

/-- Projection of a proposed demand rate onto the feasible interval. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-- Previous-batch realized surplus, computed using posted rates in an existing history. -/
def Instance.deltaWithHistory (P : Instance) (ζ b : ℝ) (t : ℕ)
    (ω : P.Path) (hist : ℕ → Fin P.N → Fin P.N → ℝ)
    (i j : Fin P.N) : ℝ :=
  ∑ s ∈ P.batch ζ b i j (P.kappa ζ b t i j - 1),
    (P.D s ω i j - hist s i j)

/-- One step of ABC: shut an origin off if it has fewer than N available servers. -/
def Instance.abcStep (P : Instance) (ϵ ζ b : ℝ) (t : ℕ)
    (ω : P.Path) (hist : ℕ → Fin P.N → Fin P.N → ℝ)
    (i j : Fin P.N) : ℝ :=
  if (P.N : ℝ) ≤ P.avail t ω i then
    clamp01 (P.lamD ζ t i j - ϵ -
      P.u ζ b t i j * P.deltaWithHistory ζ b t ω hist i j)
  else 0

/-- Posted-rate history, constructed by structural recursion on the elapsed period. -/
def Instance.abcHist (P : Instance) (ϵ ζ b : ℝ) (ω : P.Path) :
    ℕ → (ℕ → Fin P.N → Fin P.N → ℝ)
  | 0 => fun _ _ _ => 0
  | t + 1 =>
      let old := P.abcHist ϵ ζ b ω t
      fun s i j =>
        if s = t + 1 then P.abcStep ϵ ζ b (t + 1) ω old i j
        else old s i j

/-- The rate actually posted by Arc Balancing Control. -/
def Instance.abcRate (P : Instance) (ϵ ζ b : ℝ) (t : ℕ)
    (ω : P.Path) (i j : Fin P.N) : ℝ :=
  P.abcHist ϵ ζ b ω t t i j

/-- Previous-batch surplus under the ABC rule itself. -/
def Instance.deltaPrev (P : Instance) (ϵ ζ b : ℝ) (t : ℕ)
    (ω : P.Path) (i j : Fin P.N) : ℝ :=
  ∑ s ∈ P.batch ζ b i j (P.kappa ζ b t i j - 1),
    (P.D s ω i j - P.abcRate ϵ ζ b s ω i j)

/-- Parameter b in Theorem 3. -/
def Instance.bN (P : Instance) (n : ℕ) : ℝ :=
  (P.tauN n) ^ (2 / 3 : ℝ)

/-- Parameter epsilon in Theorem 3. -/
def Instance.epsN (P : Instance) (n : ℕ) : ℝ :=
  (P.tauN n)⁻¹ *
    (1 + 16 * Real.sqrt (2 * (P.bN n + 1) * Real.log (P.TN n)))

/-- Parameter zeta in Theorem 3. -/
def Instance.zetaN (P : Instance) (n : ℕ) : ℝ := 2 * P.epsN n

/-- Threshold eta in Section 5.2. -/
def Instance.etaN (P : Instance) (n : ℕ) : ℝ :=
  (P.epsN n * P.tauN n - 1) / 4

/-- The batchwise good event A in Section 5.2. -/
def Instance.inA (P : Instance) (ϵ ζ b η : ℝ) (ω : P.Path) : Prop :=
  ∀ i j k, k ∈ Finset.Icc 1 P.T →
    ∀ t ∈ P.batch ζ b i j k,
      |∑ s ∈ Finset.Icc (P.batchEnd ζ b i j (k - 1) + 1) t,
        (P.D s ω i j - P.abcRate ϵ ζ b s ω i j)| < η

/-- The ABC loss in the scaled system, normalized by Tⁿ = nT. -/
def Instance.lossABC (P : Instance) (n : ℕ) : ℝ :=
  let Q := P.scale n
  (Q.J 0 - Q.revenue (Q.abcRate (P.epsN n) (P.zetaN n) (P.bN n))) /
    (P.TN n)

end SpatialPricing.ABC


