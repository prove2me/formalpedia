-- Prove2me | Definitions.Def_CanadaCTP_PathOpt
-- name    : CanadaCTP_PathOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:41.920795+00:00
-- url     : https://prove2.me/theorems/b50b2836-4383-46bd-a5be-b164443f4a42
-- title:
--   Definitions 1, 2, 5, 6, 8, 9 — PathOpt, $\mathrm{prob}_X$, coin strategies, $\alpha$, $\beta$, $X'$ and threshold strategies
-- statement:
--   A **PathOpt** instance is a single path with $m\ge0$ edges and independent weights $X=(X_j)_{j\in[m]}$ (Definition 1); its algorithms are the randomized adaptive policies on this path, which may walk back and may stop. For a budget $b\ge0$,
--   $$
--   \mathrm{prob}_X(b)=\sup\{\mathrm{arrivalProb}(A) : \mathrm{expCost}(A)\le b\}
--   $$
--   is the optimal probability of reaching the last vertex with expected cost at most $b$ (Definitions 2, 5).
--
--   A **coin vector** $\mathrm{coin}\in\mathrm{COIN}=\times_j[0,1]^{|\operatorname{supp}X_j|}$ represents the algorithm that, in front of edge $j$ with realization $x$, traverses it with probability $\mathrm{coin}(j,x)$ and otherwise stops (Definition 6). Its arrival probability and expected cost are
--   $$
--   \mathrm{arrivalProb}(\mathrm{coin})=\sum_{x_1,\dots,x_m}\prod_j P[X_j=x_j]\prod_j\mathrm{coin}(j,x_j),\qquad
--   \mathrm{expCost}(\mathrm{coin})=\sum_{j}\sum_{x_1,\dots,x_j}\prod_{\ell\le j}P[X_\ell=x_\ell]\prod_{\ell\le j}\mathrm{coin}(\ell,x_\ell)\,x_j .
--   $$
--   $\alpha(j,x,\mathrm{coin})$ and $\beta(j,x,\mathrm{coin})$ are the coefficients of $\mathrm{coin}(j,x)$ in these two affine expressions. For $m\ge1$, $X'=(X_2,\dots,X_m)$ and $\mathrm{coin}'$ is the restriction of $\mathrm{coin}$ to $X'$ (Definition 8). With $b'=\mathrm{expCost}(\mathrm{coin}')$, $\mathrm{coin}$ is a **threshold strategy** with threshold $\theta\ge0$ (Definition 9) if (P1) $\mathrm{arrivalProb}(\mathrm{coin}')=\mathrm{prob}_{X'}(b')$; (P2) $\mathrm{coin}(1,x)=1$ for $x<\theta$ and $\mathrm{coin}(1,x)=0$ for $x>\theta$; (P3) some line through $(-\theta,0)$ and $(b',\mathrm{prob}_{X'}(b'))$ lies on or above $\mathrm{prob}_{X'}$ on $[0,\infty)$.
--
--   These objects carry Lemmas 1–7.
--
--   **Formalization Note** Edges are 0-indexed, so the paper's edge $1$ is edge `0`. $\alpha$ and $\beta$ are defined by substitution: the formula at $\mathrm{coin}(j,x)=1$ minus the formula at $\mathrm{coin}(j,x)=0$. The coin policy clamps its probability to $[0,1]$, which is the identity on $\mathrm{COIN}$. The expected-cost formula sums over full realizations; the factors for $\ell>j$ sum to $1$.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Definitions 1, 2 (p.6), 5, 6 (p.7), the formulas in the proof of Lemma 2 (p.8), Algorithm 2 (p.9), Definition 8 (p.11), Definition 9 (pp.13–14)

import Mathlib
import Definitions.Def_CanadaCTP_Model

namespace CanadaCTP

open scoped ENNReal

/-! # The PathOpt problem and coin strategies

Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
§3.1: Definitions 1, 2, 5, 6 (pp.6–7), the formulas in the proof of Lemma 2 (p.8), the
coefficients of Algorithm 2 (p.9), Definition 8 (p.11) and Definition 9 (pp.13–14).

**Formalization Note.** A PathOpt instance is the one-path instance `pathInst X` (`m ≥ 0`
edges); its algorithms are all randomized stateful policies on it (walking back and stopping
allowed), with `arrivalProb = arrProb` and `expCost = expCost` (Definition 5). Edges are
0-indexed (`Fin m`), so the paper's first edge `1` is `0` here. -/

/-- The PathOpt instance on a path with edge distributions `X` (Definition 1, `m ≥ 0`). -/
def pathInst {m : ℕ} (X : Fin m → EdgeDist) : Inst := ⟨1, fun _ => m, fun _ => X⟩

/-- `prob_X(b)`, Definition 2: the optimal probability of reaching the end of the path over all
PathOpt algorithms whose expected cost is at most `b`. The set is non-empty (stopping at once
costs `0`) and bounded by `1`. -/
noncomputable def probX {m : ℕ} (X : Fin m → EdgeDist) (b : ℝ) : ℝ :=
  sSup {p : ℝ | ∃ (Mem : Type) (A : Policy (pathInst X) Mem),
    expCost (pathInst X) A ≤ ENNReal.ofReal b ∧ p = (arrProb (pathInst X) A).toReal}

/-- The value of support point `x` of edge `j`. -/
def val {m : ℕ} (X : Fin m → EdgeDist) (j : Fin m) (x : Fin (X j).pts.length) : ℝ :=
  ((X j).pts.get x).1

/-- The probability `P[X_j = x]` of support point `x` of edge `j`. -/
def prb {m : ℕ} (X : Fin m → EdgeDist) (j : Fin m) (x : Fin (X j).pts.length) : ℝ :=
  ((X j).pts.get x).2

/-- `d = Σⱼ |supp(X_j)|`. -/
def dX {m : ℕ} (X : Fin m → EdgeDist) : ℕ := ∑ j, (X j).pts.length

/-- A coin vector `coin(j, x)`, one real per edge and support point (Definition 6). -/
abbrev Coin {m : ℕ} (X : Fin m → EdgeDist) := (j : Fin m) → Fin (X j).pts.length → ℝ

/-- `coin ∈ COIN = ×ⱼ [0,1]^{|supp(X_j)|}`. -/
def InCOIN {m : ℕ} (X : Fin m → EdgeDist) (c : Coin X) : Prop := ∀ j x, c j x ∈ Set.Icc 0 1

/-- The index of value `v` in the support of `D`, if any (the first match; values are
distinct). -/
noncomputable def idxOf (D : EdgeDist) (v : ℝ) : Option (Fin D.pts.length) := by
  classical
  exact (List.finRange D.pts.length).find? fun x => decide ((D.pts.get x).1 = v)

/-- The algorithm represented by a coin vector (Definition 6): at the start vertex of edge `j`,
with the weight of edge `j` revealed as the support point `x`, traverse edge `j` with
probability `coin(j, x)` and otherwise stop. It never walks back. The probability is clamped to
`[0,1]` so that the step is a distribution; under `InCOIN` the clamp is the identity. -/
noncomputable def coinPolicy {m : ℕ} (X : Fin m → EdgeDist) (c : Coin X) :
    Policy (pathInst X) Unit where
  init := ()
  step := fun _ o =>
    let i0 : Fin (pathInst X).k := ⟨0, Nat.one_pos⟩
    let j : ℕ := match o.pos with
      | Pos.mid _ v => v
      | _ => 0
    if h : j < m then
      match o.rev i0 ⟨j, h⟩ with
      | some v =>
          match idxOf (X ⟨j, h⟩) v with
          | some x =>
              (coinFlip (c ⟨j, h⟩ x)).map
                fun b => (if b then Move.fwd i0 else Move.stop, ())
          | none => PMF.pure (Move.stop, ())
      | none => PMF.pure (Move.stop, ())
    else PMF.pure (Move.stop, ())

/-- A full realization of the path: one support index per edge. -/
abbrev PathRealz {m : ℕ} (X : Fin m → EdgeDist) := (j : Fin m) → Fin (X j).pts.length

/-- `arrivalProb(coin)`, the closed formula of the proof of Lemma 2 (p.8):
`Σ_{x₁…x_m} Πⱼ P[Xⱼ = xⱼ] · Πⱼ coin(j, xⱼ)`. -/
noncomputable def coinArr {m : ℕ} (X : Fin m → EdgeDist) (c : Coin X) : ℝ :=
  ∑ ι : PathRealz X, (∏ j, prb X j (ι j)) * ∏ j, c j (ι j)

/-- `expCost(coin)`, the closed formula of the proof of Lemma 2 (p.8):
`Σⱼ Σ_{x₁…xⱼ} Π_{ℓ≤j} P[X_ℓ = x_ℓ] · Π_{ℓ≤j} coin(ℓ, x_ℓ) · xⱼ`.

**Formalization Note.** The inner sum runs over full realizations `x₁…x_m`; the factors
`P[X_ℓ = x_ℓ]` for `ℓ > j` sum to `1`, so this is the printed prefix sum. -/
noncomputable def coinCost {m : ℕ} (X : Fin m → EdgeDist) (c : Coin X) : ℝ :=
  ∑ j : Fin m, ∑ ι : PathRealz X,
    (∏ ℓ, prb X ℓ (ι ℓ)) * (∏ ℓ ∈ Finset.Iic j, c ℓ (ι ℓ)) * val X j (ι j)

/-- The coin vector with entry `(j, x)` replaced by `t`. -/
def updC {m : ℕ} {X : Fin m → EdgeDist} (c : Coin X) (j : Fin m) (x : Fin (X j).pts.length)
    (t : ℝ) : Coin X :=
  Function.update c j (Function.update (c j) x t)

/-- `α(j, x, coin)` of Algorithm 2: the coefficient of `coin(j, x)` in `arrivalProb(coin)`
(by Lemma 2 the formula is affine in `coin(j, x)`). `A(j, x, coin) = coinArr X (updC c j x 0)`. -/
noncomputable def alphaC {m : ℕ} (X : Fin m → EdgeDist) (c : Coin X) (j : Fin m)
    (x : Fin (X j).pts.length) : ℝ :=
  coinArr X (updC c j x 1) - coinArr X (updC c j x 0)

/-- `β(j, x, coin)` of Algorithm 2: the coefficient of `coin(j, x)` in `expCost(coin)`.
`B(j, x, coin) = coinCost X (updC c j x 0)`. -/
noncomputable def betaC {m : ℕ} (X : Fin m → EdgeDist) (c : Coin X) (j : Fin m)
    (x : Fin (X j).pts.length) : ℝ :=
  coinCost X (updC c j x 1) - coinCost X (updC c j x 0)

/-- `X′ = (X₂, …, X_m)`, Definition 8 (p.11), for a path with `n + 1 ≥ 1` edges. -/
def tailDist {n : ℕ} (X : Fin (n + 1) → EdgeDist) : Fin n → EdgeDist := fun j => X j.succ

/-- `coin′`, the restriction of `coin` to the path `X′` (Definition 8). -/
def tailCoin {n : ℕ} {X : Fin (n + 1) → EdgeDist} (c : Coin X) : Coin (tailDist X) :=
  fun j x => c j.succ x

/-- Threshold strategies, Definition 9 (pp.13–14), with threshold `θ`, for a path with
`n + 1 ≥ 1` edges. With `X′`, `coin′` of Definition 8 and `b′ = expCost(coin′)`:
(P1) `arrivalProb(coin′) = prob_{X′}(b′)`;
(P2) `coin(1, x) = 1` for realizations `x < θ` and `coin(1, x) = 0` for `x > θ`;
(P3) some line `ℓ(y) = a·y + e` through `(−θ, 0)` and `(b′, prob_{X′}(b′))` satisfies
`ℓ(y) ≥ prob_{X′}(y)` for all `y ≥ 0`.

**Formalization Note.** `arrivalProb`, `expCost` of coin strategies are the closed formulas
`coinArr`, `coinCost`, which Lemma 2 identifies with the semantics. The paper's
`expCost(coin) = b` is the budget `b := coinCost X c` at which Lemma 6 is stated. -/
def IsThreshold {n : ℕ} (X : Fin (n + 1) → EdgeDist) (c : Coin X) (θ : ℝ) : Prop :=
  0 ≤ θ ∧
  coinArr (tailDist X) (tailCoin c) = probX (tailDist X) (coinCost (tailDist X) (tailCoin c)) ∧
  (∀ x, val X 0 x < θ → c 0 x = 1) ∧ (∀ x, θ < val X 0 x → c 0 x = 0) ∧
  ∃ a e : ℝ, a * (-θ) + e = 0 ∧
    a * coinCost (tailDist X) (tailCoin c) + e =
      probX (tailDist X) (coinCost (tailDist X) (tailCoin c)) ∧
    ∀ y, 0 ≤ y → probX (tailDist X) y ≤ a * y + e

end CanadaCTP


