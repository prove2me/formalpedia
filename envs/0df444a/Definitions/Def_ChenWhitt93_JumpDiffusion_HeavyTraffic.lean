-- Prove2me | Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic
-- name    : ChenWhitt93_JumpDiffusion_HeavyTraffic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:48:13.827192+00:00
-- url     : https://prove2.me/theorems/b15ac685-5f92-4719-a542-2e9bc0f9f792
-- title:
--   Section 4 — scalings (4.1)–(4.5), (4.10), (4.12), limit processes (4.9), (4.14)–(4.17), and the assumptions of Section 4(A)
-- statement:
--   Consider a sequence of networks, indexed by $n$, all with the same routing $R$. Network $n$ has primitive data $Z^n(0),A^n,S^n,(u^{j,n}_k,d^{j,n}_k)$ and rates $\lambda^n,\mu^n$. This file defines the scaled objects of Section 4 of Chen and Whitt (1993).
--
--   1. **Scaled primitive data** (the left-hand sides of (4.1)–(4.5)):
--   $$
--   \tfrac1{\sqrt n}Z^n(0),\quad \tfrac1{\sqrt n}[A^n(nt)-\lambda^n nt],\quad \tfrac1{\sqrt n}[S^n(nt)-\mu^n nt],\quad \tfrac1{\sqrt n}[R_{kj}(\lfloor nt\rfloor)-P_{kj}nt],\quad \Big(\tfrac{u^{j,n}_k}{n},\tfrac{d^{j,n}_k}{\sqrt n}\Big).
--   $$
--   Up times are scaled by $n$ and down times by $\sqrt n$.
--   2. **Limit primitive data**: $\hat Z(0)\in\mathbb R^J$, paths $\hat A,\hat S$ in $\mathbb R^J$, $\hat R$ in $\mathbb R^{J\times J}$, and durations $(u^j_k,d^j_k)$. They converge in the sense of (4.18)–(4.22): the initial vector converges, the three path families converge u.o.c. on $[0,\infty)$, and the durations converge coordinatewise.
--   3. **The limit down-time process (4.9)**:
--   $$
--   \hat N_j(t)=\sup\Big\{m\ge 0:\sum_{k=1}^m u^j_k\le t\Big\},\qquad \hat D_j(t)=\sum_{k=1}^{\hat N_j(t)}d^j_k,
--   $$
--   and its prelimit $\hat D^n_j(t)=n^{-1/2}D^n_j(nt)$ (4.10).
--   4. **The limit free process**, (4.14)–(4.16):
--   $$
--   \hat X(t)=\hat Z(0)+\hat\xi(t)+\hat\eta(t),\qquad \hat\xi_j(t)=\hat A_j(t)+\sum_{k=1}^J\big[\hat R_{kj}(\mu_kt)+P_{kj}\hat S_k(t)\big]-\hat S_j(t),
--   $$
--   $$
--   \hat\eta(t)=\big(c_\lambda-[I-P^{\mathsf t}]c_\mu\big)t+[I-P^{\mathsf t}]\operatorname{diag}(\mu)\hat D(t).
--   $$
--   5. **The scaled processes (4.12)** $\hat Z^n(t)=n^{-1/2}Z^n(nt)$, $\hat B^n(t)=n^{-1/2}[B^n(nt)-nt]$, $\hat Y^n(t)=n^{-1/2}Y^n(nt)$, stacked with $\hat D^n$ into one path in $\mathbb R^{4J}$. The limit $(\hat Z,\hat B,\hat Y,\hat D)$ is stacked the same way, with $\hat B=-\hat D-\hat Y$ (4.17).
--   6. **Assumptions.** (4.6)–(4.8) require $\sqrt n(\lambda^n-\lambda)\to c_\lambda$ with $\lambda\ge 0$, $\sqrt n(\mu^n-\mu)\to c_\mu$ with $\mu>0$, and $\lambda=[I-P^{\mathsf t}]\mu$ with $P$ substochastic and $P^k\to 0$. The regularity of Section 4(A) requires $\hat A,\hat S,\hat R$ continuous on $[0,\infty)$ and $\sum_{k=1}^m u^j_k\to\infty$ as $m\to\infty$. (4.11) requires that no two distinct coordinates of $\hat D$ jump at the same time $t>0$. The pathwise hypothesis bundles, for deterministic sequences, Section 3's assumptions on every network, (4.6)–(4.8), (4.18)–(4.22) and the limit's regularity with (4.11). Finally, a random network has all primitive coordinates measurable.
--
--   **Formalization Note** The network index is `n : ℕ`. The paper's networks are $n\ge 1$; at $n=0$ the scalings divide by $0$, which Lean evaluates to $0$, and only the tail $n\to\infty$ enters any statement. $\hat N_j(t)$ is a supremum in $\mathbb N$. Its set is bounded whenever $\sum_k u^j_k=\infty$, which every statement assumes, and it is empty (value $0$) for $t<0$. Paths whose laws are compared (the scaled primitive paths, their limits and the four stacked processes) are extended by $0$ to $t<0$, so that their laws depend only on $t\ge 0$. The routing matrix $P$ has rows indexed by the origin station: $P_{jk}$ is the fraction of departures from $j$ that go to $k$, and $(P^{\mathsf t}v)_j=\sum_k P_{kj}v_k$.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), pp. 347–350, Section 4(A) (4.1)–(4.8), Section 4(B) (4.9)–(4.11), (4.12)–(4.17); p. 351, (4.18)–(4.22)

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_M1
import Definitions.Def_ChenWhitt93_JumpDiffusion_Reflection
import Definitions.Def_ChenWhitt93_JumpDiffusion_Network

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory Matrix

/-!
Chen and Whitt (1993), Section 4, pp. 347–350: a sequence of networks indexed by `n`, the
scalings (4.1)–(4.5), (4.10), (4.12), the limit primitives and the limit processes (4.9),
(4.13)–(4.17). The network index is `n : ℕ`; the page's networks are `n ≥ 1`, and every
statement below only uses the tail `n → ∞` (at `n = 0` the scalings divide by `0`, which Lean
evaluates to `0`; this never enters a limit).
-/

/-- The scaled primitive data of one network, a point of
`ℝᴶ × Dᴶ × Dᴶ × D^{J²} × (ℝ^{2J})^∞` (paths as functions of `t`). -/
abbrev PrimTuple (J : ℕ) : Type :=
  (Fin J → ℝ) × (ℝ → Fin J → ℝ) × (ℝ → Fin J → ℝ) × (ℝ → Fin J → Fin J → ℝ) ×
    (Fin J → ℕ → ℝ × ℝ)

/-- The left-hand sides of (4.1)–(4.5) for network `n`:
`n^{-1/2} Zⁿ(0)`, `n^{-1/2}[Aⁿ(nt) − λⁿnt]`, `n^{-1/2}[Sⁿ(nt) − μⁿnt]`,
`n^{-1/2}[R_{kj}(⌊nt⌋) − P_{kj}nt]` and `(u_k^{j,n}/n, d_k^{j,n}/√n)`. The three families of
paths live on `t ≥ 0` and are extended by `0` to `t < 0`. -/
noncomputable def scaledPrimitives {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (lamn mun : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ) (n : ℕ) : PrimTuple J :=
  (fun j => (N.Z0 j : ℝ) / Real.sqrt n,
   fun t j => if t < 0 then 0 else ((N.A (n * t) j : ℝ) - lamn j * n * t) / Real.sqrt n,
   fun t j => if t < 0 then 0 else ((N.S (n * t) j : ℝ) - mun j * n * t) / Real.sqrt n,
   fun t k j => if t < 0 then 0 else
     ((routingCount χ k j ⌊(n : ℝ) * t⌋₊ : ℝ) - P k j * n * t) / Real.sqrt n,
   fun j k => (N.up j k / n, N.down j k / Real.sqrt n))

/-- The limit primitive data: `Ẑ(0)`, `Â`, `Ŝ`, `R̂` (with `R̂ t k j = R̂_{kj}(t)`), and the limit
up and down durations `(u_kʲ, d_kʲ)` (indexed from `0`, as in `Interruptions`). -/
structure LimitData (J : ℕ) where
  Z0 : Fin J → ℝ
  A : ℝ → Fin J → ℝ
  S : ℝ → Fin J → ℝ
  R : ℝ → Fin J → Fin J → ℝ
  up : Fin J → ℕ → ℝ
  down : Fin J → ℕ → ℝ

/-- The right-hand sides of (4.1)–(4.5) as a point of `PrimTuple J` (paths extended by `0` to
`t < 0`, as in `scaledPrimitives`). -/
noncomputable def LimitData.toPrim {J : ℕ} (L : LimitData J) : PrimTuple J :=
  (L.Z0, fun t => if t < 0 then 0 else L.A t, fun t => if t < 0 then 0 else L.S t,
    fun t => if t < 0 then 0 else L.R t, fun j k => (L.up j k, L.down j k))

/-- The mode of convergence of (4.18)–(4.22): the initial vector converges, the three families of
paths converge uniformly on compact subsets of `[0, ∞)`, and the duration sequences converge
coordinatewise (the product topology of `(ℝ^{2J})^∞`). -/
def PrimConv {J : ℕ} (w : ℕ → PrimTuple J) (w' : PrimTuple J) : Prop :=
  Tendsto (fun n => (w n).1) atTop (𝓝 w'.1) ∧
  UocTendsto (fun n => (w n).2.1) w'.2.1 ∧
  UocTendsto (fun n => (w n).2.2.1) w'.2.2.1 ∧
  UocTendsto (fun n => (w n).2.2.2.1) w'.2.2.2.1 ∧
  Tendsto (fun n => (w n).2.2.2.2) atTop (𝓝 w'.2.2.2.2)

/-- (4.9) `N̂ⱼ(t) = sup{m ≥ 0 : Σ_{k=1}^{m} u_kʲ ≤ t}`, as a natural number (`sSup` in `ℕ`; the
set is bounded when `Σ_k u_kʲ = ∞`, which is assumed wherever this is used; for `t < 0` the set is
empty and the value is `0`). -/
noncomputable def countHat {J : ℕ} (u : Fin J → ℕ → ℝ) (j : Fin J) (t : ℝ) : ℕ :=
  sSup {m : ℕ | ∑ k ∈ Finset.range m, u j k ≤ t}

/-- (4.9) `D̂ⱼ(t) = Σ_{k=1}^{N̂ⱼ(t)} d_kʲ`, the limit cumulative down-time process. -/
noncomputable def downHat {J : ℕ} (u d : Fin J → ℕ → ℝ) (t : ℝ) : Fin J → ℝ :=
  fun j => ∑ k ∈ Finset.range (countHat u j t), d j k

/-- (4.10) `D̂ⱼⁿ(t) = n^{-1/2} Dⱼⁿ(nt)`. -/
noncomputable def downScaled {J : ℕ} (I : Interruptions J) (n : ℕ) (t : ℝ) : Fin J → ℝ :=
  fun j => I.downTime j (n * t) / Real.sqrt n

/-- (4.11), for one sample path: no two distinct coordinates of `x` jump at the same time `t > 0`. -/
def NoCommonJumps {J : ℕ} (x : ℝ → Fin J → ℝ) : Prop :=
  ∀ i j : Fin J, i ≠ j → ∀ t : ℝ, 0 < t →
    ContinuousAt (fun s => x s i) t ∨ ContinuousAt (fun s => x s j) t

/-- (4.6)–(4.8): `√n(λⁿ − λ) → c_λ` with `λ ≥ 0`; `√n(μⁿ − μ) → c_μ` with `μ > 0`;
`λ = [I − Pᵗ]μ` with `P` substochastic and `Pᵏ → 0`. -/
def ParamHyp {J : ℕ} (lamn mun : ℕ → Fin J → ℝ) (lam mu clam cmu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.sqrt n • (lamn n - lam)) atTop (𝓝 clam) ∧ (∀ j, 0 ≤ lam j) ∧
  Tendsto (fun n : ℕ => Real.sqrt n • (mun n - mu)) atTop (𝓝 cmu) ∧ (∀ j, 0 < mu j) ∧
  lam = (1 - P.transpose) *ᵥ mu ∧ IsTransientSubstochastic P

/-- The assumptions of Section 4(A) on the limit, and (4.11), for one sample path: `Â`, `Ŝ`, `R̂`
are continuous on `[0, ∞)`, `Σ_{k=1}^{m} u_kʲ → ∞` as `m → ∞` for each `j`, and `D̂` of (4.9)
has no common discontinuities. -/
def LimitRegular {J : ℕ} (L : LimitData J) : Prop :=
  ContinuousOn L.A (Set.Ici 0) ∧ ContinuousOn L.S (Set.Ici 0) ∧ ContinuousOn L.R (Set.Ici 0) ∧
  (∀ j, Tendsto (fun m => ∑ k ∈ Finset.range m, L.up j k) atTop atTop) ∧
  NoCommonJumps (downHat L.up L.down)

/-- (4.15) `ξ̂ⱼ(t) = Âⱼ(t) + Σₖ [R̂_{kj}(μₖt) + P_{kj}Ŝₖ(t)] − Ŝⱼ(t)`. -/
noncomputable def xiHat {J : ℕ} (L : LimitData J) (mu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (t : ℝ) : Fin J → ℝ :=
  fun j => L.A t j + ∑ k, (L.R (mu k * t) k j + P k j * L.S t k) - L.S t j

/-- (4.16) `η̂(t) = (c_λ − [I − Pᵗ]c_μ) t + [I − Pᵗ] diag(μ) D̂(t)`. -/
noncomputable def etaHat {J : ℕ} (L : LimitData J) (mu clam cmu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (t : ℝ) : Fin J → ℝ :=
  t • (clam - (1 - P.transpose) *ᵥ cmu) + (1 - P.transpose) *ᵥ (mu * downHat L.up L.down t)

/-- (4.14) `X̂(t) = Ẑ(0) + ξ̂(t) + η̂(t)`. -/
noncomputable def XHat {J : ℕ} (L : LimitData J) (mu clam cmu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (t : ℝ) : Fin J → ℝ :=
  L.Z0 + xiHat L mu P t + etaHat L mu clam cmu P t

/-- The scaled prelimit processes of (4.10) and (4.12), stacked as a path in `(ℝᴶ)⁴ = ℝ^{4J}`:
`(Ẑⁿ(t), B̂ⁿ(t), Ŷⁿ(t), D̂ⁿ(t))` with `Ẑⁿ(t) = n^{-1/2}Zⁿ(nt)`, `B̂ⁿ(t) = n^{-1/2}[Bⁿ(nt) − nt]`,
`Ŷⁿ(t) = n^{-1/2}Yⁿ(nt)`, `D̂ⁿ(t) = n^{-1/2}Dⁿ(nt)` for `t ≥ 0`, extended by `0` to `t < 0`. -/
noncomputable def jointScaled {J : ℕ} (N : NetworkData J) (Z : ℝ → Fin J → ℤ)
    (B : ℝ → Fin J → ℝ) (n : ℕ) (t : ℝ) : Fin 4 → Fin J → ℝ :=
  if t < 0 then 0 else
    ![fun j => (Z (n * t) j : ℝ) / Real.sqrt n,
      fun j => (B (n * t) j - n * t) / Real.sqrt n,
      fun j => idleTime N B (n * t) j / Real.sqrt n,
      downScaled N.toInterruptions n t]

/-- The limit `(Ẑ(t), B̂(t), Ŷ(t), D̂(t))` in `(ℝᴶ)⁴`, with `B̂ = −D̂ − Ŷ` (4.17) and `D̂` of (4.9),
for given paths `Ẑ`, `Ŷ`, for `t ≥ 0`, extended by `0` to `t < 0`. -/
noncomputable def jointLimit {J : ℕ} (L : LimitData J) (Zh Yh : ℝ → Fin J → ℝ) (t : ℝ) :
    Fin 4 → Fin J → ℝ :=
  if t < 0 then 0 else ![Zh t, -downHat L.up L.down t - Yh t, Yh t, downHat L.up L.down t]

/-- The deterministic ("almost sure") assumptions of the proof of Theorem 4.1 (p. 351) on a
sequence of networks with a fixed routing `χ`: each network satisfies Section 3's standing
assumptions, (4.6)–(4.8) hold, (4.18)–(4.22) hold, and the limit satisfies Section 4(A)'s
regularity and (4.11). -/
def PathwiseHyp {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun : ℕ → Fin J → ℝ) (lam mu clam cmu : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ)
    (L : LimitData J) : Prop :=
  (∀ n, (net n).IsValid χ) ∧ ParamHyp lamn mun lam mu clam cmu P ∧
  PrimConv (fun n => scaledPrimitives χ (net n) (lamn n) (mun n) P n) L.toPrim ∧
  LimitRegular L

/-- The primitive data of the `n`th network are random: every coordinate of `Zⁿ(0)`, `Aⁿ(t)`,
`Sⁿ(t)` (`t ≥ 0`), `u_k^{j,n}`, `d_k^{j,n}` and of the routing indicators is a random variable. -/
def IsRandomNetwork {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (χ : Ω → Fin J → Fin J → ℕ → Bool)
    (net : ℕ → Ω → NetworkData J) : Prop :=
  (∀ k j l, Measurable (fun ω => χ ω k j l)) ∧
  ∀ n, (∀ j, Measurable (fun ω => (net n ω).Z0 j)) ∧
    (∀ t, 0 ≤ t → ∀ j, Measurable (fun ω => (net n ω).A t j)) ∧
    (∀ t, 0 ≤ t → ∀ j, Measurable (fun ω => (net n ω).S t j)) ∧
    (∀ j k, Measurable (fun ω => (net n ω).up j k)) ∧
    (∀ j k, Measurable (fun ω => (net n ω).down j k))

end ChenWhitt93.JumpDiffusion


