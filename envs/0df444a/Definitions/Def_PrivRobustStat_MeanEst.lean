-- Prove2me | Definitions.Def_PrivRobustStat_MeanEst
-- name    : PrivRobustStat_MeanEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:56.399368+00:00
-- url     : https://prove2.me/theorems/9414f3ed-baa5-47e5-95b0-7c9b8ed1a917
-- title:
--   Algorithms 6–8: PrivateLocalize, PrivateWeightedMean, PrivateMeanEstimation
-- statement:
--   1. **Algorithm 6** (PrivateLocalize$(x_{[n]};\varepsilon,\delta)$): $\varepsilon_h=\varepsilon/d$, $\delta_h=\delta/d$, $h=1+\frac2{\varepsilon_h}\log\frac{16}{\delta_h}$; each coordinate is binned into $I_k=[16k,16(k+1))$; every occupied bin count $N_{a,k}$ receives independent $\mathrm{Lap}(2/\varepsilon_h)$ noise; $q_a$ is the midpoint $16k_a+8$ of the noisy-most-populated bin among those with noisy count above $h$ (smallest index on ties), and $0$ if there is none.
--   2. **Algorithm 7** (PrivateWeightedMean$(z_{[n]},w;q,R_0,\eta,\beta)$): $\sigma^2=\eta^2/(256(d+\log(2/\beta)))$, $b=\sum_iw_i(z_i-q)+\xi$, $t=R_0\|w\|_1+\xi_0$ with $\xi\sim\mathcal N(0,\sigma^2I_d)$, $\xi_0\sim\mathcal N(0,\sigma^2)$, and $c=\Pi_{B(q,R_0)}\big(q+b/\max\{\tfrac12,t/R_0\}\big)$.
--   3. **Algorithm 8** after its Line 1 (the localized centre $q$ public): project the data onto $B(q,R_0)$, set $w_0=\frac1n\mathbf 1$, $\Phi_t=(99/100)^t d(2R_0)^{2q}$, $\kappa_t=\Phi_t^{1/q}$, $T=\min\{t:\kappa_t\le\kappa_\star\}$, $\eta_t^2=\kappa_t/(1600q)$ ($t<T$), $\eta_T^2=\alpha\kappa_T$, $\beta_0=\beta/(8(T+1))$; for $t<T$, $c_t$ = Algorithm 7 and $w_{t+1}$ = Algorithm 1 with $(\tfrac{11}{10}\Phi_t,T,\alpha,\beta_0)$ on $M_{i,t}=(z_i-c_t)(z_i-c_t)^\top$; return $c_T$.
--
--   **Formalization Note** The Laplace draws are indexed by (coordinate, first sample index in the bin), which gives one independent draw per occupied bin. The paper uses $q$ for both the centre and the exponent; the centre is renamed. Line 10's arguments are read in Algorithm 1's order $(\Phi,T,\alpha,\beta)$, as the proof of Theorem 4 applies Proposition 1. $T$ is a minimum over $\mathbb N$, equal to the paper's minimum over $\mathbb Z$ under the input condition $\kappa_\star<R_0^2$.
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Algorithm 6, p.31; (38) and Algorithm 7, p.32; Algorithm 8 with its parameters, p.34

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Filter

open MeasureTheory

namespace PrivRobustStat

/-!
# Localization, private weighted means, and the mean estimator: Algorithms 6, 7 and 8

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…): Algorithm 6 (p.31), (38) and Algorithm 7 (p.32),
Algorithm 8 (p.34) with its parameters from p.34 and the proof of Theorem 4 (p.36).

**Formalization Note.**
* Algorithm 6: coordinate `a` of `x_i` lies in bin `k = ⌊[x_i]_a/16⌋`, i.e. `I_k = [16k, 16(k+1))`.
  The Laplace draws `η_{a,k}`, one per occupied bin, are indexed by `(a, i)` where `i` is the
  smallest sample index in bin `k`: the draws of distinct occupied bins are distinct coordinates of
  an i.i.d. `Lap(2/ε_h)` vector (`lapNoise`), so their joint law is the paper's. The chosen bin is
  the smallest `k` among the maximizers of `Ñ_{a,k}` over `L_a` (an `sInf` of a finite nonempty set
  of integers, i.e. its minimum).
* Algorithm 7: `σ := η/(16√(d + log(2/β)))`, so `σ² = η²/(256(d + log(2/β)))`; `ξ_j := σ g_j` and
  `ξ₀ := σ g_none`.
* Algorithm 8 is stated after its Line 1 ("for any fixed q", Lemma 17, p.37): the localized centre
  (written `qc`, since the paper's `q` names both the centre and the exponent `q = 2⌈log₂(2d)⌉ + 1`)
  is a public input. Line 10 is read with Algorithm 1's argument order `(Φ, T, α, β)`, as the proof
  applies Proposition 1 (p.36). `T := min{t : κ_t ≤ κ⋆}` is taken over `ℕ`; for `κ⋆ < κ₀`, which
  Algorithm 8's input condition `κ⋆ < R₀²` gives, it equals the paper's minimum over `ℤ`.
* The Gaussian draws of Algorithm 8 are indexed by the round `t` and then by Algorithm 7's draws
  (`inl`) or Algorithm 1's draws (`inr`); the sketch dimension of every filtering call is
  `r = ⌈C log((n + d)/β₀)⌉` with the constant `C` as a parameter.
-/

open Classical

/-- The i.i.d. Laplace vector `(η_{a,i})_{a ∈ [d], i ∈ [n]}`, each `Lap(b)` (p.10). -/
noncomputable def lapNoise (d n : ℕ) (b : ℝ) : Measure (Fin d × Fin n → ℝ) :=
  Measure.pi fun _ : Fin d × Fin n => PrivLearn.Generic.laplace b

/-- The coordinate `q_a` of Algorithm 6 (Lines 4–13) for coordinate `a`, with threshold `h` and
Laplace draws `η`. -/
noncomputable def localizeCoord {d n : ℕ} (x : Fin n → Vec d) (h : ℝ) (η : Fin d × Fin n → ℝ)
    (a : Fin d) : ℝ :=
  let kb : Fin n → ℤ := fun i => ⌊x i a / 16⌋
  let N : ℤ → ℕ := fun k => (Finset.univ.filter fun i => kb i = k).card
  let Nt : Fin n → ℝ := fun i => (N (kb i) : ℝ) + η (a, i)
  let L := Finset.univ.filter fun i => (∀ j, kb j = kb i → i ≤ j) ∧ h < Nt i
  if hL : L.Nonempty then
    let m := L.sup' hL Nt
    16 * (((sInf (((L.filter fun i => Nt i = m).image kb : Finset ℤ) : Set ℤ)) : ℤ) : ℝ) + 8
  else 0

/-- Algorithm 6, `PrivateLocalize(x[n]; ε, δ)` (p.31): `ε_h := ε/d`, `δ_h := δ/d`,
`h := 1 + (2/ε_h) log(16/δ_h)`, Laplace noise `Lap(2/ε_h)` on every occupied bin, and `q_a` the
midpoint of the most populated noisy bin above the threshold (`0` if there is none). -/
noncomputable def alg6 {d n : ℕ} (x : Fin n → Vec d) (ε δ : ℝ) (η : Fin d × Fin n → ℝ) : Vec d :=
  WithLp.toLp 2 fun a =>
    localizeCoord x (1 + (2 / (ε / d)) * Real.log (16 / (δ / d))) η a

/-- The Laplace scale `2/ε_h = 2d/ε` of Algorithm 6, Line 6. -/
noncomputable def alg6Scale (d : ℕ) (ε : ℝ) : ℝ := 2 / (ε / d)

/-- Algorithm 7, `PrivateWeightedMean(z[n], w; q, R₀, η, β)` (p.32), with its Gaussian draws `g`. -/
noncomputable def alg7 {d n : ℕ} (z : Fin n → Vec d) (w : Fin n → ℝ) (q : Vec d) (R0 η β : ℝ)
    (g : Option (Fin d) → ℝ) : Vec d :=
  let σ := η / (16 * Real.sqrt ((d : ℝ) + Real.log (2 / β)))
  let ξ : Vec d := WithLp.toLp 2 fun a => σ * g (some a)
  let b := ∑ i, w i • (z i - q) + ξ
  let t := R0 * l1 w + σ * g none
  projBall q R0 (q + (max (1 / 2) (t / R0))⁻¹ • b)

/-- `Φ₀ := d(2R₀)^{2q}` (Algorithm 8, Line 3). -/
noncomputable def phi0 (d : ℕ) (R0 : ℝ) : ℝ := d * (2 * R0) ^ (2 * qExp d)

/-- `Φ_t := (99/100)^t Φ₀` (Algorithm 8, Line 5). -/
noncomputable def phiT (d : ℕ) (R0 : ℝ) (t : ℕ) : ℝ := (99 / 100 : ℝ) ^ t * phi0 d R0

/-- `κ_t := Φ_t^{1/q}` (Algorithm 8, Line 5). -/
noncomputable def kappaT (d : ℕ) (R0 : ℝ) (t : ℕ) : ℝ := kappaOf d (phiT d R0 t)

/-- `T := min{t : κ_t ≤ κ⋆}` (Algorithm 8, Line 4). -/
noncomputable def roundsT (d : ℕ) (R0 κstar : ℝ) : ℕ := sInf {t : ℕ | kappaT d R0 t ≤ κstar}

/-- `η_t := (κ_t/(1600q))^{1/2}` for `t < T` and `η_T := (ακ_T)^{1/2}` (Algorithm 8, Line 6). -/
noncomputable def etaT (d : ℕ) (R0 κstar α : ℝ) (t : ℕ) : ℝ :=
  if t < roundsT d R0 κstar then Real.sqrt (kappaT d R0 t / (1600 * qExp d))
  else Real.sqrt (α * kappaT d R0 t)

/-- `β₀ := β/(8(T + 1))` (Algorithm 8, Line 6). -/
noncomputable def beta0 (d : ℕ) (R0 κstar β : ℝ) : ℝ := β / (8 * ((roundsT d R0 κstar : ℝ) + 1))

/-- The sketch dimension of the filtering calls of Algorithm 8. -/
noncomputable def r8 (C : ℝ) (n d : ℕ) (R0 κstar β : ℝ) : ℕ := rDim C n d (beta0 d R0 κstar β)

/-- The Gaussian draws of Algorithm 8 after Line 1: round `t`, then Algorithm 7 (`inl`) or
Algorithm 1 (`inr`). -/
abbrev A8Idx (d r : ℕ) := ℕ × (Option (Fin d) ⊕ A1Idx d r)

/-- The weights `w_t` of Algorithm 8 (Lines 3, 7–10) on the projected data `z`, with the centres
`c_t := PrivateWeightedMean(z[n], w_t; q, R₀, η_t, β₀)` and
`w_{t+1} := PrivateFastCovFilter(M[n],t, w_t; (11/10)Φ_t, T, α, β₀)`, `M_{i,t} = (z_i − c_t)(z_i − c_t)⊤`. -/
noncomputable def alg8weights {d n : ℕ} (C : ℝ) (z : Fin n → Vec d) (qc : Vec d)
    (R0 κstar α β : ℝ) (g : A8Idx d (r8 C n d R0 κstar β) → ℝ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 1 / (n : ℝ)
  | t + 1 =>
      let wt := alg8weights C z qc R0 κstar α β g t
      let ct := alg7 z wt qc R0 (etaT d R0 κstar α t) (beta0 d R0 κstar β)
        (fun a => g (t, Sum.inl a))
      alg1 C z ct wt ((11 / 10 : ℝ) * phiT d R0 t) (roundsT d R0 κstar) α (beta0 d R0 κstar β)
        (fun a => g (t, Sum.inr a))

/-- Algorithm 8, `PrivateMeanEstimation(x[n]; R₀, κ⋆, α, β, ε, δ)` (p.34), after Line 1 with the
public localized centre `qc`: project onto `B(qc, R₀)` (Line 2), run the `T` rounds, and return
`c_T` (Lines 11–12). -/
noncomputable def alg8 {d n : ℕ} (C : ℝ) (x : Fin n → Vec d) (qc : Vec d) (R0 κstar α β : ℝ)
    (g : A8Idx d (r8 C n d R0 κstar β) → ℝ) : Vec d :=
  let z : Fin n → Vec d := fun i => projBall qc R0 (x i)
  let T := roundsT d R0 κstar
  alg7 z (alg8weights C z qc R0 κstar α β g T) qc R0 (etaT d R0 κstar α T) (beta0 d R0 κstar β)
    (fun a => g (T, Sum.inl a))

end PrivRobustStat


