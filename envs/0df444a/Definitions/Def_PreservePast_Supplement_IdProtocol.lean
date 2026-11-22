-- Prove2me | Definitions.Def_PreservePast_Supplement_IdProtocol
-- name    : PreservePast_Supplement_IdProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:27:54.339105+00:00
-- url     : https://prove2.me/theorems/2291b9d1-b07d-44b6-8653-18ccb680e8c3
-- title:
--   The nearest-of-$k$ experiment on the cube: protocols, success $S$, retained information $I(X;M\mid R)$, fixed width, the full-data optimum $S^\ast$, $F$, $z$ and $h_2^{-1}$
-- statement:
--   The database $X=(X_1,\dots,X_k)$ consists of independent uniform points of $\{-1,1\}^d$. An encoder observes $X$ and independent public coins $R$ and produces a possibly randomized message $M$. Independently, $J$ is uniform on $\{1,\dots,k\}$, and given $X_J$ the query $Z$ has independent coordinates with $\Pr\{Z_i=X_{J,i}\}=\frac{1+\rho}2$. The decoder observes $(M,R,Z)$ and predicts $J$.
--
--   For a protocol we define its **success** $S=\Pr\{\hat J=J\}$, its **retained information** $I(X;M\mid R)$ in bits, and say that it has **width $B$** if the message takes at most $2^B$ values. The **full-data optimum** is
--   $$S^\ast=\mathbb E_X\sum_{z}\max_{j}\tfrac1k P_{X_j}(z),$$
--   the success of the best decoder that also sees $X$, where $P_x$ is the query law given the true string $x$.
--
--   Further, $F(t)=\ln 2-h_{\mathrm{nat}}\!\big(\tfrac{1+t}2\big)$, $\Phi$ is the standard normal distribution function, and with $\ell=\ln k$, $D=dF(\rho)$, $V=d(1-\rho^2)\theta^2$, $\theta=\operatorname{atanh}\rho$,
--   $$z=\frac{D-\ell}{\sqrt V}.$$
--   Finally $h_2^{-1}$ is the inverse of the binary entropy on $[0,\tfrac12]$.
--
--   **Formalization Note** The cube is `Fin d → Bool`. A protocol carries its public-coin space, its private encoder randomness and a standard Borel message alphabet; decoder coins are part of the public coins, as the source remarks. $S^\ast$ is written by its closed form (the maximum-a-posteriori rule). $h_2^{-1}(y)$ is $\inf\{x\in[0,\tfrac12]:h_2(x)\ge y\}$.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Definition 1 and §4.1, p.10 (PDF p.12), eq. (21); §4.2, p.11 (PDF p.13), eqs. (22)–(23); Theorem 18, p.63 (PDF p.65)

import Mathlib
import Definitions.Def_PreservePast_cmiBits

open MeasureTheory
open scoped Classical

namespace PreservePast.Supplement

/-- The query law `P_x` of the nearest-of-k experiment: given the true string `x ∈ {−1,1}^d`, the
coordinates of `Z` are independent with `Pr{Z_i = x_i} = (1+ρ)/2` (Definition 1, p.10). The cube
`{−1,1}^d` is `Fin d → Bool`. -/
noncomputable def bscLaw {d : ℕ} (ρ : ℝ) (x z : Fin d → Bool) : ℝ :=
  ∏ i, if x i = z i then (1 + ρ) / 2 else (1 - ρ) / 2

/-- **A protocol for the nearest-of-k experiment.** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Definition 1, p.10 (PDF p.12): "Let
X = (X₁, …, X_k) consist of independent uniform points of {−1, 1}^d. An encoder observes X and
independent public coins R and produces a possibly randomized message M. Independently, choose J
uniformly from {1, …, k}. Conditional on X_J, generate Z independently across coordinates with
Pr{Z_i = X_{J,i} | X_J} = (1+ρ)/2. The decoder observes (M, R, Z) and predicts J."

**Formalization Note.** `ΩR` carries the public coins `R`, `ΩE` the encoder's private
randomness ("possibly randomized message"), `Msg` is the message alphabet (standard Borel, so
that conditional mutual information is defined). The decoder is a function of `(M, R, Z)`:
"Exposing decoder coins as an independent seed unused by the encoder makes decision regions
deterministic without changing either cost or success" (p.10), i.e. decoder coins are part of
`R`. -/
structure IdProtocol (k d : ℕ) : Type 1 where
  /-- Public coins. -/
  ΩR : Type
  /-- Private encoder randomness. -/
  ΩE : Type
  /-- Message alphabet. -/
  Msg : Type
  [mR : MeasurableSpace ΩR]
  [mE : MeasurableSpace ΩE]
  [mM : MeasurableSpace Msg]
  [sbM : StandardBorelSpace Msg]
  [neM : Nonempty Msg]
  /-- Law of the public coins. -/
  PR : Measure ΩR
  /-- Law of the private randomness. -/
  PE : Measure ΩE
  [probR : IsProbabilityMeasure PR]
  [probE : IsProbabilityMeasure PE]
  /-- The encoder. -/
  enc : (Fin k → Fin d → Bool) → ΩR → ΩE → Msg
  /-- The decoder. -/
  dec : Msg → ΩR → (Fin d → Bool) → Fin k
  enc_meas : ∀ x, Measurable fun q : ΩR × ΩE => enc x q.1 q.2
  dec_meas : ∀ z, Measurable fun q : Msg × ΩR => dec q.1 q.2 z

attribute [instance] IdProtocol.mR IdProtocol.mE IdProtocol.mM IdProtocol.sbM IdProtocol.neM
  IdProtocol.probR IdProtocol.probE

/-- The **success probability** `S = Pr{Ĵ = J}` of a protocol at correlation `ρ`
(Definition 1): the average over the uniform database `x`, the uniform index `j`, the query
`z ∼ P_{x_j}` and the coins. -/
noncomputable def IdProtocol.success {k d : ℕ} (π : IdProtocol k d) (ρ : ℝ) : ℝ :=
  ((2 : ℝ) ^ (k * d))⁻¹ * ∑ x : Fin k → Fin d → Bool, ((k : ℝ))⁻¹ * ∑ j : Fin k,
    ∑ z : Fin d → Bool, bscLaw ρ (x j) z *
      ((π.PR.prod π.PE) {q | π.dec (π.enc x q.1 q.2) q.1 z = j}).toReal

/-- The **retained information** `I(X; M | R)` in bits (p.10: "the least information
I(X; M | R) …, where R denotes independent public coins"): the published conditional mutual
information `cmiBits` on the space of the database, the public coins and the private
randomness. -/
noncomputable def IdProtocol.info {k d : ℕ} (π : IdProtocol k d) : ENNReal :=
  cmiBits ((PMF.uniformOfFintype (Fin k → Fin d → Bool)).toMeasure.prod (π.PR.prod π.PE))
    (fun w => w.1) (fun w => π.enc w.1 w.2.1 w.2.2) (fun w => w.2.1)

/-- The message fits a **fixed register of width `B`**: it takes at most `2^B` values. -/
def IdProtocol.HasWidth {k d : ℕ} (π : IdProtocol k d) (B : ℕ) : Prop :=
  Finite π.Msg ∧ Nat.card π.Msg ≤ 2 ^ B

/-- The **full-data optimum** `S*` (Definition 1: "S* denotes the optimal success when the
decoder also has the full X"): the success of the maximum-a-posteriori rule,
`S* = 𝔼_X Σ_z max_j k⁻¹ P_{X_j}(z)`.

**Formalization Note.** Written by its closed form (the Bayes-optimal decoder given `(X, Z)`
picks a posterior mode, and randomization cannot improve on it). The maximum over `j` is a real
`⨆` over `Fin k`, used for `k ≥ 2`. -/
noncomputable def bayesSuccess (k d : ℕ) (ρ : ℝ) : ℝ :=
  ((2 : ℝ) ^ (k * d))⁻¹ * ∑ x : Fin k → Fin d → Bool, ∑ z : Fin d → Bool,
    ((k : ℝ))⁻¹ * ⨆ j : Fin k, bscLaw ρ (x j) z

/-- `F(t) = ln 2 − h_nat((1+t)/2)`, `0 ≤ t ≤ 1` (22), p.11 (PDF p.13), with `h_nat` the binary
entropy in nats. -/
noncomputable def bscF (t : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 + t) / 2)

/-- The inverse of the binary entropy (in bits) on the branch `[0, 1/2]`: for `0 ≤ y ≤ 1` the
unique `x ∈ [0, 1/2]` with `h₂(x) = y`. Used in Theorem 18 (`b* = [1 − 2h₂⁻¹(1 − R)]/ρ`),
where this branch gives `0 < b* < 1`.

**Formalization Note.** `sInf {x ∈ [0, 1/2] | y ≤ h₂(x)}`; `h₂` is continuous and increasing on
`[0, 1/2]` with `h₂(1/2) = 1`, so for `0 ≤ y ≤ 1` the set is nonempty, bounded below, and its
infimum is the solution. -/
noncomputable def h2inv (y : ℝ) : ℝ := sInf {x : ℝ | 0 ≤ x ∧ x ≤ 1 / 2 ∧ y ≤ h2 x}

/-- The standard normal distribution function `Φ`. -/
noncomputable def stdNormalCdf (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

/-- The window parameter `z = (D − ℓ)/√V` of (23), p.11 (PDF p.13): `ℓ = ln k`, `D = d F(ρ)`,
`V = d(1 − ρ²)θ²`, `θ = atanh ρ = ½ ln((1+ρ)/(1−ρ))` (p.10). Used for `0 < ρ < 1`, `d ≥ 1`,
where `V > 0`. -/
noncomputable def bscZ (k d : ℕ) (ρ : ℝ) : ℝ :=
  (d * bscF ρ - Real.log k) /
    Real.sqrt (d * (1 - ρ ^ 2) * ((1 / 2) * Real.log ((1 + ρ) / (1 - ρ))) ^ 2)

end PreservePast.Supplement


