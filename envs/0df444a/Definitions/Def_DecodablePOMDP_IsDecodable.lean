-- Prove2me | Definitions.Def_DecodablePOMDP_IsDecodable
-- name    : DecodablePOMDP_IsDecodable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:03.754146+00:00
-- url     : https://prove2.me/theorems/f926dab3-ec44-41ca-a381-59e4955431fc
-- title:
--   $\rho$-decodable channels and POMDPs (Definition 3)
-- statement:
--   Let $\rho\in(0,1]$. A channel $K$ from $\mathcal S$ to $\mathcal O$ is **$\rho$-decodable** if there is a decoder channel $D$ from $\mathcal O$ to $\mathcal S$ (each $D(\cdot\mid y)$ a probability vector on $\mathcal S$) such that
--
--   $$\sum_{y\in\mathcal O}K(y\mid s)\,D(s\mid y)\ \ge\ \rho\qquad\text{for every }s\in\mathcal S,$$
--
--   i.e. the cascade $DK$ returns the input state with probability at least $\rho$. A POMDP is **$\rho$-decodable** if all its observation channels $K_h$, $h\in[2:H]$, are $\rho$-decodable.
--
--   This is the paper's structural assumption; it replaces observability and is the only hypothesis of Theorem 1 besides the data.
--
--   **Formalization Note** The range $\rho\in(0,1]$ is part of both predicates; the decoder is any real stochastic matrix.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Definition 3, p.4

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_DecodablePOMDP_POMDP

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **ρ-decodable channel** (Definition 3, p.4). For `ρ ∈ (0, 1]`, a channel `K` from `S` to `O`
(`Kc s y = K(y | s)`) is ρ-decodable if there is a decoder channel `D` from `O` to `S`
(`D y s = D(s | y)`, each `D(· | y)` a probability vector) with
`Σ_y K(y | s) D(s | y) ≥ ρ` for every `s ∈ S`.

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), Definition 3, p.4: "Let ρ ∈ (0, 1]. … We say that K is ρ-decodable if there exists
a decoder channel D from the observation space O to the state space S such that the cascaded
channel DK from S to S satisfies (DK)(s,s) ≥ ρ for every s ∈ S. Equivalently,
Σ_{y∈O} K(y|s)D(s|y) ≥ ρ for all s ∈ S."

**Formalization Note.** The standing range `ρ ∈ (0, 1]` is part of the predicate; the decoder is
any real stochastic matrix. -/
def ChannelDecodable {S O : Type} [Fintype S] [Fintype O] (Kc : S → O → ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∃ D : O → S → ℝ, (∀ y, IsDist (D y)) ∧ ∀ s, ρ ≤ ∑ y, Kc s y * D y s

/-- **ρ-decodable POMDP** (Definition 3, p.4): "A POMDP is said to be ρ-decodable if all its
observation channels are ρ-decodable", i.e. `K_h` is ρ-decodable for every `h ∈ [2 : H]`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Definition 3, p.4.

**Formalization Note.** `ρ ∈ (0, 1]` is required even when `H = 1` (no channels). -/
def IsDecodable {S A O : Type} [Fintype S] [Fintype O] (P : POMDP S A O) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∀ h, 2 ≤ h → h ≤ P.H → ChannelDecodable (P.K h) ρ

end DecodablePOMDP


