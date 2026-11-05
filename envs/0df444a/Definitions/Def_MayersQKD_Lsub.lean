-- Prove2me | Definitions.Def_MayersQKD_Lsub
-- name    : MayersQKD_Lsub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:41.081086+00:00
-- url     : https://prove2.me/theorems/1e5df4ac-c966-4074-a561-eb94c5f9e5fb
-- title:
--   The subspaces $L_j[E,\tau]$ and the projections $P_j[E,\tau]$
-- statement:
--   Fix Bob's bases $\hat\theta$, his outcome $\hat w$ and a set of positions $E$. For a threshold $\tau$, $L_1[E,\tau]$ is the span of the states $|\psi_{\alpha,\hat\theta}\rangle$ with $d_E(\alpha,\hat w)\le\tau$ and $L_0[E,\tau]$ is the span of those with $d_E(\alpha,\hat w)>\tau$. $P_j[E,\tau]$ is the orthogonal projection on $L_j[E,\tau]$, and $P_0=P_0[E_c,\epsilon n]$.
--
--   These split the photon space according to how far Bob's basis string lies from $\hat w$ on $E$. The small distance property says that the part in $L_0$ is invisible to Bob's final operation.
--
--   **Formalization Note** The page prints $d_E(\alpha,z)$ in the definition of $L_0$; this is $d_E(\alpha,\hat w)$. If the rule stops there is no $E_c$, and $\emptyset$ stands for it: for $\epsilon\ge0$ this makes $P_0=0$.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §7, p.9

import Mathlib
import Definitions.Def_MayersBC_bb84State
import Definitions.Def_MayersQKD_Bits
import Definitions.Def_MayersQKD_T0
import Definitions.Def_MayersQKD_Attack

namespace MayersQKD

open MayersBC

variable {n r m : ℕ}

/-- Mayers, arXiv:quant-ph/9606003v1, §7, p.9: `L₁[E, τ]` (`j = true`) is the span of the states
`|ψ_{α,θ̂}⟩` with `d_E(α, ŵ) ≤ τ`, and `L₀[E, τ]` (`j = false`) the span of those with
`d_E(α, ŵ) > τ`.

**Formalization Note.** The page prints `d_E(α, z)` in `L₀`; this is `d_E(α, ŵ)`. The paper writes
`τ = εn`. -/
noncomputable def Lsub (j : Bool) (θhat : Bases n) (what : Bits n) (E : Finset (Fin n)) (τ : ℝ) :
    Submodule ℂ (Photons n) :=
  Submodule.span ℂ {φ | ∃ α : Bits n, φ = bb84State θhat α ∧
    (if j then (posDist E α what : ℝ) ≤ τ else τ < (posDist E α what : ℝ))}

/-- Mayers, arXiv:quant-ph/9606003v1, §7, p.9: `P_j[E, τ]`, the orthogonal projection on
`L_j[E, τ]`. -/
noncomputable def proj (j : Bool) (θhat : Bases n) (what : Bits n) (E : Finset (Fin n)) (τ : ℝ) :
    Photons n →ₗ[ℂ] Photons n :=
  ((Lsub j θhat what E τ).starProjection : Photons n →L[ℂ] Photons n)

/-- Mayers, arXiv:quant-ph/9606003v1, §7, p.9: the set `E_c` for a given seed, `ŵ`, `R`, `θ`, `c`.

**Formalization Note.** If the rule stops, no `E_c` exists and this is `∅`. Then `d_∅ = 0`, so for
`ε ≥ 0` the projection `P₀` is `0` and the bad events below are empty, matching that nothing is
announced. -/
def EcOf (A : Attack n r m) (s : A.Seed) (what : Bits n) (R : Finset (Fin n)) (θ : Bases n)
    (c : Bool) : Finset (Fin n) :=
  match A.sel s what R θ with
  | some E => if c then E.2 else E.1
  | none => ∅

/-- Mayers, arXiv:quant-ph/9606003v1, §7, p.9: `P₀ = P₀[E_c, εn]`. -/
noncomputable def P0 (A : Attack n r m) (ε : ℝ) (s : A.Seed) (what : Bits n) (R : Finset (Fin n))
    (θ : Bases n) (c : Bool) : Photons n →ₗ[ℂ] Photons n :=
  proj false (A.commit s) what (EcOf A s what R θ c) (ε * n)

end MayersQKD


