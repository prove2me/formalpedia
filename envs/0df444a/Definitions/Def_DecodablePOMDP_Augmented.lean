-- Prove2me | Definitions.Def_DecodablePOMDP_Augmented
-- name    : DecodablePOMDP_Augmented
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:59.889609+00:00
-- url     : https://prove2.me/theorems/7175cb9d-82a8-45df-b6eb-76338ab94e08
-- title:
--   Decoders, decoding probability $d_{h,s}$ and the augmented POMDP $\widehat{\mathcal P}$
-- statement:
--   A **decoder family** assigns to each $h\in[2:H]$ a channel $D_h$ from $\mathcal O$ to $\mathcal S$. Its **decoding probability** is
--
--   $$d_{h,s}=\sum_y K_h(y\mid s)\,D_h(s\mid y),$$
--
--   and it is a **$\rho$-decoder family** if $d_{h,s}\ge\rho$ for all $h\in[2:H]$ and $s$.
--
--   The **augmented POMDP** $\widehat{\mathcal P}$ has the states, actions, horizon, initial law and transitions of $\mathcal P$, the observation $Z_h=(Y_h,\widehat X_h)\in\mathcal O\times\mathcal S$ with channel
--
--   $$J_h((y,\hat s)\mid s)=K_h(y\mid s)\,D_h(\hat s\mid y),\tag{3}$$
--
--   and the reward $r_h(y)$ for $z=(y,\hat s)$. The extra coordinate is the decoder's guess of the state.
--
--   **Formalization Note** The decoders are any stochastic matrices; statements that need $d_{h,s}\ge\rho$ assume it.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §3, pp.6–7, (3); App. A.2, p.14 ($d_{h,s}$)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_DecodablePOMDP_POMDP

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **Decoder family** (§3, p.6): `D h y s = D_h(s | y)`, with `D_h(· | y)` a probability vector
on `S` for every `h ∈ [2 : H]` and `y ∈ O`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §3, p.6: "for each observation channel
Kh ∈ R^{O×S}, there is an optimal decoder Dh ∈ R^{S×O}". -/
def IsDecoderFamily {S A O : Type} [Fintype S] (P : POMDP S A O) (D : ℕ → O → S → ℝ) : Prop :=
  ∀ h, 2 ≤ h → h ≤ P.H → ∀ y, IsDist (D h y)

/-- **Decoding success probability** `d_{h,s} := Σ_y K_h(y | s) D_h(s | y)` (A.2, p.14).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.2, p.14: "Recall that
dh,s := Σ_y Kh(y|s)Dh(s|y)". -/
def decodeProb {S A O : Type} [Fintype O] (P : POMDP S A O) (D : ℕ → O → S → ℝ) (h : ℕ) (s : S) :
    ℝ :=
  ∑ y, P.K h s y * D h y s

/-- **ρ-decoder family** (§3, p.6): a decoder family with `(D_h K_h)_{s,s} = d_{h,s} ≥ ρ` for every
state `s` and every `h ∈ [2 : H]`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §3, p.6: "(DhKh)s,s ≥ ρ uniformly for every
state s and time h".

**Formalization Note.** The decoders need not be optimal; every statement that uses this
predicate holds for any decoders with success probability at least `ρ`. -/
def IsRhoDecoderFamily {S A O : Type} [Fintype S] [Fintype O] (P : POMDP S A O)
    (D : ℕ → O → S → ℝ) (ρ : ℝ) : Prop :=
  IsDecoderFamily P D ∧ ∀ h, 2 ≤ h → h ≤ P.H → ∀ s, ρ ≤ decodeProb P D h s

/-- **Augmented POMDP** `P̂` (§3, p.7, (3)): same horizon, states, actions, initial law and
transitions as `P`; observation `Z_h = (Y_h, X̂_h) ∈ O × S` with channel
`J_h((y, ŝ) | s) := K_h(y | s) D_h(ŝ | y)`; reward `r_h(y)` for `z = (y, ŝ)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §3, pp.6–7: "after we receive the observation
Yh = y, we pass it through the decoder and obtain X̂h ∼ Dh(·|y). We define the augmented observation
to be Zh := (Yh, X̂h) with observation alphabet Z := O × S. … Jh((y, ŝ)|s) := Kh(y|s)Dh(ŝ|y). (3)" and
p.8: "The reward for an observation Zh = (Yh, X̂h) is the same reward as in P̂, namely the original
reward associated with Yh". -/
def augmented {S A O : Type} (P : POMDP S A O) (D : ℕ → O → S → ℝ) : POMDP S A (O × S) where
  H := P.H
  μ₁ := P.μ₁
  T := P.T
  K h s z := P.K h s z.1 * D h z.1 z.2
  r h z := P.r h z.1

end DecodablePOMDP


