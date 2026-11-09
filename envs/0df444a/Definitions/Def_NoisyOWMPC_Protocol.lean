-- Prove2me | Definitions.Def_NoisyOWMPC_Protocol
-- name    : NoisyOWMPC_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:44.056487+00:00
-- url     : https://prove2.me/theorems/8b264861-03bf-4b3f-9838-3234e72101da
-- title:
--   One-way protocols over a product broadcast channel
-- statement:
--   A **one-way protocol** $\Pi=(S,R_1,\dots,R_k)$ for a functionality $F$ consists of
--   1. the sender $S(1^\lambda,x;r_S)\to(\tau,\hat{\mathbf x})$, which maps $x\in\{0,1\}^{\ell_x}$ and its protocol coins $r_S$ (with an exact finite reference law) to a public message $\tau\in\{0,1\}^L$ and a word $\hat{\mathbf x}\in\mathcal X^N$;
--   2. deterministic receivers $R_i(1^\lambda,\tau,\hat{\mathbf y}_i)\to y_i\in\{0,1\}^{\ell_i}\cup\{\mathsf{fail}\}$.
--
--   In the **real execution** the word is sent once through the product channel, $(\hat{\mathbf y}_1,\dots,\hat{\mathbf y}_k)\leftarrow\mathbf C^N(\hat{\mathbf x})$, and $\tau$ is delivered noiselessly to everyone.
--
--   **Formalization Note** The sender is given by its exact reference coin distribution (p.24); its polynomial-time implementation within $2^{-\lambda}$ is a separate clause (`Protocol.IsEfficient`).
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 4.2, pp.18–19

import Mathlib
import Definitions.Def_NoisyOWMPC_DMC
import Definitions.Def_NoisyOWMPC_Functionality

namespace NoisyOWMPC

/-- A **one-way protocol** `Π = (S, R₁, …, R_k)` over a product broadcast channel for a
functionality `F` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…),
Definition 4.2, pp.18–19):
* `S(1^λ, x; r_S) → (τ, x̂)`: the sender, with protocol coins `r_S` drawn from the finite reference
  distribution `wS λ` on `RS λ`, maps `x ∈ {0,1}^{ℓ_x}` to a public message `τ ∈ {0,1}^L` and a word
  `x̂ ∈ X^N`; `encRS` encodes the coins in the sender's view;
* `R_i(1^λ, τ, ŷ_i) → y_i`: receiver `i` deterministically decodes `τ` and its own noisy
  observation `ŷ_i ∈ Y_i^N`; `none` is `fail`.

**Formalization Note** The sender is given by its exact reference coin distribution (Sampling
convention, p.24: "The distributions above are exact reference distributions"); its polynomial-time
implementation within statistical distance `2^{−λ}` is the separate clause of
`Protocol.IsEfficient`. -/
structure Protocol (k : ℕ) (X : Type) (Y : Fin k → Type) (F : Functionality k) where
  /-- the sender's coin space -/
  RS : ℕ → Type
  [finRS : ∀ lam, Fintype (RS lam)]
  /-- the law of the sender's coins -/
  wS : (lam : ℕ) → RS lam → ℝ
  /-- the encoding of the sender's coins -/
  encRS : (lam : ℕ) → RS lam → List Bool
  /-- the noiseless message length `L` -/
  L : ℕ → ℕ
  /-- the number `N` of noisy channel uses -/
  N : ℕ → ℕ
  /-- the sender -/
  send : (lam : ℕ) → (Fin (F.lx lam) → Bool) → RS lam → (Fin (L lam) → Bool) × (Fin (N lam) → X)
  /-- receiver `i` -/
  recv : (lam : ℕ) → (i : Fin k) → (Fin (L lam) → Bool) → (Fin (N lam) → Y i) →
    Option (Fin (F.lo i lam) → Bool)

attribute [instance] Protocol.finRS

variable {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)] {F : Functionality k}

/-- The **real execution** (Definition 4.2, p.18): the sender's coins `r_S` and the joint channel
output `(ŷ₁, …, ŷ_k) ← Cᴺ(x̂)`, with weight `w_S(r_S) · ∏_p ∏_i C_i(ŷ_i[p] | x̂[p])`. -/
noncomputable def Protocol.realW (P : Protocol k X Y F) (C : ∀ i, DMC X (Y i)) (lam : ℕ)
    (x : Fin (F.lx lam) → Bool) (ω : P.RS lam × (Fin (P.N lam) → ∀ i, Y i)) : ℝ :=
  P.wS lam ω.1 * ∏ p, jointP C ((P.send lam x ω.1).2 p) (ω.2 p)

/-- The decoded output `y_i = R_i(1^λ, τ, ŷ_i)` of receiver `i` in the real execution. -/
def Protocol.out (P : Protocol k X Y F) (lam : ℕ) (x : Fin (F.lx lam) → Bool)
    (ω : P.RS lam × (Fin (P.N lam) → ∀ i, Y i)) (i : Fin k) : Option (Fin (F.lo i lam) → Bool) :=
  P.recv lam i (P.send lam x ω.1).1 (fun p => ω.2 p i)

end NoisyOWMPC


