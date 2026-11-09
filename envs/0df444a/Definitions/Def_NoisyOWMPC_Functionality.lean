-- Prove2me | Definitions.Def_NoisyOWMPC_Functionality
-- name    : NoisyOWMPC_Functionality
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:36.588703+00:00
-- url     : https://prove2.me/theorems/1f113f35-8ff6-4332-9a31-247386c7d0c9
-- title:
--   Randomized functionalities given by target circuits
-- statement:
--   A **randomized functionality** for $k$ receivers is given by target functions $f_i:\{0,1\}^{\ell_x}\times\{0,1\}^{r_i}\to\{0,1\}^{\ell_i}$, so that on sender input $x$ receiver $i$ should obtain $f_i(x;\rho_i)$ for independent uniform coins $\rho_i$. It is **polynomial** if $\ell_x$, $r_i$, $\ell_i$ are public polynomial parameters (polynomially bounded and computable from $1^\lambda$ in polynomial time) and each $f_i$ is computed by a circuit of size polynomial in $\lambda$. Write $q_J=\sum_{i\in J}r_i$ and $q=q_{[k]}$.
--
--   This is the functionality of Definition 4.2 in the form fixed by the conventions of §5 ("fix a public deterministic circuit $f_i$ … $\mathcal M=\{0,1\}^{\ell_x}$ and $\mathcal O_i=\{0,1\}^{\ell_i}$").
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §4.2, p.18; §5 Conventions, p.21

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_NoisyOWMPC_Negligible

namespace NoisyOWMPC

open LaconicBarrier

/-- A **randomized functionality given by target circuits** (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), §4.2 Randomized functionalities, p.18, and §5
Conventions, p.21: "For each receiver `i`, fix a public deterministic circuit
`f_i : {0,1}^{ℓ_x} × {0,1}^{r_i} → {0,1}^{ℓ_i}`, where `r_i` may be zero, so that `M = {0,1}^{ℓ_x}`
and `O_i = {0,1}^{ℓ_i}`"): `f λ i x ρ` is `f_i(x; ρ)` at security parameter `λ`. -/
structure Functionality (k : ℕ) where
  /-- the input length `ℓ_x(λ)` -/
  lx : ℕ → ℕ
  /-- the coin length `r_i(λ)` of receiver `i` -/
  r : Fin k → ℕ → ℕ
  /-- the output length `ℓ_i(λ)` of receiver `i` -/
  lo : Fin k → ℕ → ℕ
  /-- the target function `f_i(x; ρ)` -/
  f : (lam : ℕ) → (i : Fin k) → (Fin (lx lam) → Bool) → (Fin (r i lam) → Bool) → Fin (lo i lam) → Bool

/-- The lengths are polynomial in `λ` and each `f_i` is computed by a circuit of size polynomial
in `λ` (§4.2, p.18: "each `f_i` is a public polynomial-size circuit … its input and output lengths
may be any polynomials in `λ`"); the lengths are public polynomial parameters (`PolyParam`). -/
def Functionality.IsPolyCircuit {k : ℕ} (F : Functionality k) : Prop :=
  PolyParam F.lx ∧ (∀ i, PolyParam (F.r i)) ∧ (∀ i, PolyParam (F.lo i)) ∧
  ∃ c : ℕ, ∀ lam i, ∃ Cf : MCircuit (F.lx lam + F.r i lam), Cf.size ≤ (lam + 2) ^ c ∧
    ∀ x ρ, Cf.eval (bits x ++ bits ρ) = bits (F.f lam i x ρ)

/-- `q_J = ∑_{i ∈ J} r_i` (§5 Conventions, p.21); `q = q_{[k]}`. -/
def Functionality.qOf {k : ℕ} (F : Functionality k) (J : Finset (Fin k)) (lam : ℕ) : ℕ :=
  ∑ i ∈ J, F.r i lam

end NoisyOWMPC


