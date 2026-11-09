-- Prove2me | Definitions.Def_NoisyOWMPC_NoisePreserving
-- name    : NoisyOWMPC_NoisePreserving
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:53.033999+00:00
-- url     : https://prove2.me/theorems/02809178-d886-4ef5-9706-27376d443ffc
-- title:
--   Noise preservation
-- statement:
--   Let $\mathbf C=(C_1,\dots,C_k)$ be a product broadcast channel with finite input alphabet $\mathcal X$. A deterministic bit $\beta_i:\mathcal X\times\mathcal Y_i\to\{0,1\}$ **witnesses noise preservation for receiver $i$** if
--   1. *nontrivial randomness*: some $u\in\mathcal X$ has
--   $$0<\sum_{y\in\mathcal Y_i}C_i(y\mid u)\,\beta_i(u,y)<1;$$
--   2. *resampling invariance*: for every stochastic map $K:\prod_{j=1}^k\mathcal Y_j\to\mathcal Y_i$ with $\mathbf CK=C_i$ and every $u\in\mathcal X$, $\Pr[\beta_i(u,Z_i)=\beta_i(u,Y_i)]=1$, where $Y_{[k]}\leftarrow\mathbf C(u)$ and $Z_i\leftarrow K(Y_{[k]})$;
--   3. $\beta_i(u,y)=0$ on pairs with $C_i(y\mid u)=0$.
--
--   The channel **satisfies noise preservation** with the bits $\beta$ if every receiver has such a bit (Definition 4.5). This is the paper's characterizing condition for one-way MPC.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 4.5, p.20

import Mathlib
import Definitions.Def_NoisyOWMPC_DMC

namespace NoisyOWMPC

/-- The bit `β_i : X × Y_i → {0,1}` **witnesses noise preservation for receiver `i`** (Ishai, Lu,
Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 4.5, p.20):
1. *nontrivial randomness*: some `u ∈ X` has `0 < ∑_{y ∈ Y_i} C_i(y | u) β_i(u, y) < 1`;
2. *resampling invariance*: for every stochastic map `K : ∏_j Y_j → Y_i` with `C K = C_i` and every
   `u ∈ X`, `Pr[β_i(u, Z_i) = β_i(u, Y_i)] = 1` where `Y_{[k]} ← C(u)` and `Z_i ← K(Y_{[k]})`;
3. the convention "Set `β_i(u, y) = 0` on pairs with `C_i(y | u) = 0`". -/
def NoisePreservingAt {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)]
    (C : ∀ i, DMC X (Y i)) (i : Fin k) (β : X → Y i → Bool) : Prop :=
  (∃ u : X, 0 < ∑ y, (C i).P u y * (if β u y then 1 else 0) ∧
      ∑ y, (C i).P u y * (if β u y then 1 else 0) < 1) ∧
  (∀ K : (∀ j, Y j) → Y i → ℝ, IsStoch K →
    (∀ x z, ∑ y, jointP C x y * K y z = (C i).P x z) →
    ∀ u : X, ∑ y, ∑ z, jointP C u y * K y z * (if β u z = β u (y i) then 1 else 0) = 1) ∧
  (∀ u y, (C i).P u y = 0 → β u y = false)

/-- The product broadcast channel `C` **satisfies noise preservation** with the bits `β`
(Definition 4.5, p.20): every receiver `i` has the bit `β_i` witnessing it. -/
def NoisePreserving {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)]
    (C : ∀ i, DMC X (Y i)) (β : ∀ i, X → Y i → Bool) : Prop :=
  ∀ i, NoisePreservingAt C i (β i)

end NoisyOWMPC


