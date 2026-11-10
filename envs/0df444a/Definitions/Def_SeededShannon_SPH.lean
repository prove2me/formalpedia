-- Prove2me | Definitions.Def_SeededShannon_SPH
-- name    : SeededShannon_SPH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:15.754418+00:00
-- url     : https://prove2.me/theorems/95d3f949-207c-4ed2-8aa5-8a83f2479fbf
-- title:
--   Single point binding hash (Definition 3.9)
-- statement:
--   A **single point binding hash** $\Pi_{\mathrm{SPH}}=(\mathrm{Setup},\mathrm{Hash})$ has a randomized $\mathrm{Setup}(1^\lambda,x^*)\to hk$ for $x^*\in\{0,1\}^n$ and a deterministic $\mathrm{Hash}(hk,x)\to h\in\{0,1\}^{\ell_{hash}}$. A key $hk$ is **statistically binding** for $x$ if no $x'\in\{0,1\}^n\setminus\{x\}$ has $\mathrm{Hash}(hk,x)=\mathrm{Hash}(hk,x')$. It is required that:
--
--   1. the algorithms are polynomial-time;
--   2. **input hiding**: for any adversary choosing $n$ and $x_0,x_1\in\{0,1\}^n$, keys $\mathrm{Setup}(1^\lambda,x_0)$ and $\mathrm{Setup}(1^\lambda,x_1)$ are indistinguishable;
--   3. **statistical binding**: there is a negligible $\nu$ such that for all $\lambda$, all $n\le 2^\lambda$ and all $x^*\in\{0,1\}^n$, $hk\leftarrow\mathrm{Setup}(1^\lambda,x^*)$ is binding for $x^*$ except with probability $\nu(\lambda)$;
--   4. **succinctness**: $\ell_{hash}$ is a fixed polynomial in $\lambda$, independent of $n$.
--
--   In Construction 6.1 the hash of the message is the index of the hidden structure; binding at the challenge message isolates it in the correctness proof.
--
--   **Formalization Note** Coins are explicit; $\ell_{hash}$ is a function of $\lambda$ alone. The input-hiding adversary is nonuniform: $n(\lambda),x_0(\lambda),x_1(\lambda)$ are hard-wired into a polynomial-size distinguisher of the key.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 3.9, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_NoisyOWMPC_Distinguisher
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_NoisyOWMPC_wprob

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- A **single point binding hash** `Π_SPH = (Setup, Hash)` (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Definition 3.9, p.19): `Setup(1^λ, x*) → hk` on an
input `x* ∈ {0,1}^n`, and a deterministic `Hash(hk, x) → h ∈ {0,1}^{ℓhash}`.

**Formalization Note** `setup λ n x* r` is the key under coins `r ∈ {0,1}^{coins λ n}`. The hash
length `ℓhash = hlen λ` depends on `λ` only. -/
structure SPH where
  /-- the hash length `ℓhash(λ)` -/
  hlen : ℕ → ℕ
  /-- coins of `Setup(1^λ, x*)` for `x* ∈ {0,1}^n` -/
  coins : ℕ → ℕ → ℕ
  /-- `Setup(1^λ, x*; r) = hk` -/
  setup : (lam n : ℕ) → (Fin n → Bool) → (Fin (coins lam n) → Bool) → List Bool
  /-- `Hash(hk, x)` -/
  hash : List Bool → List Bool → List Bool

/-- `hk` is **statistically binding** for `x ∈ {0,1}^n` (Definition 3.9, p.19): no
`x′ ∈ {0,1}^n \ {x}` has `Hash(hk, x) = Hash(hk, x′)`. -/
def SPH.Binding (H : SPH) (n : ℕ) (hk : List Bool) (x : Fin n → Bool) : Prop :=
  ∀ x' : Fin n → Bool, x' ≠ x → H.hash hk (bits x) ≠ H.hash hk (bits x')

/-- `Π_SPH` is a **single point binding hash** (Definition 3.9, p.19):
1. *efficiency*: polynomially many coins; `Setup` and `Hash` polynomial-time (on honest keys);
2. *syntax*: `Hash(hk, x) ∈ {0,1}^{ℓhash(λ)}`;
3. *input hiding*: for every adversary choosing `n` and `x₀, x₁ ∈ {0,1}^n`, the keys
   `Setup(1^λ, x₀)` and `Setup(1^λ, x₁)` are indistinguishable;
4. *statistical binding*: there is a negligible `ν` such that for all `λ`, all `n ≤ 2^λ` and all
   `x* ∈ {0,1}^n`, `hk ← Setup(1^λ, x*)` is binding for `x*` except with probability `ν(λ)`;
5. *succinctness*: `ℓhash` is a fixed polynomial in `λ`, independent of `n`.

**Formalization Note** The adversary of input hiding is nonuniform and deterministic: its choice is
a sequence `n(λ), x₀(λ), x₁(λ)` of polynomial length, hard-wired into a polynomial-size
distinguisher of the key. Succinctness is `PolyBounded ℓhash` with `ℓhash` a function of `λ`
alone. -/
def SPH.IsSPH (H : SPH) : Prop :=
  (∃ c : ℕ, ∀ lam n, H.coins lam n ≤ (lam + n + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (Fin n → Bool) × (Fin (H.coins lam n) → Bool))
    (fun i => [unary i.1, bits i.2.2.1, bits i.2.2.2])
    (fun i => H.setup i.1 i.2.1 i.2.2.1 i.2.2.2) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (Fin n → Bool) × (Fin (H.coins lam n) → Bool) ×
      (Fin n → Bool))
    (fun i => [unary i.1, H.setup i.1 i.2.1 i.2.2.1 i.2.2.2.1, bits i.2.2.2.2])
    (fun i => H.hash (H.setup i.1 i.2.1 i.2.2.1 i.2.2.2.1) (bits i.2.2.2.2)) ∧
  (∀ (lam n : ℕ) (xs : Fin n → Bool) (r : Fin (H.coins lam n) → Bool) (x : Fin n → Bool),
    (H.hash (H.setup lam n xs r) (bits x)).length = H.hlen lam) ∧
  (∀ (n : ℕ → ℕ) (x₀ x₁ : ∀ lam, Fin (n lam) → Bool), PolyBounded n →
    ∀ D : Distinguisher, D.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |D.accProb lam (unifW (Fin (H.coins lam (n lam)) → Bool))
          (fun r => H.setup lam (n lam) (x₀ lam) r) -
        D.accProb lam (unifW (Fin (H.coins lam (n lam)) → Bool))
          (fun r => H.setup lam (n lam) (x₁ lam) r)| ≤ ν lam) ∧
  (∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam n : ℕ, n ≤ 2 ^ lam → ∀ xs : Fin n → Bool,
    wprob (unifW (Fin (H.coins lam n) → Bool))
      (fun r => ¬ H.Binding n (H.setup lam n xs r) xs) ≤ ν lam) ∧
  PolyBounded H.hlen

end SeededShannon


