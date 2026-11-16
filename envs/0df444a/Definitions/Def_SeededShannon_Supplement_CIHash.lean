-- Prove2me | Definitions.Def_SeededShannon_Supplement_CIHash
-- name    : SeededShannon_Supplement_CIHash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:38:47.982441+00:00
-- url     : https://prove2.me/theorems/c83166bb-49b5-4eae-82d5-1950a54f385d
-- title:
--   Linearly shifted two-input correlation-intractable hashing, subexponential security (Definition 7.6)
-- statement:
--   A keyed hash family $\Pi_H=(\mathrm{Gen},\mathrm{Hash})$ consists of polynomial-time algorithms with $\mathrm{Gen}(1^\kappa,1^k,1^v)\to K$ and $\mathrm{Hash}(K,\cdot):\{0,1\}^k\to\{0,1\}^v$.
--
--   $\Pi_H$ is **subexponentially secure two-input correlation intractable for linearly shifted $s$-sparse output relations, with constant $c>0$**, if for every polynomial size bound there is $\kappa_0$ such that for all $\kappa\ge\kappa_0$, all $k,v=\mathrm{poly}(\kappa)$, every $\mathbb F_2$-linear $f:\{0,1\}^k\to\{0,1\}^v$, every relation $R_{\mathrm{out}}\subseteq(\{0,1\}^v)^2$ of polynomial size and density $|R_{\mathrm{out}}|/2^{2v}\le 2^{-s(\kappa)}$, and every adversary $\mathcal A$ of size at most $2^{\kappa^c}$,
--   $$\Pr_{K\leftarrow\mathrm{Gen}(1^\kappa,1^k,1^v)}\Big[(x_1,x_2)\leftarrow\mathcal A(K):\ x_1\ne x_2\ \wedge\ \big(\mathrm{Hash}(K,x_1)\oplus f(x_1),\mathrm{Hash}(K,x_2)\oplus f(x_2)\big)\in R_{\mathrm{out}}\Big]\le 2^{-\kappa^c}.$$
--
--   This is the hash that prunes the base list in Construction 7.1 and Theorems 7.10, 7.15.
--
--   **Formalization Note** Relations are given by circuits; "uniformly over $f$, $R_{\mathrm{out}}$ and nonuniform advice" is $\kappa_0$ chosen before them and before the adversary, a deterministic circuit with its advice hard-wired.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 7.6, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_NoisyOWMPC_KeyedFamily
import Definitions.Def_NoisyOWMPC_wprob

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC KarpLiptonOM

/-- A **keyed hash family** `Π_H = (Gen, Hash)` with `Gen(1^κ, 1^k, 1^v) → K` and
`Hash(K, ·) : {0,1}^k → {0,1}^v` (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission (manuscript
sha256 52f4b606…a769709), Definition 7.6, p.50).

**Formalization Note** `gen κ k v ρ` is the key under coins `ρ ∈ {0,1}^{keyCoins κ k v}`; the
lengths `κ, k, v` are passed to `hash` so that its type is `{0,1}^k → {0,1}^v`. -/
structure CIHash where
  /-- coins of `Gen(1^κ, 1^k, 1^v)` -/
  keyCoins : ℕ → ℕ → ℕ → ℕ
  /-- `Gen(1^κ, 1^k, 1^v; ρ) = K` -/
  gen : (κ k v : ℕ) → (Fin (keyCoins κ k v) → Bool) → List Bool
  /-- `Hash(K, x)` -/
  hash : (κ k v : ℕ) → List Bool → (Fin k → Bool) → Fin v → Bool

/-- `Π_H` consists of **polynomial-time algorithms** (Definition 7.6, p.50): polynomially many coins
and one polynomial-time machine each for `Gen` (from `(1^κ, 1^k, 1^v)` and its coins) and for
`Hash` (from `(1^κ, 1^k, 1^v, K, x)` on generated keys). -/
def CIHash.IsEfficient (H : CIHash) : Prop :=
  (∃ c : ℕ, ∀ κ k v, H.keyCoins κ k v ≤ (κ + k + v + 2) ^ c) ∧
  PolyTimeOn (ι := (z : ℕ × ℕ × ℕ) × (Fin (H.keyCoins z.1 z.2.1 z.2.2) → Bool))
    (fun i => [unary i.1.1, unary i.1.2.1, unary i.1.2.2, bits i.2])
    (fun i => H.gen i.1.1 i.1.2.1 i.1.2.2 i.2) ∧
  PolyTimeOn (ι := (z : ℕ × ℕ × ℕ) × (Fin (H.keyCoins z.1 z.2.1 z.2.2) → Bool) × (Fin z.2.1 → Bool))
    (fun i => [unary i.1.1, unary i.1.2.1, unary i.1.2.2, H.gen i.1.1 i.1.2.1 i.1.2.2 i.2.1,
      bits i.2.2])
    (fun i => bits (H.hash i.1.1 i.1.2.1 i.1.2.2 (H.gen i.1.1 i.1.2.1 i.1.2.2 i.2.1) i.2.2))

/-- A map `f : {0,1}^k → {0,1}^v` is **`𝔽₂`-linear**: `f(x ⊕ y) = f(x) ⊕ f(y)`. -/
def IsF2Linear {k v : ℕ} (f : (Fin k → Bool) → Fin v → Bool) : Prop :=
  ∀ x y : Fin k → Bool, f (fun i => xor (x i) (y i)) = fun j => xor (f x j) (f y j)

open Classical in
/-- The number of pairs `(a, b) ∈ ({0,1}^v)²` accepted by the relation circuit `R`, which reads
`a` followed by `b`. -/
noncomputable def relCount {v : ℕ} (R : Circuit (v + v)) : ℕ :=
  (Finset.univ.filter (fun ab : (Fin v → Bool) × (Fin v → Bool) =>
    R.eval (bits ab.1 ++ bits ab.2) = true)).card

/-- **Subexponentially secure two-input correlation intractability for linearly shifted
`s`-sparse output relations, with constant `c`** (Definition 7.6, p.50): `c > 0`, and for every
polynomial size bound `(κ + 2)^d` there is `κ₀` such that for all `κ ≥ κ₀`, all lengths
`k, v ≤ (κ + 2)^d`, every `𝔽₂`-linear `f : {0,1}^k → {0,1}^v`, every relation
`R_out ⊆ ({0,1}^v)²` given by a circuit of size at most `(κ + 2)^d` with density
`|R_out|/2^{2v} ≤ 2^{−s(κ)}`, and every adversary `A` (a circuit with its advice hard-wired) of size
at most `2^{κ^c}`, the probability over `K ← Gen(1^κ, 1^k, 1^v)` that `A(K) = (x₁, x₂)` with
`x₁ ≠ x₂` and `(Hash(K, x₁) ⊕ f(x₁), Hash(K, x₂) ⊕ f(x₂)) ∈ R_out` is at most `2^{−κ^c}`.

**Formalization Note** "`f`, `R_out` of polynomial size and fixed independently of `K`" is the size
bound `(κ + 2)^d` chosen before `κ₀`, with `f`, `R_out` quantified before the key; `f` is any linear
map (a `v × k` matrix). "Uniformly over `f`, `R_out` and nonuniform advice of size at most
`2^{κ^c}`" is `κ₀` chosen before them and before the adversary. The adversary is a deterministic
multi-output circuit fed `K` (`padIn`); its output counts only if it has length `2k`, read as
`x₁` followed by `x₂`. A randomized adversary is matched by its best coins. -/
def CIHash.SubexpCI (H : CIHash) (c : ℝ) (s : ℕ → ℕ) : Prop :=
  0 < c ∧ ∀ d : ℕ, ∃ κ₀ : ℕ, ∀ κ ≥ κ₀, ∀ k v : ℕ, k ≤ (κ + 2) ^ d → v ≤ (κ + 2) ^ d →
    ∀ f : (Fin k → Bool) → Fin v → Bool, IsF2Linear f →
    ∀ R : Circuit (v + v), R.gates.length ≤ (κ + 2) ^ d → relCount R * 2 ^ s κ ≤ 2 ^ (v + v) →
    ∀ (n : ℕ) (A : MCircuit n), (n : ℝ) ≤ (2 : ℝ) ^ ((κ : ℝ) ^ c) →
      (A.size : ℝ) ≤ (2 : ℝ) ^ ((κ : ℝ) ^ c) →
      wprob (unifW (Fin (H.keyCoins κ k v) → Bool)) (fun ρ =>
        let K := H.gen κ k v ρ
        let o := A.eval (padIn n K)
        let x₁ : Fin k → Bool := fun i => o.getD i.val false
        let x₂ : Fin k → Bool := fun i => o.getD (k + i.val) false
        o.length = k + k ∧ x₁ ≠ x₂ ∧
          R.eval (bits (fun j => xor (H.hash κ k v K x₁ j) (f x₁ j)) ++
            bits (fun j => xor (H.hash κ k v K x₂ j) (f x₂ j))) = true) ≤
        (2 : ℝ) ^ (-((κ : ℝ) ^ c))

end SeededShannon.Supplement


