-- Prove2me | Definitions.Def_NoisyOWMPC_CoinAlg
-- name    : NoisyOWMPC_CoinAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:43:28.610988+00:00
-- url     : https://prove2.me/theorems/f23b8978-adad-41ce-a7dd-e5f085922503
-- title:
--   Probabilistic polynomial-time algorithms with explicit coins
-- statement:
--   A **probabilistic algorithm** on security parameter $\lambda$ and input string $u$ uses $\mathrm{coins}(\lambda)$ uniform coins $\rho$ and outputs $\mathrm{run}(\lambda,u;\rho)$. It is **PPT** if it uses polynomially many coins and one deterministic machine computes $\mathrm{run}(\lambda,u;\rho)$ from $(1^\lambda,u,\rho)$ in time polynomial in the input length, for every coin string ("with a worst-case bound for every choice of random coins").
--
--   An input-indexed finite reference distribution is **implementable within statistical error $2^{-\lambda}$** if one PPT algorithm, run on $(1^\lambda,\text{input})$, has an output law within statistical distance $2^{-\lambda}$ of the encoded reference law, for every $\lambda$ and input.
--
--   These are the efficiency notions for the sender, the simulators and the samplers ("All samplers are implemented in polynomial time to within statistical error $2^{-\lambda}$").
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §3, p.15; §5 Conventions, p.21; Sampling convention, p.24

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_NoisyOWMPC_wprob

namespace NoisyOWMPC

open LaconicBarrier

/-- A **probabilistic algorithm with explicit coins** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), §3, p.15: "An algorithm's random coins may be displayed after a
semicolon"): on security parameter `λ` and input string `u` it uses `coins λ` uniform coins `ρ`
and outputs `run λ u ρ`. -/
structure CoinAlg where
  /-- the number of coins at security parameter `λ` -/
  coins : ℕ → ℕ
  /-- the output on `(1^λ, u; ρ)` -/
  run : (lam : ℕ) → List Bool → (Fin (coins lam) → Bool) → List Bool

/-- The algorithm is **(uniform) PPT** (§3, p.15: "all algorithms and simulators run in
probabilistic polynomial time (PPT), with a worst-case bound for every choice of random coins"):
polynomially many coins, and one machine of the published model computes `run λ u ρ` from
`(1^λ, u, ρ)` within a polynomial of the input length, for every coin string. -/
def CoinAlg.IsPPT (S : CoinAlg) : Prop :=
  PolyBounded S.coins ∧
  PolyTimeOn (ι := (lam : ℕ) × List Bool × (Fin (S.coins lam) → Bool))
    (fun i => [unary i.1, i.2.1, bits i.2.2]) (fun i => S.run i.1 i.2.1 i.2.2)

/-- An input-indexed finite reference distribution (weights `w λ x` on `Ω λ`, outcomes encoded by
`enc λ x`) is **implementable in polynomial time to within statistical error `2^{−λ}`**
(STOC 2027 submission (manuscript sha256 3a9569fa…), §5 Conventions, p.21: "All samplers are
implemented in polynomial time to within statistical error `2^{−λ}`"; Sampling convention, p.24):
one PPT coin algorithm, run on `(1^λ, inp λ x)`, has an output law within statistical distance
`2^{−λ}` of the encoded reference law, for every `λ` and `x`. -/
def Samplable {I Ω : ℕ → Type} [∀ l, Fintype (Ω l)] (w : ∀ l, I l → Ω l → ℝ)
    (enc : ∀ l, I l → Ω l → List Bool) (inp : ∀ l, I l → List Bool) : Prop :=
  ∃ S : CoinAlg, S.IsPPT ∧ ∀ (lam : ℕ) (x : I lam),
    sdPush (unifW (Fin (S.coins lam) → Bool)) (fun ρ => S.run lam (inp lam x) ρ)
      (w lam x) (enc lam x) ≤ (2 : ℝ) ^ (-(lam : ℤ))

end NoisyOWMPC


