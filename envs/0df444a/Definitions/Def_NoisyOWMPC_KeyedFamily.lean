-- Prove2me | Definitions.Def_NoisyOWMPC_KeyedFamily
-- name    : NoisyOWMPC_KeyedFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:50:44.691191+00:00
-- url     : https://prove2.me/theorems/157b71a4-26a8-4733-b193-e19f516fa58c
-- title:
--   Keyed function families, one-wayness, injectivity and hard-core bits
-- statement:
--   A **keyed function family** $F=\{F_{\lambda,\mathrm{pk}}:\{0,1\}^{n(\lambda)}\to\{0,1\}^{\ell(\lambda)}\}$ comes with a PPT key sampler $\mathrm{KeyGen}(1^\lambda)\to\mathrm{pk}\in\{0,1\}^{k(\lambda)}$. Following Definition 3.3:
--   1. *efficiency*: $n,\ell,k$ are polynomially bounded and $\mathrm{KeyGen}$ and $F$ are polynomial time;
--   2. *one-wayness*: for every nonuniform polynomial-size $\mathcal A$ there is a negligible $\nu$ with $\Pr[x'\in\{0,1\}^{n(\lambda)}\text{ and }F_{\lambda,\mathrm{pk}}(x')=F_{\lambda,\mathrm{pk}}(X)]\le\nu(\lambda)$ for $x'\leftarrow\mathcal A(1^\lambda,\mathrm{pk},F_{\lambda,\mathrm{pk}}(X))$;
--   3. *injectivity*: $\varepsilon_{\mathrm{inj}}(\lambda)=\Pr_{\mathrm{pk}}[\exists x\ne x':F_{\lambda,\mathrm{pk}}(x)=F_{\lambda,\mathrm{pk}}(x')]$ is negligible;
--   4. a *randomized hard-core bit* $\mathrm{hcb}_\lambda$ is efficiently computable with $(\mathrm{pk},F(X),R,\mathrm{hcb}(X;R))\approx^c(\mathrm{pk},F(X),R,B)$.
--
--   An **injective one-way function** is an efficient family with one-wayness and injectivity.
--
--   **Formalization Note** Inverters are polynomial-size multi-output circuit families; a randomized inverter is matched by the circuit with its best coins.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 3.3, p.16

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_NoisyOWMPC_CompClose

namespace NoisyOWMPC

open KarpLiptonOM LaconicBarrier

/-- A **keyed function family with a key sampler** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Definition 3.3, p.16: "`F = {F_{λ,pk} : {0,1}^{n(λ)} → {0,1}^{ℓ(λ)}
: pk ∈ {0,1}^{k(λ)}, λ ∈ ℕ}` … with a PPT key sampler `KeyGen(1^λ) → pk ∈ {0,1}^{k(λ)}`"):
`keyGen λ ρ` is the key sampled with coins `ρ ∈ {0,1}^{kgCoins λ}`. -/
structure KeyedFamily where
  /-- the input length `n(λ)` -/
  n : ℕ → ℕ
  /-- the output length `ℓ(λ)` -/
  ℓ : ℕ → ℕ
  /-- the key length `k(λ)` -/
  kl : ℕ → ℕ
  /-- the number of coins of `KeyGen(1^λ)` -/
  kgCoins : ℕ → ℕ
  /-- the key sampler -/
  keyGen : (lam : ℕ) → (Fin (kgCoins lam) → Bool) → Fin (kl lam) → Bool
  /-- the function `F_{λ,pk}` -/
  F : (lam : ℕ) → (Fin (kl lam) → Bool) → (Fin (n lam) → Bool) → Fin (ℓ lam) → Bool

/-- The family is **efficiently computable** with a PPT key sampler and polynomially bounded
lengths `n, ℓ, k` (Definition 3.3, p.16). -/
def KeyedFamily.Efficient (F : KeyedFamily) : Prop :=
  PolyBounded F.n ∧ PolyBounded F.ℓ ∧ PolyBounded F.kl ∧ PolyBounded F.kgCoins ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (F.kgCoins lam) → Bool))
    (fun i => [unary i.1, bits i.2]) (fun i => bits (F.keyGen i.1 i.2)) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (F.kl lam) → Bool) × (Fin (F.n lam) → Bool))
    (fun i => [unary i.1, bits i.2.1, bits i.2.2]) (fun i => bits (F.F i.1 i.2.1 i.2.2))

/-- A **nonuniform algorithm with string output**: one multi-output circuit `A_λ` with `inLen λ`
inputs per security parameter (§3, p.15: "adversaries … may be nonuniform"). -/
structure CircFamily where
  /-- the number of inputs of `A_λ` -/
  inLen : ℕ → ℕ
  /-- the circuit `A_λ` -/
  circ : (lam : ℕ) → MCircuit (inLen lam)

/-- The family has polynomial size: inputs and size at most `(λ + 2)^c`. -/
def CircFamily.IsPoly (A : CircFamily) : Prop :=
  ∃ c : ℕ, ∀ lam, A.inLen lam ≤ (lam + 2) ^ c ∧ (A.circ lam).size ≤ (lam + 2) ^ c

/-- **One-wayness** (Definition 3.3, p.16): for every nonuniform polynomial-size inverter `A`
there is a negligible `ν` with
`Pr[x′ ∈ {0,1}^{n(λ)} and F_{λ,pk}(x′) = F_{λ,pk}(X) : x′ ← A(1^λ, pk, F_{λ,pk}(X))] ≤ ν(λ)`,
for independent `pk ← KeyGen(1^λ)` and uniform `X ∈ {0,1}^{n(λ)}`.

**Formalization Note** The inverter's input `(1^λ, pk, F(X))` is the tuple encoding, fed as
`padIn`; its output string `x′` counts only if it has length `n(λ)`. A randomized inverter is
matched by the circuit with its best coins hard-wired. -/
def KeyedFamily.OneWay (F : KeyedFamily) : Prop :=
  ∀ A : CircFamily, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    wprob (unifW ((Fin (F.kgCoins lam) → Bool) × (Fin (F.n lam) → Bool))) (fun ω =>
      let pk := F.keyGen lam ω.1
      let out := (A.circ lam).eval (padIn (A.inLen lam)
        (QAdvFew.PoQOracle.tup [unary lam, bits pk, bits (F.F lam pk ω.2)]))
      out.length = F.n lam ∧ F.F lam pk (fun j => out.getD j.val false) = F.F lam pk ω.2) ≤ ν lam

/-- **Injectivity** (Definition 3.3, p.16): `ε_inj(λ) = Pr_{pk ← KeyGen(1^λ)}[∃ x ≠ x′ ∈ {0,1}^{n(λ)} :
F_{λ,pk}(x) = F_{λ,pk}(x′)]` is negligible. -/
def KeyedFamily.Injective (F : KeyedFamily) : Prop :=
  Negligible fun lam => wprob (unifW (Fin (F.kgCoins lam) → Bool)) (fun ρ =>
    ∃ x x' : Fin (F.n lam) → Bool, x ≠ x' ∧ F.F lam (F.keyGen lam ρ) x = F.F lam (F.keyGen lam ρ) x')

/-- An **injective one-way function** (Definition 3.3, p.16: "An injective one-way function is a
family satisfying one-wayness and injectivity"), efficiently computable. -/
def KeyedFamily.IsInjOWF (F : KeyedFamily) : Prop := F.Efficient ∧ F.OneWay ∧ F.Injective

/-- A **randomized hard-core bit** `hcb_λ : {0,1}^{n(λ)} × {0,1}^{d(λ)} → {0,1}` of `F`
(Definition 3.3, p.16): `hcb` is efficiently computable and
`(pk, F_{λ,pk}(X), R, hcb_λ(X; R)) ≈^c (pk, F_{λ,pk}(X), R, B)` for independent `pk ← KeyGen(1^λ)`
and uniform `X`, `R`, `B`. -/
def KeyedFamily.IsHardCoreBit (F : KeyedFamily) (d : ℕ → ℕ)
    (hcb : (lam : ℕ) → (Fin (F.n lam) → Bool) → (Fin (d lam) → Bool) → Bool) : Prop :=
  PolyBounded d ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (F.n lam) → Bool) × (Fin (d lam) → Bool))
    (fun i => [unary i.1, bits i.2.1, bits i.2.2]) (fun i => [hcb i.1 i.2.1 i.2.2]) ∧
  CompClose (I := fun _ => Unit)
    (Ω₀ := fun lam => (Fin (F.kgCoins lam) → Bool) × (Fin (F.n lam) → Bool) × (Fin (d lam) → Bool))
    (Ω₁ := fun lam => ((Fin (F.kgCoins lam) → Bool) × (Fin (F.n lam) → Bool) × (Fin (d lam) → Bool))
      × Bool)
    (fun _ _ => unifW _)
    (fun lam _ ω => QAdvFew.PoQOracle.tup [bits (F.keyGen lam ω.1),
      bits (F.F lam (F.keyGen lam ω.1) ω.2.1), bits ω.2.2, [hcb lam ω.2.1 ω.2.2]])
    (fun _ _ => unifW _)
    (fun lam _ ω => QAdvFew.PoQOracle.tup [bits (F.keyGen lam ω.1.1),
      bits (F.F lam (F.keyGen lam ω.1.1) ω.1.2.1), bits ω.1.2.2, [ω.2]])
    (fun _ => 0)

end NoisyOWMPC


