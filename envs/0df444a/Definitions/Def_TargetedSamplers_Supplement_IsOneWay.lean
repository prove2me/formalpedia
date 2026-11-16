-- Prove2me | Definitions.Def_TargetedSamplers_Supplement_IsOneWay
-- name    : TargetedSamplers_Supplement_IsOneWay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:12:29.551204+00:00
-- url     : https://prove2.me/theorems/5b5680be-6a8b-4685-b754-766ec22928ac
-- title:
--   One-way functions secure against polynomial-size circuits
-- statement:
--   A function $f:\{0,1\}^*\to\{0,1\}^*$ is a **one-way function secure against polynomial-size circuits** if
--
--   1. one deterministic program computes $f(x)$ from $x$ in time polynomial in $|x|$, and
--   2. for every family of Boolean circuits $C_{m,\ell}:\{0,1\}^\ell\to\{0,1\}^m$ whose size is polynomial in $m$, the inversion probability is negligible: for every $e\in\mathbb N$ and all sufficiently large $m$,
--   $$\Pr_{x\in\{0,1\}^m}\big[f\big(C_{m,|f(x)|}(f(x))\big)=f(x)\big]\le m^{-e}.$$
--
--   "One-way functions exist" means that such an $f$ exists. This is the hypothesis of Theorem 5.1, used through the cryptographic pseudorandom generator of Theorem 3.3 (Goldreich–Levin, Håstad–Impagliazzo–Levin–Luby).
--
--   **Formalization Note** The paper names "non-uniformly secure OWFs" (§3) without defining them; this is the standard notion. Circuits are the published `MultAddExt.Multiplicative.Circ` (fan-in-2 AND/OR, NOT, constant wires); size is the number of gates. The inverter may depend on the length of its input, so $f$ need not be length-regular. Polynomial time is $K(|x|+1)^k$ on the base mission's RAM.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), §3, p.19 (pdf p.21) and Theorem 5.1, p.43 (pdf p.45)

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_coinProb
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers.Supplement

/-- `f : {0,1}* → {0,1}*` is a one-way function secure against polynomial-size circuits (Chen,
Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, §3, p.19:
"if non-uniformly secure OWFs exist", Theorem 3.3 "OWFs secure against polynomial-size circuits";
Theorem 5.1, p.43, "Assume that one-way functions exists"):

1. *Easy to compute.* One deterministic program computes `f(x)` from `x` in time polynomial in `|x|`.
2. *Hard to invert.* For every family of Boolean circuits `C_{m,ℓ} : {0,1}^ℓ → {0,1}^m` of polynomial
   size in `m`, and every exponent `e`, for all large `m`,
   `Pr_{x ∈ {0,1}^m}[f(C_{m,|f(x)|}(f(x))) = f(x)] ≤ m^{−e}` (the inverter's success probability is
   negligible).

**Formalization Note** The paper does not define OWFs; this is the standard non-uniform notion it
names. Circuits are the published `MultAddExt.Multiplicative.Circ` (fan-in-2 AND/OR, NOT, constant
wires); their size is the number of gates. The inverter for inputs of length `m` may depend on the
length `ℓ = |f(x)|` of its input, so `f` need not be length-regular. "Polynomial time" is
`K · (|x| + 1)^k` on the base RAM; the output length is then polynomial in `|x|`. -/
def IsOneWay (f : List Bool → List Bool) : Prop :=
  (∃ (P : Program) (K k : ℕ), ∀ x : List Bool,
    P.RunsIn (Tapes.ofInput x) (K * (x.length + 1) ^ k) (some (f x))) ∧
  ∀ (C : (m ℓ : ℕ) → MultAddExt.Multiplicative.Circ ℓ m) (a : ℕ),
    (∀ m ℓ : ℕ, (C m ℓ).numGates ≤ a * (m + 1) ^ a) →
    ∀ e : ℕ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      coinProb m (fun x => f (List.ofFn ((C m (f x).length).eval (toVec (f x)))) = f x) ≤
        (m : ℝ) ^ (-(e : ℝ))

/-- One-way functions secure against polynomial-size circuits exist. -/
def OWFExist : Prop := ∃ f : List Bool → List Bool, IsOneWay f

end TargetedSamplers.Supplement


