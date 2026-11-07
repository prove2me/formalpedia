-- Prove2me | Definitions.Def_LaconicBarrier_IOScheme
-- name    : LaconicBarrier_IOScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:50.448665+00:00
-- url     : https://prove2.me/theorems/7c5e68eb-639d-44af-bac0-6a264254c3b0
-- title:
--   Indistinguishability obfuscation for circuits
-- statement:
--   An **obfuscator** is a probabilistic algorithm $i\mathcal O$ that takes $1^\lambda$ and a circuit $C$ with $n$ inputs and outputs a circuit $\widetilde C$ with $n$ inputs. It is an indistinguishability obfuscator, as far as the lower bound uses it, if
--
--   1. it runs in probabilistic polynomial time (on the description of $C$);
--   2. **correctness**: there is a negligible $\kappa$ such that for all $\lambda$, all circuits $C$ and all inputs $u$,
--   $$
--   \Pr\bigl[\widetilde C(u) = C(u) : \widetilde C \leftarrow i\mathcal O(1^\lambda, C)\bigr] \ge 1 - \kappa(\lambda).
--   $$
--
--   **Formalization Note** Circuits are the published single-output circuits; the gate count is passed explicitly so that the number of coins depends only on $(\lambda, n, |C|)$. Security is not part of this definition; the security game is the reduction's source family.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.5, p.20, Definition 4.11

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_KarpLiptonOM_circuitCode
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace LaconicBarrier

open KarpLiptonOM

/-- The description of a circuit with `n` inputs and `s` gates: the tuple `(1ⁿ, 1^s, code)`, with the
published fixed circuit encoding `circuitCode`. -/
def circCode {n : ℕ} (C : Circuit n) : List Bool :=
  QAdvFew.PoQOracle.tup [unary n, unary C.gates.length, circuitCode n C.gates.length C]

/-- An **obfuscator for circuits** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower
Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.5, p.20:
"a probabilistic polynomial-time algorithm `iO` that takes as input `1^λ` and a circuit `C`, and
outputs a circuit `C̃`"): `obf λ n s C ρ` is the obfuscation of the circuit `C` with `n` inputs and
`s` gates under coins `ρ`, a circuit with the same inputs.

**Formalization Note** Circuits are the published single-output circuits of `KarpLiptonOM`; the gate
count `s` is passed explicitly so that the number of coins depends only on `(λ, n, s)`, and every
clause of `IOScheme.IsIO` uses `s = |C|`. -/
structure IOScheme where
  /-- the number of coins at `(λ, n, s)` -/
  coins : ℕ → ℕ → ℕ → ℕ
  /-- the obfuscator -/
  obf : (lam n s : ℕ) → Circuit n → (Fin (coins lam n s) → Bool) → Circuit n

/-- `iO` is an **indistinguishability obfuscator**, as far as the paper's lower bound uses it
(Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.11,
p.20):

1. `iO` is probabilistic polynomial-time: polynomially many coins and one machine computing the
   description of `C̃` from `(1^λ, description of C, ρ)` within a polynomial of the input length;
2. **correctness**: there is a negligible `κ` with `Pr[C̃(u) = C(u) : C̃ ← iO(1^λ, C)] ≥ 1 − κ(λ)`
   for all `λ`, all circuits `C` and all inputs `u`; written as: for every `e`, for all large `λ` the
   error is at most `(λ + 2)^{-e}`, uniformly in `C` and `u`.

**Formalization Note** Security is not part of this definition: the lower bound never uses it (the
security game is the source family `IOScheme.source` of the reduction). -/
def IOScheme.IsIO (O : IOScheme) : Prop :=
  (∃ c : ℕ, ∀ lam n s, O.coins lam n s ≤ (lam + n + s + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (C : Circuit n) ×
      (Fin (O.coins lam n C.gates.length) → Bool))
    (fun i => [unary i.1, circCode i.2.2.1, bits i.2.2.2])
    (fun i => circCode (O.obf i.1 i.2.1 i.2.2.1.gates.length i.2.2.1 i.2.2.2)) ∧
  ∀ e : ℕ, ∀ᶠ lam : ℕ in Filter.atTop, ∀ (n : ℕ) (C : Circuit n) (u : List Bool), u.length = n →
    1 - (((lam : ℝ) + 2) ^ e)⁻¹ ≤ coinAvg (O.coins lam n C.gates.length)
      (fun ρ => if (O.obf lam n C.gates.length C ρ).eval u = C.eval u then 1 else 0)

end LaconicBarrier


