-- Prove2me | Definitions.Def_NoisyOWMPC_IOScheme
-- name    : NoisyOWMPC_IOScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:50:24.995203+00:00
-- url     : https://prove2.me/theorems/1eae0dd2-51e7-4e87-9b5a-29b1bc4942b8
-- title:
--   Indistinguishability obfuscation
-- statement:
--   An **obfuscator** maps, with coins $\rho$, a multi-output circuit $C$ with $n$ inputs to a circuit $\tilde C=i\mathcal O(1^\lambda,C;\rho)$ with the same inputs. It is an **indistinguishability obfuscator** (Definition 3.2) if
--   1. it is uniform PPT, $\tilde C$ has the output length of $C$, and the description of $\tilde C$ has length at most a public bound $\mathrm{len}(\lambda,n,|C|)$, polynomial and computable in polynomial time ("polynomially bounded description");
--   2. *functionality preservation*: for every $\lambda$, every circuit $C$ and every coin string, $\tilde C(u)=C(u)$ for every input $u$;
--   3. *indistinguishability*: for every polynomial-length sequence $(C_{0,\lambda},C_{1,\lambda},z_\lambda)$ of circuits of equal size with equal input and output lengths and $C_{0,\lambda}(u)=C_{1,\lambda}(u)$ for all $u$, and every nonuniform polynomial-size distinguisher $\mathcal A$, there is a negligible $\nu$ with
--   $$\bigl|\Pr[\mathcal A(1^\lambda,z_\lambda,i\mathcal O(C_{0,\lambda}))=1]-\Pr[\mathcal A(1^\lambda,z_\lambda,i\mathcal O(C_{1,\lambda}))=1]\bigr|\le\nu(\lambda).$$
--
--   The hypothesis "iO" of the main theorem is an obfuscator with this property.
--
--   **Formalization Note** Circuits are the published multi-output circuits; the obfuscated circuit is given to $\mathcal A$ by its description. Functionality preservation holds for every coin string ("with probability one over the obfuscator's coins"). The public length bound is what obfuscations are padded to for transmission (§5 Conventions, p.21: "padded to a fixed public length").
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 3.2, p.16

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_NoisyOWMPC_CompClose

namespace NoisyOWMPC

open KarpLiptonOM LaconicBarrier

/-- The syntax of an **obfuscator for multi-output circuits** (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), Definition 3.2, p.16: "`iO(1^λ, C) → C̃`: On `C ∈ C_λ`,
the uniform PPT algorithm returns a circuit with the same input and output domains"):
`obf λ n s C ρ` is the obfuscation, under coins `ρ ∈ {0,1}^{coins λ n s}`, of a circuit `C` with
`n` inputs and size `s`, a circuit with the same `n` inputs.

**Formalization Note** Circuits are the published multi-output circuits `LaconicBarrier.MCircuit`.
The size `s` is an explicit argument so that the number of coins depends only on `(λ, n, s)`;
every clause of `IOScheme.IsIO` uses `s = C.size`. The field `len` is a public bound on the length
of the obfuscated description ("polynomially bounded description"), used to pad obfuscations "to a
fixed public length for transmission" (§5 Conventions, p.21); every obfuscator with polynomially
bounded descriptions has such a bound. -/
structure IOScheme where
  /-- the number of coins at `(λ, n, s)` -/
  coins : ℕ → ℕ → ℕ → ℕ
  /-- the obfuscator -/
  obf : (lam n s : ℕ) → MCircuit n → (Fin (coins lam n s) → Bool) → MCircuit n
  /-- the public bound on the description length of an obfuscation at `(λ, n, s)` -/
  len : ℕ → ℕ → ℕ → ℕ

/-- `O` is an **indistinguishability obfuscator** (STOC 2027 submission (manuscript sha256
3a9569fa…), Definition 3.2, p.16):
1. *syntax*: `O` is uniform PPT — polynomially many coins and one machine computing the
   description of `C̃` from `(1^λ, C, ρ)` in polynomial time — and `C̃` has the output length of `C`;
   the description of `C̃` has length at most the public bound `len(λ, n, |C|)`, a polynomial
   computed from `(1^λ, 1^n, 1^{|C|})` in polynomial time;
2. *functionality preservation*: for every `λ`, every circuit `C` and **every** coin string,
   `C̃(u) = C(u)` for every input `u` ("with probability one over the obfuscator's coins");
3. *indistinguishability*: for every polynomial-length sequence `(C_{0,λ}, C_{1,λ}, z_λ)` of
   circuits of equal size with the same input and output lengths and `C_{0,λ}(u) = C_{1,λ}(u)` for
   every input `u`, and every nonuniform polynomial-size distinguisher `A`, there is a negligible
   `ν` with `|Pr[A(1^λ, z_λ, iO(1^λ, C_{0,λ})) = 1] − Pr[A(1^λ, z_λ, iO(1^λ, C_{1,λ})) = 1]| ≤ ν(λ)`.

**Formalization Note** The obfuscated circuit is given to `A` by its published description
`MCircuit.code`, after `1^λ` and `z_λ` (tuple encoding `tup`). Functionality preservation is
required for every circuit (iO for polynomial-size circuits, run in time polynomial in `λ` and the
input description). -/
def IOScheme.IsIO (O : IOScheme) : Prop :=
  (∃ c : ℕ, ∀ lam n s, O.coins lam n s ≤ (lam + n + s + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (C : MCircuit n) × (Fin (O.coins lam n C.size) → Bool))
    (fun i => [unary i.1, i.2.2.1.code, bits i.2.2.2])
    (fun i => (O.obf i.1 i.2.1 i.2.2.1.size i.2.2.1 i.2.2.2).code) ∧
  (∀ (lam n : ℕ) (C : MCircuit n) (ρ : Fin (O.coins lam n C.size) → Bool),
    (O.obf lam n C.size C ρ).outs.length = C.outs.length) ∧
  (∃ c : ℕ, ∀ lam n s, O.len lam n s ≤ (lam + n + s + 2) ^ c) ∧
  PolyTimeOn (ι := ℕ × ℕ × ℕ) (fun z => [unary z.1, unary z.2.1, unary z.2.2])
    (fun z => binW (Nat.size (O.len z.1 z.2.1 z.2.2)) (O.len z.1 z.2.1 z.2.2)) ∧
  (∀ (lam n : ℕ) (C : MCircuit n) (ρ : Fin (O.coins lam n C.size) → Bool),
    (O.obf lam n C.size C ρ).code.length ≤ O.len lam n C.size) ∧
  (∀ (lam n : ℕ) (C : MCircuit n) (ρ : Fin (O.coins lam n C.size) → Bool) (u : List Bool),
    u.length = n → (O.obf lam n C.size C ρ).eval u = C.eval u) ∧
  ∀ (n : ℕ → ℕ) (C₀ C₁ : ∀ lam, MCircuit (n lam)) (z : ℕ → List Bool),
    PolyBounded n → PolyBounded (fun lam => (C₀ lam).size) →
    PolyBounded (fun lam => (z lam).length) →
    (∀ lam, (C₀ lam).size = (C₁ lam).size) →
    (∀ lam, (C₀ lam).outs.length = (C₁ lam).outs.length) →
    (∀ lam (u : List Bool), u.length = n lam → (C₀ lam).eval u = (C₁ lam).eval u) →
    ∀ A : Distinguisher, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |A.accProb lam (unifW (Fin (O.coins lam (n lam) (C₀ lam).size) → Bool))
          (fun ρ => QAdvFew.PoQOracle.tup
            [unary lam, z lam, (O.obf lam (n lam) (C₀ lam).size (C₀ lam) ρ).code]) -
        A.accProb lam (unifW (Fin (O.coins lam (n lam) (C₁ lam).size) → Bool))
          (fun ρ => QAdvFew.PoQOracle.tup
            [unary lam, z lam, (O.obf lam (n lam) (C₁ lam).size (C₁ lam) ρ).code])| ≤ ν lam

end NoisyOWMPC


