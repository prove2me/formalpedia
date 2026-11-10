-- Prove2me | Definitions.Def_SeededShannon_EvObf
-- name    : SeededShannon_EvObf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:13.882284+00:00
-- url     : https://prove2.me/theorems/11b40ca0-97bf-4012-8761-324a6f80323c
-- title:
--   Distributional evasive obfuscator (Definition 5.1)
-- statement:
--   Let $N_{\min}$ be an efficiently computable polynomial and $\{\mathcal F_{\lambda,n}\}_{n\ge N_{\min}(\lambda)}$ a family of functions $\{0,1\}^n\to\{0,1\}$. A **distributional evasive obfuscator** specifies a map from sampling seeds $\sigma$ to functions $f_\sigma\in\mathcal F_{\lambda,n}$ and algorithms running in time $\mathrm{poly}(\lambda,n)$:
--
--   1. $\mathrm{GenProg}(1^\lambda,1^n)\to(\sigma,\tilde P_\sigma)$, a seed and an obfuscation of $f_\sigma$;
--   2. $\mathrm{GenZero}(1^\lambda,1^n)\to\tilde P_0$, an obfuscation of the all-zeros program;
--   3. $\mathrm{Eval}(\tilde P,x)\in\{0,1\}$, deterministic.
--
--   **Correctness**: for every polynomial $P$ there is a negligible $\nu_P$ such that for all $\lambda$ and supported $N_{\min}(\lambda)\le n\le P(\lambda)$, with probability at least $1-\nu_P(\lambda)$, $\mathrm{Eval}(\tilde P_\sigma,x)=f_\sigma(x)$ for all $x$, and with probability at least $1-\nu_P(\lambda)$, $\mathrm{Eval}(\tilde P_0,x)=0$ for all $x$. **Null indistinguishability**: for any adversary choosing $1^n$, the program $\tilde P$ of $\mathrm{GenProg}(1^\lambda,1^n)$ (seed hidden) and $\tilde P_0\leftarrow\mathrm{GenZero}(1^\lambda,1^n)$ are indistinguishable; unsupported lengths make both experiments output $0$.
--
--   Two such obfuscators (sparse set, partition) form the decoder's corruption tests in Construction 6.1.
--
--   **Formalization Note** The seed-to-function map is the field `func`; the deterministic polynomial-time map from seeds to descriptions is the clause that one polynomial-time machine computes $f_\sigma(x)$ from $(1^\lambda,1^n,\sigma,x)$ for every seed returned by GenProg. Theorems 5.2 and 5.3 also state the polynomial-time map from seeds to their set or partition. The supported lengths are $n\ge N_{\min}(\lambda)$ with an extra restriction `supp`. The adversary's length is a polynomially bounded sequence $n(\lambda)$ hard-wired into a polynomial-size distinguisher. Machines receive $1^\lambda,1^n$ with their inputs.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 5.1, p.31 (PDF p.34)

import Mathlib
import Definitions.Def_NoisyOWMPC_Distinguisher
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_NoisyOWMPC_wprob

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- A **distributional evasive obfuscator** `Π_EvObf = (GenProg, GenZero, Eval)` together with its
map from sampling seeds to functions (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission (manuscript
sha256 52f4b606…a769709), Definition 5.1, p.31): `GenProg(1^λ, 1^n) → (σ, P̃_σ)`, `GenZero(1^λ, 1^n)
→ P̃_0`, a deterministic `Eval(P̃, x) ∈ {0,1}`, and the function `f_σ` on `{0,1}^n` specified by a
seed `σ`.

**Formalization Note** The randomized algorithms take explicit coins. `func λ n σ` is the function
`f_σ` that the seed `σ` specifies. Definition 5.1's "deterministic polynomial-time map from
sampling seeds to descriptions of functions" is the clause of `IsEvObf` that one polynomial-time
machine computes `f_σ(x)` from `(1^λ, 1^n, σ, x)` for every seed `σ` returned by `GenProg`; the
specific families of Theorems 5.2 and 5.3 also state the polynomial-time map from seeds to their
index (a set, a partition). -/
structure EvObf where
  /-- coins of `GenProg(1^λ, 1^n)` -/
  progCoins : ℕ → ℕ → ℕ
  /-- `GenProg(1^λ, 1^n; r) = (σ, P̃_σ)` -/
  genProg : (lam n : ℕ) → (Fin (progCoins lam n) → Bool) → List Bool × List Bool
  /-- coins of `GenZero(1^λ, 1^n)` -/
  zeroCoins : ℕ → ℕ → ℕ
  /-- `GenZero(1^λ, 1^n; r) = P̃_0` -/
  genZero : (lam n : ℕ) → (Fin (zeroCoins lam n) → Bool) → List Bool
  /-- `Eval(P̃, x)` -/
  eval : List Bool → List Bool → Bool
  /-- the function `f_σ` specified by the seed `σ` -/
  func : (lam n : ℕ) → List Bool → (Fin n → Bool) → Bool

/-- `Π_EvObf` is a **distributional evasive obfuscator for `{F_{λ,n}}` with minimum input length
`N_min`** (Definition 5.1, p.31), on the supported lengths `N_min(λ) ≤ n` with `supp λ n`:
1. `N_min` is an efficiently computable polynomial;
2. `GenProg`, `GenZero` and `Eval` (on generated programs) run in time `poly(λ, n)`;
3. `f_σ ∈ F_{λ,n}` for every seed returned by `GenProg`, and `f_σ(x)` is computed from `σ` and `x`
   in time `poly(λ, n)` (the deterministic polynomial-time map from seeds to descriptions);
4. *correctness*: for every polynomial `P` there is a negligible `ν_P` such that for all `λ` and all
   supported `N_min(λ) ≤ n ≤ P(λ)`, with probability at least `1 − ν_P(λ)` over `GenProg`,
   `Eval(P̃_σ, x) = f_σ(x)` for all `x ∈ {0,1}^n`, and with probability at least `1 − ν_P(λ)` over
   `GenZero`, `Eval(P̃_0, x) = 0` for all `x`;
5. *null indistinguishability*: for every adversary choosing a length `1^n`, the program `P̃` of
   `GenProg(1^λ, 1^n)` (seed hidden) and `P̃_0 ← GenZero(1^λ, 1^n)` are indistinguishable;
   unsupported lengths make both experiments output `0`.

**Formalization Note** "Every polynomial `P`" is "every bound `n ≤ (λ + 2)^c`". The adversary is
nonuniform and deterministic: its length is a polynomially bounded sequence `n(λ)` hard-wired into a
polynomial-size distinguisher of `P̃`. Machines receive `1^λ, 1^n` with their inputs. -/
def EvObf.IsEvObf (O : EvObf) (Nmin : ℕ → ℕ) (supp : ℕ → ℕ → Prop)
    (F : (lam n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  PolyParam Nmin ∧
  (∃ c : ℕ, ∀ lam n, Nmin lam ≤ n → supp lam n →
    O.progCoins lam n ≤ (lam + n + 2) ^ c ∧ O.zeroCoins lam n ≤ (lam + n + 2) ^ c) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (O.progCoins z.1.1 z.1.2) → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, bits i.2])
    (fun i => QAdvFew.PoQOracle.tup
      [(O.genProg i.1.1.1 i.1.1.2 i.2).1, (O.genProg i.1.1.1 i.1.1.2 i.2).2]) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (O.zeroCoins z.1.1 z.1.2) → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, bits i.2])
    (fun i => O.genZero i.1.1.1 i.1.1.2 i.2) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (O.progCoins z.1.1 z.1.2) → Bool) × (Fin z.1.2 → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, (O.genProg i.1.1.1 i.1.1.2 i.2.1).2, bits i.2.2])
    (fun i => [O.eval (O.genProg i.1.1.1 i.1.1.2 i.2.1).2 (bits i.2.2)]) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (O.zeroCoins z.1.1 z.1.2) → Bool) × (Fin z.1.2 → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, O.genZero i.1.1.1 i.1.1.2 i.2.1, bits i.2.2])
    (fun i => [O.eval (O.genZero i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2)]) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (O.progCoins z.1.1 z.1.2) → Bool) × (Fin z.1.2 → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, (O.genProg i.1.1.1 i.1.1.2 i.2.1).1, bits i.2.2])
    (fun i => [O.func i.1.1.1 i.1.1.2 (O.genProg i.1.1.1 i.1.1.2 i.2.1).1 i.2.2]) ∧
  (∀ lam n, Nmin lam ≤ n → supp lam n → ∀ r : Fin (O.progCoins lam n) → Bool,
    O.func lam n (O.genProg lam n r).1 ∈ F lam n) ∧
  (∀ c : ℕ, ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam n, Nmin lam ≤ n → supp lam n →
    n ≤ (lam + 2) ^ c →
      wprob (unifW (Fin (O.progCoins lam n) → Bool)) (fun r =>
        ¬ ∀ x : Fin n → Bool,
          O.eval (O.genProg lam n r).2 (bits x) = O.func lam n (O.genProg lam n r).1 x) ≤ ν lam ∧
      wprob (unifW (Fin (O.zeroCoins lam n) → Bool)) (fun r =>
        ¬ ∀ x : Fin n → Bool, O.eval (O.genZero lam n r) (bits x) = false) ≤ ν lam) ∧
  ∀ n : ℕ → ℕ, PolyBounded n → ∀ D : Distinguisher, D.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ lam, Nmin lam ≤ n lam → supp lam (n lam) →
      |D.accProb lam (unifW (Fin (O.progCoins lam (n lam)) → Bool))
          (fun r => (O.genProg lam (n lam) r).2) -
        D.accProb lam (unifW (Fin (O.zeroCoins lam (n lam)) → Bool))
          (fun r => O.genZero lam (n lam) r)| ≤ ν lam

end SeededShannon


