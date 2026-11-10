-- Prove2me | Definitions.Def_SeededShannon_RecEmb
-- name    : SeededShannon_RecEmb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:55.549689+00:00
-- url     : https://prove2.me/theorems/2eba557c-f988-486c-922c-0f59991c9b67
-- title:
--   Recoverable embedding (Definition 5.4)
-- statement:
--   Let $N_{\min}$ be an efficiently computable polynomial and $\{\mathcal F_{\lambda,n}\}_{n\ge N_{\min}(\lambda)}$ a family of functions $\{0,1\}^n\to\{0,1\}$. A **recoverable embedding** $\Pi_{\mathrm{Emb}}=(\mathrm{SampleParams},\mathrm{SampleFunc},\mathrm{RecoverSeeds})$ runs in time $\mathrm{poly}(\lambda,n)$:
--
--   1. $\mathrm{SampleParams}(1^\lambda,1^n)\to pp$, randomized;
--   2. $\mathrm{SampleFunc}(pp,u)\to f_u\in\mathcal F_{\lambda,n}$, deterministic, for seeds $u\in\{0,1\}^\lambda$, a description evaluable in time $\mathrm{poly}(\lambda,n)$;
--   3. $\mathrm{RecoverSeeds}(pp,y)\to L\subseteq\{0,1\}^\lambda$, deterministic.
--
--   $pp$ is **perfectly recoverable** if for all $y\in\{0,1\}^n$ and all $u$ with $f_u(y)=1$, $u\in\mathrm{RecoverSeeds}(pp,y)$. **Correctness**: for every polynomial $P$ there is a negligible $\nu_P$ such that for all $\lambda$ and all supported $N_{\min}(\lambda)\le n\le P(\lambda)$, $pp\leftarrow\mathrm{SampleParams}(1^\lambda,1^n)$ is perfectly recoverable with probability at least $1-\nu_P(\lambda)$.
--
--   Recoverable embeddings are the information-theoretic core from which Theorem A.1 builds evasive obfuscators.
--
--   **Formalization Note** Descriptions are bit strings evaluated by a fixed evaluator. The supported lengths are $n\ge N_{\min}(\lambda)$ with an extra restriction `supp` (for instance $b\mid n$). Machines receive $1^\lambda,1^n$ with their inputs and run on honest parameters. "Every polynomial $P$" is "every bound $n\le(\lambda+2)^c$".
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 5.4, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_NoisyOWMPC_wprob
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- A **recoverable embedding** `Π_Emb = (SampleParams, SampleFunc, RecoverSeeds)` (Dujmovic, Lu,
Silbak, Wichs, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 5.4, p.32):
`SampleParams(1^λ, 1^n) → pp`; a deterministic `SampleFunc(pp, u) → f_u`, a description of a
function on `{0,1}^n`, for seeds `u ∈ {0,1}^λ`; a deterministic `RecoverSeeds(pp, y) → L ⊆ {0,1}^λ`.

**Formalization Note** `sampleParams λ n r` uses coins `r ∈ {0,1}^{ppCoins λ n}`. Descriptions are
bit strings, evaluated by `evalDesc`: `f_u(y) = evalDesc(SampleFunc(pp, u), y)`. -/
structure RecEmb where
  /-- coins of `SampleParams(1^λ, 1^n)` -/
  ppCoins : ℕ → ℕ → ℕ
  /-- `SampleParams(1^λ, 1^n; r) = pp` -/
  sampleParams : (lam n : ℕ) → (Fin (ppCoins lam n) → Bool) → List Bool
  /-- `SampleFunc(pp, u)`, a description of `f_u` -/
  sampleFunc : List Bool → List Bool → List Bool
  /-- evaluation of a function description on an input -/
  evalDesc : List Bool → List Bool → Bool
  /-- `RecoverSeeds(pp, y)` -/
  recoverSeeds : List Bool → List Bool → List (List Bool)

/-- `pp` is **perfectly recoverable** (Definition 5.4, p.32): for all `y ∈ {0,1}^n` and all
`u ∈ {0,1}^λ` with `f_u(y) = 1`, `u ∈ RecoverSeeds(pp, y)`, where `f_u := SampleFunc(pp, u)`. -/
def RecEmb.PerfectlyRecoverable (E : RecEmb) (lam n : ℕ) (pp : List Bool) : Prop :=
  ∀ (y : Fin n → Bool) (u : Fin lam → Bool),
    E.evalDesc (E.sampleFunc pp (bits u)) (bits y) = true → bits u ∈ E.recoverSeeds pp (bits y)

/-- `Π_Emb` is a **recoverable embedding for the family `{F_{λ,n}}` with minimum input length
`N_min`** (Definition 5.4, p.32), on the supported lengths `N_min(λ) ≤ n` with `supp λ n`:
1. `N_min` is an efficiently computable polynomial;
2. the algorithms run in time `poly(λ, n)`, and `f_u` can be evaluated in time `poly(λ, n)`;
3. every `f_u = SampleFunc(pp, u)` with `pp` in the support of `SampleParams` lies in `F_{λ,n}`, and
   `RecoverSeeds` lists strings of length `λ`;
4. *correctness*: for every polynomial `P` there is a negligible `ν_P` such that for all `λ` and
   all supported `N_min(λ) ≤ n ≤ P(λ)`, `pp ← SampleParams(1^λ, 1^n)` is perfectly recoverable with
   probability at least `1 − ν_P(λ)`.

**Formalization Note** `supp` is the additional restriction on lengths (e.g. divisibility by a
constant); unsupported lengths play no role. "Every polynomial `P`" is "every bound
`n ≤ (λ + 2)^c`". Machines receive `1^λ, 1^n` with their inputs, and run on honest parameters. -/
def RecEmb.IsRecEmb (E : RecEmb) (Nmin : ℕ → ℕ) (supp : ℕ → ℕ → Prop)
    (F : (lam n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  PolyParam Nmin ∧
  (∃ c : ℕ, ∀ lam n, Nmin lam ≤ n → supp lam n → E.ppCoins lam n ≤ (lam + n + 2) ^ c) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (E.ppCoins z.1.1 z.1.2) → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, bits i.2])
    (fun i => E.sampleParams i.1.1.1 i.1.1.2 i.2) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (E.ppCoins z.1.1 z.1.2) → Bool) × (Fin z.1.1 → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, E.sampleParams i.1.1.1 i.1.1.2 i.2.1, bits i.2.2])
    (fun i => E.sampleFunc (E.sampleParams i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2)) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (E.ppCoins z.1.1 z.1.2) → Bool) × (Fin z.1.1 → Bool) × (Fin z.1.2 → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2,
      E.sampleFunc (E.sampleParams i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2.1), bits i.2.2.2])
    (fun i => [E.evalDesc (E.sampleFunc (E.sampleParams i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2.1))
      (bits i.2.2.2)]) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ supp z.1 z.2}) ×
      (Fin (E.ppCoins z.1.1 z.1.2) → Bool) × (Fin z.1.2 → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, E.sampleParams i.1.1.1 i.1.1.2 i.2.1, bits i.2.2])
    (fun i => QAdvFew.PoQOracle.tup
      (E.recoverSeeds (E.sampleParams i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2))) ∧
  (∀ lam n, Nmin lam ≤ n → supp lam n → ∀ (r : Fin (E.ppCoins lam n) → Bool) (u : Fin lam → Bool),
    (fun y : Fin n → Bool => E.evalDesc (E.sampleFunc (E.sampleParams lam n r) (bits u)) (bits y))
      ∈ F lam n) ∧
  (∀ lam n, Nmin lam ≤ n → supp lam n → ∀ (r : Fin (E.ppCoins lam n) → Bool) (y : Fin n → Bool),
    ∀ u ∈ E.recoverSeeds (E.sampleParams lam n r) (bits y), u.length = lam) ∧
  ∀ c : ℕ, ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam n, Nmin lam ≤ n → supp lam n → n ≤ (lam + 2) ^ c →
    wprob (unifW (Fin (E.ppCoins lam n) → Bool))
      (fun r => ¬ E.PerfectlyRecoverable lam n (E.sampleParams lam n r)) ≤ ν lam

end SeededShannon


