-- Prove2me | Definitions.Def_SeededShannon_PPRC
-- name    : SeededShannon_PPRC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:58.776195+00:00
-- url     : https://prove2.me/theorems/0ffcdf21-7795-4483-8e02-e122f79c980f
-- title:
--   $t$-puncturable $p$-robust pseudorandom code at input length $\ell_{in}$ (Definition 4.1)
-- statement:
--   A **$t$-puncturable pseudorandom code** $\Pi_{\mathrm{PPRC}}=(\mathrm{KeyGen},\mathrm{Eval},\mathrm{Puncture},\mathrm{Recover})$ with output length $\ell_{out}=\mathrm{poly}(\lambda,\ell_{in})$ has a randomized $\mathrm{KeyGen}(1^\lambda,1^{\ell_{in}})\to K$, $\mathrm{Puncture}(K,S)\to K_S$ for $|S|\le t$, a deterministic $\mathrm{Eval}(\hat K,x)\in\{0,1\}^{\ell_{out}}$ (with $\mathrm{Eval}(K_S,x)=\perp$ for $x\in S$), and a deterministic $\mathrm{Recover}(\hat K,y)\subseteq\{0,1\}^{\ell_{in}}$. At input length $\ell_{in}=\ell_{in}(\lambda)$ it is required that:
--
--   1. lengths, coins and running times are polynomial;
--   2. **functionality preservation**: $\mathrm{Eval}(K,x)=\mathrm{Eval}(K_S,x)$ for every $|S|\le t$ and $x\notin S$, with probability $1$;
--   3. **punctured pseudorandomness**: the selective experiment of Definition 3.4 with $|S|\le t$, the adversary choosing only $S$;
--   4. **$p$-robust functionality-preserving recovery**: with probability at least $1-\mathrm{negl}(\lambda)$ over $K\leftarrow\mathrm{KeyGen}(1^\lambda,1^{\ell_{in}})$, simultaneously for every $y\in\{0,1\}^{\ell_{out}}$, every $|S|\le t$ and every $K_S$ in the support of $\mathrm{Puncture}(K,S)$,
--   $$\mathrm{Recover}(K,y)=\mathrm{Recover}(K_S,y)\cup\{x\in S:\delta(\mathrm{Eval}(K,x),y)\le p\}.\tag{4.1}$$
--
--   The PPRC writes the hash of the message into the headers of the seeded code of Construction 6.1; (4.1) lets the decoder recover the hash from any lightly corrupted header.
--
--   **Formalization Note** All clauses are at the input length $\ell_{in}(\lambda)$ passed as a parameter (Theorem 4.13 gives a PPRC "with input length $\ell_{in}$"). Sets are strictly lexicographically increasing lists, $\perp$ is `none`, the recovery identity is an equality of sets, and $\delta\le p$ is $\Delta\le p\cdot\ell_{out}$. Probability $1$ over finitely many uniform coins is "for all coins".
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 4.1, p.23 (PDF p.26)

import Mathlib
import Definitions.Def_SeededShannon_PPRF
import Definitions.Def_SeededShannon_SeededCode

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- A **puncturable pseudorandom code** `Π_PPRC = (KeyGen, Eval, Puncture, Recover)` (Dujmovic, Lu,
Silbak, Wichs, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 4.1, p.23):
`KeyGen(1^λ, 1^{ℓin}) → K`, `Puncture(K, S) → K_S`, a deterministic `Eval(K̂, x) ∈ {0,1}^{ℓout}`
(`⊥` on punctured points) and a deterministic `Recover(K̂, y) ⊆ {0,1}^{ℓin}`, with output length
`ℓout = ℓout(λ, ℓin)`.

**Formalization Note** Randomized algorithms take explicit coins; keys are bit strings; `Eval`
returns `none` for `⊥`; the set returned by `Recover` is a list. -/
structure PPRC where
  /-- coins of `KeyGen(1^λ, 1^{ℓin})` -/
  keyCoins : ℕ → ℕ → ℕ
  /-- the output length `ℓout(λ, ℓin)` -/
  lout : ℕ → ℕ → ℕ
  /-- `KeyGen(1^λ, 1^{ℓin}; r) = K` -/
  keyGen : (lam lin : ℕ) → (Fin (keyCoins lam lin) → Bool) → List Bool
  /-- coins of `Puncture` -/
  puncCoins : ℕ → ℕ → ℕ
  /-- `Puncture(K, S; r′) = K_S` -/
  puncture : (lam lin : ℕ) → List Bool → List (List Bool) → (Fin (puncCoins lam lin) → Bool) →
    List Bool
  /-- `Eval(K̂, x)`, `none` meaning `⊥` -/
  eval : List Bool → List Bool → Option (List Bool)
  /-- `Recover(K̂, y)` -/
  recover : List Bool → List Bool → List (List Bool)

/-- `Π_PPRC` is a **`t`-puncturable, `p`-robust pseudorandom code with input length `ℓin`**
(Definition 4.1, p.23, at the input length `ℓin(λ)` of Theorem 4.13): writing `ℓout = ℓout(λ, ℓin(λ))`,
1. *lengths and efficiency*: `ℓout`, the coin counts are `poly(λ, ℓin)`; `KeyGen`, `Puncture`,
   `Eval` and `Recover` run in polynomial time (on full keys and on punctured keys in the support of
   `Puncture`);
2. *syntax*: `Eval(K, x) ∈ {0,1}^{ℓout}` for full keys; `Eval(K_S, x) = ⊥` for `x ∈ S`; every
   recovered string has length `ℓin`;
3. *functionality preservation*: `Eval(K, x) = Eval(K_S, x)` for every `S` with `|S| ≤ t` and every
   `x ∉ S`, with probability `1`;
4. *punctured pseudorandomness*: the selective experiment of Definition 3.4 with `|S| ≤ t`, the
   adversary choosing only `S` (`ℓout` is fixed by the construction);
5. *`p`-robust functionality-preserving recovery* (4.1): there is a negligible `ν` such that, with
   probability at least `1 − ν(λ)` over `K ← KeyGen(1^λ, 1^{ℓin})`, simultaneously for every
   `y ∈ {0,1}^{ℓout}`, every `S` with `|S| ≤ t` and every `K_S` in the support of `Puncture(K, S)`,
   `Recover(K, y) = Recover(K_S, y) ∪ {x ∈ S : δ(Eval(K, x), y) ≤ p}`.

**Formalization Note** All clauses are taken at the input length `ℓin(λ)` given as a parameter
(Theorem 4.13: "with input length `ℓin`"); Definition 4.1's "for every polynomially bounded
input-length function" is the choice of this parameter. The recovery identity is an equality of
sets (membership). `δ ≤ p` is `Δ ≤ p · ℓout`. Probability `1` over finitely many uniform coins is
"for all coins". Adversaries are nonuniform: the committed set `S(λ)` is hard-wired. -/
def PPRC.IsPPRCAt (C : PPRC) (t : ℕ → ℕ) (p : ℝ) (lin : ℕ → ℕ) : Prop :=
  (∃ c : ℕ, ∀ lam, C.lout lam (lin lam) ≤ (lam + lin lam + 2) ^ c ∧
    C.keyCoins lam (lin lam) ≤ (lam + lin lam + 2) ^ c ∧
    C.puncCoins lam (lin lam) ≤ (lam + lin lam + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (C.keyCoins lam (lin lam)) → Bool))
    (fun i => [unary i.1, unary (lin i.1), bits i.2]) (fun i => C.keyGen i.1 (lin i.1) i.2) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (C.keyCoins lam (lin lam)) → Bool) ×
      {S : List (List Bool) // ValidSet (t lam) (lin lam) S} ×
      (Fin (C.puncCoins lam (lin lam)) → Bool))
    (fun i => [unary i.1, unary (lin i.1), C.keyGen i.1 (lin i.1) i.2.1,
      QAdvFew.PoQOracle.tup i.2.2.1.1, bits i.2.2.2])
    (fun i => C.puncture i.1 (lin i.1) (C.keyGen i.1 (lin i.1) i.2.1) i.2.2.1.1 i.2.2.2) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (C.keyCoins lam (lin lam)) → Bool) × (Fin (lin lam) → Bool))
    (fun i => [unary i.1, unary (lin i.1), C.keyGen i.1 (lin i.1) i.2.1, bits i.2.2])
    (fun i => encOpt (C.eval (C.keyGen i.1 (lin i.1) i.2.1) (bits i.2.2))) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (C.keyCoins lam (lin lam)) → Bool) ×
      {S : List (List Bool) // ValidSet (t lam) (lin lam) S} ×
      (Fin (C.puncCoins lam (lin lam)) → Bool) × (Fin (lin lam) → Bool))
    (fun i => [unary i.1, unary (lin i.1),
      C.puncture i.1 (lin i.1) (C.keyGen i.1 (lin i.1) i.2.1) i.2.2.1.1 i.2.2.2.1, bits i.2.2.2.2])
    (fun i => encOpt (C.eval
      (C.puncture i.1 (lin i.1) (C.keyGen i.1 (lin i.1) i.2.1) i.2.2.1.1 i.2.2.2.1)
      (bits i.2.2.2.2))) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (C.keyCoins lam (lin lam)) → Bool) ×
      (Fin (C.lout lam (lin lam)) → Bool))
    (fun i => [unary i.1, unary (lin i.1), C.keyGen i.1 (lin i.1) i.2.1, bits i.2.2])
    (fun i => QAdvFew.PoQOracle.tup (C.recover (C.keyGen i.1 (lin i.1) i.2.1) (bits i.2.2))) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (C.keyCoins lam (lin lam)) → Bool) ×
      {S : List (List Bool) // ValidSet (t lam) (lin lam) S} ×
      (Fin (C.puncCoins lam (lin lam)) → Bool) × (Fin (C.lout lam (lin lam)) → Bool))
    (fun i => [unary i.1, unary (lin i.1),
      C.puncture i.1 (lin i.1) (C.keyGen i.1 (lin i.1) i.2.1) i.2.2.1.1 i.2.2.2.1, bits i.2.2.2.2])
    (fun i => QAdvFew.PoQOracle.tup (C.recover
      (C.puncture i.1 (lin i.1) (C.keyGen i.1 (lin i.1) i.2.1) i.2.2.1.1 i.2.2.2.1)
      (bits i.2.2.2.2))) ∧
  (∀ (lam : ℕ) (r : Fin (C.keyCoins lam (lin lam)) → Bool) (x : Fin (lin lam) → Bool),
    ∃ y : List Bool, C.eval (C.keyGen lam (lin lam) r) (bits x) = some y ∧
      y.length = C.lout lam (lin lam)) ∧
  (∀ (lam : ℕ) (r : Fin (C.keyCoins lam (lin lam)) → Bool) (y : Fin (C.lout lam (lin lam)) → Bool),
    ∀ x ∈ C.recover (C.keyGen lam (lin lam) r) (bits y), x.length = lin lam) ∧
  (∀ (lam : ℕ) (S : List (List Bool)), ValidSet (t lam) (lin lam) S →
    ∀ (r : Fin (C.keyCoins lam (lin lam)) → Bool) (r' : Fin (C.puncCoins lam (lin lam)) → Bool),
      (∀ x ∈ S, C.eval (C.puncture lam (lin lam) (C.keyGen lam (lin lam) r) S r') x = none) ∧
      (∀ (y : Fin (C.lout lam (lin lam)) → Bool),
        ∀ x ∈ C.recover (C.puncture lam (lin lam) (C.keyGen lam (lin lam) r) S r') (bits y),
          x.length = lin lam) ∧
      ∀ x : Fin (lin lam) → Bool, bits x ∉ S →
        C.eval (C.keyGen lam (lin lam) r) (bits x) =
          C.eval (C.puncture lam (lin lam) (C.keyGen lam (lin lam) r) S r') (bits x)) ∧
  (∀ S : ℕ → List (List Bool), (∀ lam, ValidSet (t lam) (lin lam) (S lam)) →
    ∀ D : Distinguisher, D.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |D.accProb lam (unifW ((Fin (C.keyCoins lam (lin lam)) → Bool) ×
            (Fin (C.puncCoins lam (lin lam)) → Bool)))
          (fun ω => QAdvFew.PoQOracle.tup
            [C.puncture lam (lin lam) (C.keyGen lam (lin lam) ω.1) (S lam) ω.2,
             QAdvFew.PoQOracle.tup ((S lam).map fun x =>
               (C.eval (C.keyGen lam (lin lam) ω.1) x).getD [])]) -
        D.accProb lam (unifW ((Fin (C.keyCoins lam (lin lam)) → Bool) ×
            (Fin (C.puncCoins lam (lin lam)) → Bool) ×
            (Fin (S lam).length → Fin (C.lout lam (lin lam)) → Bool)))
          (fun ω => QAdvFew.PoQOracle.tup
            [C.puncture lam (lin lam) (C.keyGen lam (lin lam) ω.1) (S lam) ω.2.1,
             QAdvFew.PoQOracle.tup (List.ofFn fun i => bits (ω.2.2 i))])| ≤ ν lam) ∧
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    wprob (unifW (Fin (C.keyCoins lam (lin lam)) → Bool)) (fun r =>
      ¬ ∀ (y : Fin (C.lout lam (lin lam)) → Bool) (S : List (List Bool)),
        ValidSet (t lam) (lin lam) S → ∀ (r' : Fin (C.puncCoins lam (lin lam)) → Bool)
          (x : List Bool),
          x ∈ C.recover (C.keyGen lam (lin lam) r) (bits y) ↔
            (x ∈ C.recover (C.puncture lam (lin lam) (C.keyGen lam (lin lam) r) S r') (bits y) ∨
              (x ∈ S ∧ ∃ z : List Bool, C.eval (C.keyGen lam (lin lam) r) x = some z ∧
                (ldist z (bits y) : ℝ) ≤ p * C.lout lam (lin lam)))) ≤ ν lam

end SeededShannon


