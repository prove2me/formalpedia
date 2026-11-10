-- Prove2me | Definitions.Def_SeededShannon_PPRF
-- name    : SeededShannon_PPRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:05.254208+00:00
-- url     : https://prove2.me/theorems/42c4983d-11f4-4425-8146-74f113763fb1
-- title:
--   $t$-puncturable pseudorandom function (Definition 3.4)
-- statement:
--   A **$t$-puncturable PRF** $\Pi_{\mathrm{PPRF}}=(\mathrm{KeyGen},\mathrm{Eval},\mathrm{Puncture})$ has a randomized $\mathrm{KeyGen}(1^\lambda,1^{\ell_{in}},1^{\ell_{out}})\to K$, a (possibly randomized) $\mathrm{Puncture}(K,S)\to K_S$ for $S\subseteq\{0,1\}^{\ell_{in}}$ with $|S|\le t$, and a deterministic $\mathrm{Eval}(\hat K,x)$ on full or punctured keys, returning $\perp$ on $x\in S$. It is required that:
--
--   1. the algorithms are polynomial-time and $\mathrm{Eval}(K,x)\in\{0,1\}^{\ell_{out}}$;
--   2. **functionality preservation**: for all $\lambda,\ell_{in},\ell_{out}$, every $S$ with $|S|\le t$ and every $x\notin S$, $\Pr[\mathrm{Eval}(K,x)=\mathrm{Eval}(K_S,x)]=1$;
--   3. **selective punctured pseudorandomness**: an adversary commits to $1^{\ell_{in}}$, $1^{\ell_{out}}$ and $S=\{x_1^*<\dots<x_s^*\}$, $s\le t$, receives $K_S$ and either $(\mathrm{Eval}(K,x_i^*))_i$ or independent uniform $y_i^*\in\{0,1\}^{\ell_{out}}$; its advantage is negligible.
--
--   It is the PRF that derives the hidden set, partition and mask in Construction 6.1 and the encoding randomness in Construction 4.2.
--
--   **Formalization Note** Coins are explicit; probability $1$ over finitely many uniform coins is "for all coins". Sets are strictly lexicographically increasing lists. Adversaries are nonuniform: their choices are polynomially bounded sequences hard-wired into a polynomial-size distinguisher. Machines also receive $1^\lambda,1^{\ell_{in}},1^{\ell_{out}}$.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 3.4, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_NoisyOWMPC_Distinguisher
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_NoisyOWMPC_wprob

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- The bit-string code of an output in `{0,1}^* ∪ {⊥}`: `⊥ ↦ 0`, `y ↦ 1y` (used to feed
evaluation outputs to machines). -/
def encOpt : Option (List Bool) → List Bool
  | none => [false]
  | some y => true :: y

/-- A **puncturing set** for a `t`-puncturable primitive (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Definition 3.4, p.17: "a set `S ⊆ {0,1}^{ℓin}` of
size at most `t`", "listed in lexicographic order"): a strictly increasing (lexicographic, `List.Pairwise (· < ·)`) list of
at most `t` strings, each of length `ℓin`. -/
def ValidSet (t lin : ℕ) (S : List (List Bool)) : Prop :=
  S.length ≤ t ∧ (∀ x ∈ S, x.length = lin) ∧ List.Pairwise (fun a b : List Bool => a < b) S

/-- A **puncturable PRF** `Π_PPRF = (KeyGen, Eval, Puncture)` (Dujmovic, Lu, Silbak, Wichs, STOC
2027 submission (manuscript sha256 52f4b606…a769709), Definition 3.4, p.17):
`KeyGen(1^λ, 1^{ℓin}, 1^{ℓout}) → K`, `Puncture(K, S) → K_S`, and a deterministic
`Eval(K̂, x)` on a full or punctured key, returning `⊥` on punctured points.

**Formalization Note** The randomized algorithms take explicit coin strings whose number depends on
`(λ, ℓin, ℓout)` (recorded in the key). Keys are bit strings; `Eval` returns `none` for `⊥`. -/
structure PPRF where
  /-- coins of `KeyGen(1^λ, 1^{ℓin}, 1^{ℓout})` -/
  keyCoins : ℕ → ℕ → ℕ → ℕ
  /-- `KeyGen(1^λ, 1^{ℓin}, 1^{ℓout}; r) = K` -/
  keyGen : (lam lin lout : ℕ) → (Fin (keyCoins lam lin lout) → Bool) → List Bool
  /-- coins of `Puncture` -/
  puncCoins : ℕ → ℕ → ℕ → ℕ
  /-- `Puncture(K, S; r′) = K_S` -/
  puncture : (lam lin lout : ℕ) → List Bool → List (List Bool) →
    (Fin (puncCoins lam lin lout) → Bool) → List Bool
  /-- `Eval(K̂, x)`, `none` meaning `⊥` -/
  eval : List Bool → List Bool → Option (List Bool)

/-- `Π_PPRF` is a **`t`-puncturable pseudorandom function** (Definition 3.4, p.17):
1. *efficiency*: polynomially many coins and polynomial-time `KeyGen`, `Puncture`, `Eval` (on full
   keys and on punctured keys in the support of `Puncture`), in `λ`, `ℓin`, `ℓout`;
2. *syntax*: `Eval(K, x) ∈ {0,1}^{ℓout}` for every full key and `x ∈ {0,1}^{ℓin}`, and
   `Eval(K_S, x) = ⊥` for `x ∈ S`;
3. *functionality preservation*: for all `λ, ℓin, ℓout`, every `S` of size at most `t(λ)` and every
   `x ∉ S`, `Eval(K, x) = Eval(K_S, x)` with probability `1` over `KeyGen` and `Puncture`;
4. *selective punctured pseudorandomness*: for every adversary committing to `1^{ℓin}`,
   `1^{ℓout}` and `S = {x*_1 < ⋯ < x*_s}` with `s ≤ t`, the distinguishing advantage between
   `(K_S, (Eval(K, x*_i))_i)` and `(K_S, (y*_i)_i)` with independent uniform `y*_i ∈ {0,1}^{ℓout}`
   is negligible.

**Formalization Note** Probability `1` over finitely many uniform coins is "for all coins". The
adversary is nonuniform and deterministic: its choices are sequences `ℓin(λ), ℓout(λ), S(λ)` of
polynomial size, hard-wired into a polynomial-size distinguisher. The challenge values are given in
the order of `S`. Machines receive `1^λ, 1^{ℓin}, 1^{ℓout}` with their other inputs. -/
def PPRF.IsPPRF (F : PPRF) (t : ℕ → ℕ) : Prop :=
  (∃ c : ℕ, ∀ lam lin lout, F.keyCoins lam lin lout ≤ (lam + lin + lout + 2) ^ c ∧
    F.puncCoins lam lin lout ≤ (lam + lin + lout + 2) ^ c) ∧
  PolyTimeOn (ι := (z : ℕ × ℕ × ℕ) × (Fin (F.keyCoins z.1 z.2.1 z.2.2) → Bool))
    (fun i => [unary i.1.1, unary i.1.2.1, unary i.1.2.2, bits i.2])
    (fun i => F.keyGen i.1.1 i.1.2.1 i.1.2.2 i.2) ∧
  PolyTimeOn (ι := (z : ℕ × ℕ × ℕ) × (Fin (F.keyCoins z.1 z.2.1 z.2.2) → Bool) ×
      {S : List (List Bool) // ValidSet (t z.1) z.2.1 S} × (Fin (F.puncCoins z.1 z.2.1 z.2.2) → Bool))
    (fun i => [unary i.1.1, unary i.1.2.1, unary i.1.2.2, F.keyGen i.1.1 i.1.2.1 i.1.2.2 i.2.1,
      QAdvFew.PoQOracle.tup i.2.2.1.1, bits i.2.2.2])
    (fun i => F.puncture i.1.1 i.1.2.1 i.1.2.2 (F.keyGen i.1.1 i.1.2.1 i.1.2.2 i.2.1) i.2.2.1.1
      i.2.2.2) ∧
  PolyTimeOn (ι := (z : ℕ × ℕ × ℕ) × (Fin (F.keyCoins z.1 z.2.1 z.2.2) → Bool) × (Fin z.2.1 → Bool))
    (fun i => [unary i.1.1, unary i.1.2.1, unary i.1.2.2, F.keyGen i.1.1 i.1.2.1 i.1.2.2 i.2.1,
      bits i.2.2])
    (fun i => encOpt (F.eval (F.keyGen i.1.1 i.1.2.1 i.1.2.2 i.2.1) (bits i.2.2))) ∧
  PolyTimeOn (ι := (z : ℕ × ℕ × ℕ) × (Fin (F.keyCoins z.1 z.2.1 z.2.2) → Bool) ×
      {S : List (List Bool) // ValidSet (t z.1) z.2.1 S} ×
      (Fin (F.puncCoins z.1 z.2.1 z.2.2) → Bool) × (Fin z.2.1 → Bool))
    (fun i => [unary i.1.1, unary i.1.2.1, unary i.1.2.2,
      F.puncture i.1.1 i.1.2.1 i.1.2.2 (F.keyGen i.1.1 i.1.2.1 i.1.2.2 i.2.1) i.2.2.1.1 i.2.2.2.1,
      bits i.2.2.2.2])
    (fun i => encOpt (F.eval
      (F.puncture i.1.1 i.1.2.1 i.1.2.2 (F.keyGen i.1.1 i.1.2.1 i.1.2.2 i.2.1) i.2.2.1.1 i.2.2.2.1)
      (bits i.2.2.2.2))) ∧
  (∀ (lam lin lout : ℕ) (r : Fin (F.keyCoins lam lin lout) → Bool) (x : Fin lin → Bool),
    ∃ y : List Bool, F.eval (F.keyGen lam lin lout r) (bits x) = some y ∧ y.length = lout) ∧
  (∀ (lam lin lout : ℕ) (S : List (List Bool)), ValidSet (t lam) lin S →
    ∀ (r : Fin (F.keyCoins lam lin lout) → Bool) (r' : Fin (F.puncCoins lam lin lout) → Bool),
      ∀ x ∈ S, F.eval (F.puncture lam lin lout (F.keyGen lam lin lout r) S r') x = none) ∧
  (∀ (lam lin lout : ℕ) (S : List (List Bool)), ValidSet (t lam) lin S →
    ∀ x : Fin lin → Bool, bits x ∉ S →
    ∀ (r : Fin (F.keyCoins lam lin lout) → Bool) (r' : Fin (F.puncCoins lam lin lout) → Bool),
      F.eval (F.keyGen lam lin lout r) (bits x) =
        F.eval (F.puncture lam lin lout (F.keyGen lam lin lout r) S r') (bits x)) ∧
  ∀ (lin lout : ℕ → ℕ) (S : ℕ → List (List Bool)), PolyBounded lin → PolyBounded lout →
    (∀ lam, ValidSet (t lam) (lin lam) (S lam)) →
    ∀ D : Distinguisher, D.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |D.accProb lam (unifW ((Fin (F.keyCoins lam (lin lam) (lout lam)) → Bool) ×
            (Fin (F.puncCoins lam (lin lam) (lout lam)) → Bool)))
          (fun ω => QAdvFew.PoQOracle.tup
            [F.puncture lam (lin lam) (lout lam) (F.keyGen lam (lin lam) (lout lam) ω.1) (S lam) ω.2,
             QAdvFew.PoQOracle.tup ((S lam).map fun x =>
               (F.eval (F.keyGen lam (lin lam) (lout lam) ω.1) x).getD [])]) -
        D.accProb lam (unifW ((Fin (F.keyCoins lam (lin lam) (lout lam)) → Bool) ×
            (Fin (F.puncCoins lam (lin lam) (lout lam)) → Bool) ×
            (Fin (S lam).length → Fin (lout lam) → Bool)))
          (fun ω => QAdvFew.PoQOracle.tup
            [F.puncture lam (lin lam) (lout lam) (F.keyGen lam (lin lam) (lout lam) ω.1) (S lam)
               ω.2.1,
             QAdvFew.PoQOracle.tup (List.ofFn fun i => bits (ω.2.2 i))])| ≤ ν lam

end SeededShannon


