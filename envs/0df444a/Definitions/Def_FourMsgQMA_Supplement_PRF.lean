-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_PRF
-- name    : FourMsgQMA_Supplement_PRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:22:33.73682+00:00
-- url     : https://prove2.me/theorems/5e45cfbc-3d9d-4597-a251-f16c09e57b21
-- title:
--   Post-quantum pseudorandom functions (Def 3.30)
-- statement:
--   A **pseudorandom-function family** consists of a key generator $a\leftarrow\mathrm{Gen}(1^\lambda)$ and a deterministic evaluation $\mathrm{Eval}(a,i)\in\{0,1\}^v$ on the domain $\{0,1\}^\ell$, with keys and algorithms of size polynomial in $(\lambda,\ell,v)$.
--
--   **Post-quantum security** (Definition 3.30): for every QPT oracle algorithm $A$ with classical queries and admissible auxiliary input, with
--   $$
--   p_{\mathrm{PRF}}=\Pr\big[A^{\mathrm{Eval}(a,\cdot)}=1: a\leftarrow\mathrm{Gen}(1^\lambda)\big],\qquad p_{\mathrm{rand}}=\Pr\big[A^{F}=1: F\leftarrow\mathrm{Func}(\{0,1\}^\ell,\{0,1\}^v)\big],
--   $$
--   security requires $|p_{\mathrm{PRF}}-p_{\mathrm{rand}}|\le\mathrm{negl}(\lambda)$.
--
--   PRFs are one of the hypotheses of Theorem 7.5 (the basis generator and the private final coins of §7.1).
--
--   **Formalization Note** An oracle algorithm is an `IsQPT` strategy that makes $Q(\lambda)$ classical queries, one per round, for any polynomial $Q$; its output is the first bit of its last answer. A query outside $\{0,1\}^\ell$ is answered by $0^v$ in both worlds.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.14 and Definition 3.30, pp.25–26 (PDF 27–28)

import Mathlib
import Definitions.Def_FourMsgQMA_Supplement_HashFamily

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.14 and Definition 3.30 (pp.25–26,
PDF 27–28): pseudorandom functions `a ← Gen(1^λ)`, `Eval(a, i) ∈ {0,1}^v` on a declared domain
`{0,1}^ℓ`, and post-quantum security against QPT oracle algorithms with classical queries.

Pinned-down version (operator request): an oracle algorithm is a published `IsQPT` strategy run
against an oracle that answers, in each round, the query the strategy sent in the previous round;
it makes `Q(λ)` queries for a polynomial `Q` and its output is the first bit of its last answer.
A query outside the domain `{0,1}^ℓ` is answered by `0^v` in both worlds.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- A pseudorandom-function family (§3.14, p.25). -/
structure PRF where
  /-- The coins of `Gen(1^λ)`. -/
  genCoins : ℕ → ℕ
  /-- `a ← Gen(1^λ)`, with coins. -/
  gen : ℕ → Bits → Bits
  /-- `Eval(a, i)`, deterministic. -/
  eval : Bits → Bits → Bits

/-- Efficiency for the domain length `ℓ(λ)` and output length `v(λ)` (§3.14, p.25: "Keys and
algorithms have size polynomial in `(λ, ℓ, v)`"): polynomial coin and key lengths, polynomial-time
`Gen` and `Eval`, and outputs of length exactly `v` on the domain. -/
def PRF.Efficient (Φ : PRF) (l v : ℕ → ℕ) : Prop :=
  PolyBound Φ.genCoins ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam, g (unary lam) = unary (Φ.genCoins lam)) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam r, g (pack [unary lam, r]) = Φ.gen lam r) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ a i, g (pack [a, i]) = Φ.eval a i) ∧
  ∀ lam (r i : Bits), r.length = Φ.genCoins lam → i.length = l lam →
    (Φ.eval (Φ.gen lam r) i).length = v lam

/-- The oracle of the real world: `Eval(a, ·)` with `a ← Gen(1^λ)` from the coins `r`. -/
def PRF.realAnswer (Φ : PRF) (l v : ℕ → ℕ) (lam : ℕ) (r i : Bits) : Bits :=
  if i.length = l lam then Φ.eval (Φ.gen lam r) i else zeros (v lam)

/-- The oracle of the ideal world: a uniformly random function `F : {0,1}^ℓ → {0,1}^v`, given by its
table `r` of `2^ℓ · v` uniform bits. -/
def randAnswer (l v : ℕ → ℕ) (lam : ℕ) (r i : Bits) : Bits :=
  if i.length = l lam then (r.drop (bitsVal i * v lam)).take (v lam) else zeros (v lam)

/-- The oracle experiment as a published `TightPQRepetition.Main.Verifier` (semantic carrier):
round `0` sends the empty string; round `j + 1` sends the oracle's answer to the strategy's round-`j`
answer (its query); after `Q(λ)` queries the output is the first bit of the last answer. -/
def oracleVerifier (Q : ℕ → ℕ) (coins : ℕ → ℕ) (oracle : ℕ → Bits → Bits → Bits) : Verifier where
  rounds := fun lam => Q lam + 1
  coins := coins
  qLen := fun _ _ => 0
  query := fun lam r j as => if j = 0 then [] else oracle lam r (as.getD (j - 1) [])
  verdict := fun lam _ τ => (τ.getD (Q lam) ([], [])).2.getD 0 false

/-- Post-quantum PRF security, Definition 3.30 (p.26), for the domain `{0,1}^ℓ` and outputs in
`{0,1}^v`: for every polynomial query bound `Q` and every QPT oracle algorithm with classical queries
and quantum advice, `|p_PRF − p_rand| ≤ ν(λ)` for a negligible `ν`. -/
def PRF.Secure (Φ : PRF) (l v : ℕ → ℕ) : Prop :=
  ∀ Q : ℕ → ℕ, PolyBound Q → ∀ Adv : ℕ → Strategy, IsQPT Adv →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |(Adv lam).acceptProb (oracleVerifier Q Φ.genCoins (Φ.realAnswer l v)) lam -
        (Adv lam).acceptProb (oracleVerifier Q (fun lam => 2 ^ l lam * v lam) (randAnswer l v)) lam|
        ≤ ν lam

end Supplement

end FourMsgQMA


