-- Prove2me | Definitions.Def_FourMsgQMA_Arg4_Succinct
-- name    : FourMsgQMA_Arg4_Succinct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:37:26.876814+00:00
-- url     : https://prove2.me/theorems/0ac7b569-1406-47f2-a53f-c918faca11ab
-- title:
--   Batch communication and online verifier succinctness $\mathrm{poly}(\lambda,T,\log(k+1),\log(s+1))$
-- statement:
--   An argument is **succinct** for $F$ if there is one polynomial $p$, fixed by the scheme, with the following property. Write $P=p(\lambda,t(X),\lceil\log_2(k+1)\rceil,\lceil\log_2(s+1)\rceil)$. For every $\lambda$, every admissible instance and every outcome of the verifier's coins:
--
--   1. $|q_1|\le P$, and $|q_2|\le P$ whenever $|a_1|\le P$;
--   2. the verifier rejects longer answers: if $\mathrm{Dec}$ accepts then $|a_1|,|a_2|\le P$;
--   3. the online work ($V_2$ and $\mathrm{Dec}$, the computation "after preprocessing and generation of $q_1$") is at most $P$. On the inputs that occur for instances with $k$ entries, $s$ gates and $t(X)\le t$, each of $V_2$ and $\mathrm{Dec}$ is computed at every input length by Boolean circuits of total size at most $p(\lambda,t,\lceil\log_2(k+1)\rceil,\lceil\log_2(s+1)\rceil)$.
--
--   Preprocessing ($\mathrm{Pre}$, $V_1$) is not bounded here; it is polynomial time by uniformity.
--
--   **Formalization Note** Pinned-down version (operator request): $t(X)$ replaces $T$; $\log$ is $\lceil\log_2\rceil$; work is circuit size on the inputs that occur.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.3, p.12 (PDF 14), Batch communication and Online verifier succinctness; Corollary 5.15, p.44

import Mathlib
import Definitions.Def_FourMsgQMA_Arg4

namespace FourMsgQMA

open QAlgorithms.Complexity TightPQRepetition.Main

/-- The total number of verifier coins at `λ` for a statement of length `m`. -/
def Arg4.totalCoins (A : Arg4) (lam m : ℕ) : ℕ := A.coins0 lam m + A.coins1 lam m + A.coins2 lam m

/-- `V₂` as a function of its packed input `(v₁, a₁, coins)`, with packed output `(q₂, v₂)`. -/
def Arg4.v2Packed (A : Arg4) (lam : ℕ) (x : Bits) : Bits :=
  let l := unpack x
  let o := A.v2 lam (l.getD 0 []) (l.getD 1 []) (l.getD 2 [])
  pack [o.1, o.2]

/-- `Dec` as a function of its packed input `(v₂, a₂)`. -/
def Arg4.decPacked (A : Arg4) (lam : ℕ) (x : Bits) : Bits :=
  let l := unpack x
  [A.dec lam (l.getD 0 []) (l.getD 1 [])]

/-- The admissible instances with `k` entries, `s` gates and local cost `t(X) ≤ t`. -/
def instClass (F : QMAFamily) (t k s : ℕ) : Set Inst :=
  {u | u.Admissible ∧ u.k = k ∧ u.s = s ∧ batchCost F u ≤ t}

/-- The inputs `(v₁, a₁, coins of V₂)` of the online stage `V₂` that occur at `λ` on instances of
the class `(t, k, s)`, for verifier coins of the prescribed length and answers `a₁` of length at
most `b`. -/
def Arg4.v2Inputs (A : Arg4) (F : QMAFamily) (lam t k s b : ℕ) : Set Bits :=
  {x | ∃ u ∈ instClass F t k s, ∃ r : Bits, r.length = A.totalCoins lam u.size ∧
    ∃ a1 : Bits, a1.length ≤ b ∧
      x = pack [(A.firstMsg lam u.encode r).2, a1, (A.coinParts lam u.size r).2.2]}

/-- The inputs `(v₂, a₂)` of `Dec` that occur at `λ` on instances of the class `(t, k, s)`, for
verifier coins of the prescribed length and answers of length at most `b`. -/
def Arg4.decInputs (A : Arg4) (F : QMAFamily) (lam t k s b : ℕ) : Set Bits :=
  {x | ∃ u ∈ instClass F t k s, ∃ r : Bits, r.length = A.totalCoins lam u.size ∧
    ∃ a1 a2 : Bits, a1.length ≤ b ∧ a2.length ≤ b ∧
      x = pack [(A.v2 lam (A.firstMsg lam u.encode r).2 a1 (A.coinParts lam u.size r).2.2).2, a2]}

/-- Batch communication and online verifier succinctness for a circuit policy (§3.3, p.12,
"Batch communication" and "Online verifier succinctness"; Corollary 5.15, p.44: "Its communication
and online verifier work are poly(λ, T, log(k + 1), log(s + 1))"). There is one polynomial `p`,
fixed by the scheme, such that, writing `P = p(λ, t(X), ⌈log₂(k+1)⌉, ⌈log₂(s+1)⌉)`, for every `λ`,
every admissible instance, every outcome of the verifier's coins and every transcript within the
length bounds:

1. `|q₁| ≤ P`, and `|q₂| ≤ P` whenever `|a₁| ≤ P`;
2. the verifier rejects longer answers: if `Dec` accepts then `|a₁| ≤ P` and `|a₂| ≤ P`; and
   every answer of the honest prover (for any classical witness `y` and any view) has length
   at most `P`, so every message of an honest execution is bounded;
3. the online work (`V₂` and `Dec`, the computation "after preprocessing and generation of `q₁`")
   is at most `P`: on the inputs that occur for instances of the class `(t, k, s)`, each of `V₂`
   and `Dec` is computed, at every input length, by Boolean circuits of total size at most
   `p(λ, t, ⌈log₂(k+1)⌉, ⌈log₂(s+1)⌉)`.

**Formalization Note** Pinned-down version (operator request): `T` is replaced by
`t(X) = max_i t_L(x_i)`; `log(k+1)` is `⌈log₂(k+1)⌉`; work is circuit size (the published
`ComputedBySize` restricted to the inputs that occur, `ComputedOn`). Preprocessing (`Pre`, `V₁`) is
not bounded here; it is polynomial time by `Arg4.IsUniform`. -/
def Arg4.Succinct (A : Arg4) (F : QMAFamily) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ,
    (∀ (lam : ℕ) (u : Inst), u.Admissible → ∀ r : Bits, r.length = A.totalCoins lam u.size →
      let P := eval4 p lam (batchCost F u) (clog2 (u.k + 1)) (clog2 (u.s + 1))
      let m1 := A.firstMsg lam u.encode r
      let r2 := (A.coinParts lam u.size r).2.2
      m1.1.length ≤ P ∧
      (∀ a1 : Bits, a1.length ≤ P → (A.v2 lam m1.2 a1 r2).1.length ≤ P) ∧
      (∀ a1 a2 : Bits, A.dec lam (A.v2 lam m1.2 a1 r2).2 a2 = true →
        a1.length ≤ P ∧ a2.length ≤ P) ∧
      (∀ (y : Fin u.k → Bool) (j : ℕ) (v : Bits),
        (A.toVerifier lam u.encode (u.classicalWitness y) j v).length ≤ P)) ∧
    (∀ lam t k s n : ℕ,
      ComputedOn (A.v2Packed lam)
        (A.v2Inputs F lam t k s (eval4 p lam t (clog2 (k + 1)) (clog2 (s + 1)))) n
        (eval4 p lam t (clog2 (k + 1)) (clog2 (s + 1)))) ∧
    (∀ lam t k s n : ℕ,
      ComputedOn (A.decPacked lam)
        (A.decInputs F lam t k s (eval4 p lam t (clog2 (k + 1)) (clog2 (s + 1)))) n
        (eval4 p lam t (clog2 (k + 1)) (clog2 (s + 1))))

end FourMsgQMA


