-- Prove2me | Definitions.Def_ZKSheafPCP_PCPPFamily
-- name    : ZKSheafPCP_PCPPFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:13:24.439203+00:00
-- url     : https://prove2.me/theorems/a846f356-01ad-4969-a06a-9dd7953840e4
-- title:
--   Black-box $l$-local perfect zero-knowledge PCPs of proximity
-- statement:
--   A **pair language** is given by explicit inputs $i$ with string encodings, a block length $N_i$, an alphabet size $a_i$ and the set $L[i]$ of implicit inputs. A **black-box $l$-local perfect zero-knowledge PCP of proximity** with proof length $\ell$, query complexity $q$, soundness error $\varepsilon$, proximity parameter $\delta$ and query bound $b$ consists of a prover $P(i,y)$ and a verifier running in time polynomial in the length of the explicit input, with oracle access to the implicit input $y$ and a proof, such that:
--
--   1. the verifier reads at most $q_i$ distinct positions of $(y,\pi)$, on all coins and every $(y,\pi)$;
--   2. if $y\in L[i]$, it accepts every proof in the support of $P(i,y)$ on all coins;
--   3. if $y$ is $\delta_i$-far from $L[i]$, it accepts every proof with probability at most $\varepsilon_i$;
--   4. one simulator, running in time polynomial in $|i|+b_i+m$ with oracle access to $V^*$ and $y$, reads at most $b_i\,l_i$ distinct positions of $y$, and for $y\in L[i]$ and every $b_i$-query-bounded $V^*$ its output law equals the law of the view of $V^*$ on $(y,\pi)$ with $\pi\leftarrow P(i,y)$.
--
--   **Formalization Note** "$\delta$-far" means fractional Hamming distance at least $\delta$ from every element. Definition 3.25 does not say that the verifier is efficient; Theorem 9.8 needs it, so this is the stronger reading.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definitions 3.25, 3.26, 3.27, pp.13–14

import Mathlib
import Definitions.Def_ZKSheafPCP_PCPSys

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace ZKSheafPCP

open Classical

/-- A pair language for a PCP of proximity (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission, manuscript
sha256 ac5e528f…, Definition 3.25, p.13), as a family of explicit inputs `i` with their string encoding, block
length `N i`, alphabet size `a i`, and the set `L[x]` of implicit inputs. -/
structure PCPPFamily where
  /-- the explicit inputs -/
  Inst : Type
  /-- the encoding of an explicit input as a string -/
  enc : Inst → Str
  /-- the block length of the implicit input -/
  N : Inst → ℕ
  /-- the alphabet size -/
  a : Inst → ℕ
  /-- the set `L[x]` -/
  Lang : ∀ i, Set (Fin (N i) → Fin (a i))

/-- The verifier's oracle for an implicit input `y` and a proof `π`: a tag bit `false` reads `y`, a tag bit
`true` reads `π`. -/
noncomputable def pcppOracle {N ℓ a : ℕ} (y : Fin N → Fin a) (π : Fin ℓ → Fin a) : Oracle
  | [] => false
  | false :: q => proofOracle y q
  | true :: q => proofOracle π q

/-- The simulator's oracle: a tag bit `false` reads the implicit input `y`, a tag bit `true` reads the verifier. -/
noncomputable def pcppSimOracle {N a : ℕ} (y : Fin N → Fin a) (Ov : Oracle) : Oracle
  | [] => false
  | false :: q => proofOracle y q
  | true :: q => Ov q

/-- The positions of the implicit input read in a log of tagged queries. -/
def inputPositions (N : ℕ) (log : List Str) : Set (Fin N) :=
  queriedPositions N (log.filterMap fun q =>
    match q with
    | false :: q' => some q'
    | _ => none)

/-- The positions of the proof read in a log of tagged queries. -/
def proofPositions (ℓ : ℕ) (log : List Str) : Set (Fin ℓ) :=
  queriedPositions ℓ (log.filterMap fun q =>
    match q with
    | true :: q' => some q'
    | _ => none)

/-- The code of a query to the implicit input or the proof, for the simulator's reading of `V∗`. -/
def sumCode {N ℓ : ℕ} : Fin N ⊕ Fin ℓ → ℕ
  | Sum.inl i => 2 * i.val
  | Sum.inr j => 2 * j.val + 1

/-- `y` is `δ`-far from a set of words: its fractional Hamming distance from every element is at least `δ`
(Definitions 3.25, p.14). The set may be empty, in which case every word is far. -/
def IsFar {N a : ℕ} (δ : ℝ) (y : Fin N → Fin a) (C : Set (Fin N → Fin a)) : Prop :=
  ∀ c ∈ C, δ * N ≤ ((Finset.univ.filter fun i => y i ≠ c i).card : ℝ)

/-- A black-box `l`-local perfect zero-knowledge PCP of proximity with proof length `ℓ`, query complexity `q`,
soundness error `ε`, proximity parameter `δ` and query bound `b` (Definitions 3.25–3.27, pp.13–14).

The verifier runs in time polynomial in the length of the explicit input, with at most `q i` distinct positions of
`y` and of the proof, on all coins and all `(y, π)`. Completeness holds for `y ∈ L[x]`, soundness for `δ`-far `y`
and every proof. One simulator `S` is fixed first. It runs in time `poly(|x|, b, m)` on every oracle, reads at most
`b i * l i` distinct positions of `y` under every malicious verifier, and its output law equals that of the view
of the verifier on `(y, π)`, `π ← P(x, y)`.

**Formalization Note** Definition 3.25 does not say the verifier is efficient, but Theorem 9.8 needs it; this is the
stronger reading. The clause on `S`'s reads of `y` is required for `y ∈ L[x]`, as in Definition 3.27. -/
def IsPZKPCPP (Φ : PCPPFamily) (ℓ q : Φ.Inst → ℕ) (ε δ : Φ.Inst → ℝ) (b l : Φ.Inst → ℕ) : Prop :=
  ∃ (P : ∀ i, (Fin (Φ.N i) → Fin (Φ.a i)) → PMF (Fin (ℓ i) → Fin (Φ.a i)))
    (V : OTM) (ρ τ : ℕ → ℕ),
    PolyBdd ρ ∧ PolyBdd τ ∧
    (∀ (i : Φ.Inst) (r : Fin (ρ (Φ.enc i).length) → Bool) (y : Fin (Φ.N i) → Fin (Φ.a i))
      (π : Fin (ℓ i) → Fin (Φ.a i)),
      let O := pcppOracle y π
      let log := queryLog V O (tup [Φ.enc i, coinStr r]) (τ (Φ.enc i).length)
      V.result O (tup [Φ.enc i, coinStr r]) (τ (Φ.enc i).length) ≠ none ∧
      (inputPositions (Φ.N i) log).ncard + (proofPositions (ℓ i) log).ncard ≤ q i) ∧
    (∀ (i : Φ.Inst), ∀ y ∈ Φ.Lang i, ∀ π ∈ (P i y).support, ∀ r : Fin (ρ (Φ.enc i).length) → Bool,
      V.result (pcppOracle y π) (tup [Φ.enc i, coinStr r]) (τ (Φ.enc i).length) = some true) ∧
    (∀ (i : Φ.Inst) (y : Fin (Φ.N i) → Fin (Φ.a i)), IsFar (δ i) y (Φ.Lang i) →
      ∀ π : Fin (ℓ i) → Fin (Φ.a i),
        acceptProb V (pcppOracle y π) (Φ.enc i) (ρ (Φ.enc i).length) (τ (Φ.enc i).length) ≤ ε i) ∧
    ∃ (S : OTM) (σ θ : ℕ → ℕ), PolyBdd σ ∧ PolyBdd θ ∧
      (∀ (i : Φ.Inst) (m : ℕ) (s : Fin (σ ((Φ.enc i).length + b i + m)) → Bool) (O : Oracle),
        S.result O (simInput (Φ.enc i) m s) (θ ((Φ.enc i).length + b i + m)) ≠ none) ∧
      ∀ (i : Φ.Inst), ∀ y ∈ Φ.Lang i, ∀ (m : ℕ) (Vs : MVerifier m (Fin (Φ.N i) ⊕ Fin (ℓ i)) (Φ.a i)),
        Vs.Bounded (b i) →
        (PMF.uniformOfFintype (Fin (σ ((Φ.enc i).length + b i + m)) → Bool)).map
            (fun s => S.output (pcppSimOracle y (Vs.oracle sumCode)) (simInput (Φ.enc i) m s)
              (θ ((Φ.enc i).length + b i + m))) =
          (Vs.viewLaw ((P i y).map fun π => Sum.elim y π) (b i)).map viewCode ∧
        ∀ s : Fin (σ ((Φ.enc i).length + b i + m)) → Bool,
          (inputPositions (Φ.N i) (queryLog S (pcppSimOracle y (Vs.oracle sumCode))
            (simInput (Φ.enc i) m s) (θ ((Φ.enc i).length + b i + m)))).ncard ≤ b i * l i

end ZKSheafPCP


