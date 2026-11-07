-- Prove2me | Definitions.Def_ZKSheafPCP_PCPSys
-- name    : ZKSheafPCP_PCPSys
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:11:59.362283+00:00
-- url     : https://prove2.me/theorems/183a4a58-0ee6-46d6-bf53-5067506b8a9c
-- title:
--   PCP systems and black-box perfect zero knowledge
-- statement:
--   A **PCP system** over an alphabet of size $A$ with proof length $\ell$ consists of a prover $P$, mapping $(x,w)$ to a distribution on proofs, and a verifier machine $V$ with coin length $\rho$ and clock $\tau$. It **meets the parameters** $q,\varepsilon,b$ for a relation $R$ and a no-set $\mathrm{No}$ if:
--
--   1. $V$ is PPT with query complexity $q$: $\rho,\tau$ are polynomially bounded, and on every input, all coins and every proof, $V$ halts within $\tau(|x|)$ steps having read at most $q$ positions;
--   2. perfect completeness: for $(x,w)\in R$, every proof in the support of $P(x,w)$ and all coins, $V$ accepts;
--   3. soundness: for $x\in\mathrm{No}$ and every proof, $V$ accepts with probability at most $\varepsilon$;
--   4. black-box perfect zero knowledge with query bound $b$: there is one machine $S$, fixed before the malicious verifier, $x$, $w$ and $m$, running in time polynomial in $|x|+B+m$ on every oracle and all coins, such that for $(x,w)\in R$ and every $b$-query-bounded $V^*$ with $m$ coins the output law of $S^{V^*}$ equals the law of the code of $\mathrm{View}_{V^*,P}(x,w)$.
--
--   A verifier is **non-adaptive** if under fixed coins the positions it reads do not depend on the proof. It has **polynomial decision complexity** if a machine with no oracle computes its verdict from $x$, the coins and the symbols read, in time polynomial in $|x|$.
--
--   **Formalization Note** $S$ never sees $w$, since its oracle is $V^*$ alone. A PPT simulator is the case $B=0$. The parameters $A,\ell,q,\varepsilon,b$ are functions of an index $\mathrm{size}(x)$, which is $|x|$ except for the instances $(1^n,g)$ of Theorem 9.8.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definitions 3.24, 3.26, 3.28, pp.13–14; Lemma A.1, p.46

import Mathlib
import Definitions.Def_ZKSheafPCP_IsPolynomial
import Definitions.Def_ZKSheafPCP_MVerifier

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace ZKSheafPCP

open Classical

/-- A PCP system over a finite alphabet (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission, manuscript
sha256 ac5e528f…, Definition 3.24, p.13): a prover `P`, a verifier machine `V`, and `V`'s coin length `ρ` and
clock `τ`, both functions of `|x|`. The alphabet size `A` and the proof length `ℓ` are functions of `size x`.

**Formalization Note** `size x` is the index of the parameters. It is `|x|` for the PCPs of Theorems 9.1, 9.2
and Lemma A.1, and the `n` of the instance `(1ⁿ, g)` for Theorem 9.8. `P` is any `PMF`-valued function, with no
efficiency requirement, since Definition 3.24 calls efficiency of `P` an optional extra and Theorem 9.2 does
not claim it. -/
structure PCPSys (size : Str → ℕ) (A ℓ : ℕ → ℕ) where
  /-- the prover -/
  P : ∀ x _w : Str, PMF (Fin (ℓ (size x)) → Fin (A (size x)))
  /-- the verifier -/
  V : OTM
  /-- the verifier's coin length -/
  ρ : ℕ → ℕ
  /-- the verifier's clock -/
  τ : ℕ → ℕ

namespace PCPSys

variable {size : Str → ℕ} {A ℓ : ℕ → ℕ} (Sys : PCPSys size A ℓ)

/-- The verifier is PPT and has query complexity `q`: on every input, all coins and **every** proof, it halts
within `τ(|x|)` steps having read at most `q(size x)` distinct proof positions. -/
def Efficient (q : ℕ → ℕ) : Prop :=
  PolyBdd Sys.ρ ∧ PolyBdd Sys.τ ∧
  ∀ (x : Str) (r : Fin (Sys.ρ x.length) → Bool) (π : Fin (ℓ (size x)) → Fin (A (size x))),
    Sys.V.result (proofOracle π) (tup [x, coinStr r]) (Sys.τ x.length) ≠ none ∧
    (queriedPositions (ℓ (size x))
      (queryLog Sys.V (proofOracle π) (tup [x, coinStr r]) (Sys.τ x.length))).ncard ≤ q (size x)

/-- Perfect completeness (Definition 3.24, item 1): for `(x, w) ∈ R`, every proof in the support of `P(x, w)`
and all coins, the verifier accepts. -/
def Complete (R : Set (Str × Str)) : Prop :=
  ∀ x w, (x, w) ∈ R → ∀ π ∈ (Sys.P x w).support, ∀ r : Fin (Sys.ρ x.length) → Bool,
    Sys.V.result (proofOracle π) (tup [x, coinStr r]) (Sys.τ x.length) = some true

/-- Soundness error `ε` (Definition 3.24, item 2): for `x ∈ No` and every proof, the acceptance probability is
at most `ε(size x)`. `No` is `L(R)ᶜ`, or the no-language of a promise relation. -/
def Sound (No : Set Str) (ε : ℕ → ℝ) : Prop :=
  ∀ x ∈ No, ∀ π : Fin (ℓ (size x)) → Fin (A (size x)),
    acceptProb Sys.V (proofOracle π) x (Sys.ρ x.length) (Sys.τ x.length) ≤ ε (size x)

/-- Black-box perfect zero knowledge with query bound `b` (Definition 3.28, p.14). One machine `S` is fixed
before the malicious verifier, `x`, `w` and `m`. On every input, coin string and oracle it halts within
`θ(|x| + B(size x) + m)` steps. For every `(x, w) ∈ R`, every `m` and every `b(size x)`-query-bounded `V∗` with
`m` coins, the law of its output over uniform coins is exactly the law of the code of `View_{V∗,P}(x, w)`. Its
oracle is `V∗` alone, so it never sees `w`.

**Formalization Note** Definition 3.28 asks for a PPT `S`. For that, take `B = 0`, as in Theorems 9.1 and 9.2.
Theorem 9.8 inherits the time `poly(|x|, q∗)` of Definition 3.27 through `B`. -/
def PZK (R : Set (Str × Str)) (b B : ℕ → ℕ) : Prop :=
  ∃ (S : OTM) (σ θ : ℕ → ℕ), PolyBdd σ ∧ PolyBdd θ ∧
    (∀ (x : Str) (m : ℕ) (s : Fin (σ (x.length + B (size x) + m)) → Bool) (O : Oracle),
      S.result O (simInput x m s) (θ (x.length + B (size x) + m)) ≠ none) ∧
    ∀ x w, (x, w) ∈ R → ∀ (m : ℕ) (Vs : MVerifier m (Fin (ℓ (size x))) (A (size x))),
      Vs.Bounded (b (size x)) →
      (PMF.uniformOfFintype (Fin (σ (x.length + B (size x) + m)) → Bool)).map
          (fun s => S.output (Vs.oracle fun p => p.val) (simInput x m s)
            (θ (x.length + B (size x) + m))) =
        (Vs.viewLaw ((Sys.P x w).map fun π p => π p) (b (size x))).map viewCode

/-- The verifier is non-adaptive: under fixed coins, the set of proof positions it reads does not depend
on the proof (Lemma A.1, p.46). -/
def IsNonadaptive : Prop :=
  ∀ (x : Str) (r : Fin (Sys.ρ x.length) → Bool) (π π' : Fin (ℓ (size x)) → Fin (A (size x))),
    queriedPositions (ℓ (size x)) (queryLog Sys.V (proofOracle π) (tup [x, coinStr r]) (Sys.τ x.length)) =
    queriedPositions (ℓ (size x)) (queryLog Sys.V (proofOracle π') (tup [x, coinStr r]) (Sys.τ x.length))

/-- Polynomial decision complexity (Lemma A.1, p.46): a machine `D` with no oracle, given `x`, the coins and the
symbols at the read positions in increasing order, computes the verifier's verdict in time polynomial in `|x|`. -/
def DecisionPoly : Prop :=
  ∃ (D : OTM) (δ : ℕ → ℕ), PolyBdd δ ∧
    ∀ (x : Str) (r : Fin (Sys.ρ x.length) → Bool) (π : Fin (ℓ (size x)) → Fin (A (size x))),
      let log := queryLog Sys.V (proofOracle π) (tup [x, coinStr r]) (Sys.τ x.length)
      let ans := ((List.finRange (ℓ (size x))).filter
        (fun i => i ∈ queriedPositions (ℓ (size x)) log)).map fun i => binN (π i).val
      D.result (fun _ => false) (tup (x :: coinStr r :: ans)) (δ x.length) =
        Sys.V.result (proofOracle π) (tup [x, coinStr r]) (Sys.τ x.length)

/-- The system meets the parameters: alphabet `A`, length `ℓ`, query complexity `q`, soundness error `ε`, query
bound `b`, perfect completeness, for the relation `R` with no-set `No`. -/
def Meets (q : ℕ → ℕ) (ε : ℕ → ℝ) (b B : ℕ → ℕ) (R : Set (Str × Str)) (No : Set Str) : Prop :=
  Sys.Efficient q ∧ Sys.Complete R ∧ Sys.Sound No ε ∧ Sys.PZK R b B

end PCPSys

/-- A perfect zero-knowledge PCP system exists with these parameters, for the parameter index `size`. -/
def IsPZKPCPAt (size : Str → ℕ) (A ℓ q : ℕ → ℕ) (ε : ℕ → ℝ) (b B : ℕ → ℕ)
    (R : Set (Str × Str)) (No : Set Str) : Prop :=
  ∃ Sys : PCPSys size A ℓ, Sys.Meets q ε b B R No

end ZKSheafPCP


