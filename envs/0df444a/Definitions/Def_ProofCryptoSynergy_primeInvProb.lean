-- Prove2me | Definitions.Def_ProofCryptoSynergy_primeInvProb
-- name    : ProofCryptoSynergy_primeInvProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:57.758308+00:00
-- url     : https://prove2.me/theorems/fb0f7db3-2791-48ab-a51e-036ab7696f38
-- title:
--   The construction $\mathrm{Gen}'$, $\mathrm{Eval}'$, $\mathrm{Cert}$ of the proof of Theorem 39
-- statement:
--   Let $(\mathrm{Gen},\mathrm{Eval})$ be a keyed permutation with $s(\eta)$ coins, $L=\{(1^\eta,k):\exists r\ \mathrm{Gen}(1^\eta;r)=k\}$, and $\Pi=\Pi[\Psi]$ the proof system for $L$ obtained through a witness-preserving reduction $(f,g)$ of $L$ to SAT. Then $\mathrm{Gen}'_{\Pi,c}(1^\eta;r,r')=(k,\pi)$ with $k=\mathrm{Gen}(1^\eta;r)$ and $\pi=P[\Psi]((1^\eta,k),r,1^{\eta^c};r')$; $\mathrm{Eval}'_{\Pi,c}(1^\eta,(k,\pi),x)$ is $\mathrm{Eval}(1^\eta,k,x)$ if $V[\Psi]((1^\eta,k),\pi,1^{\eta^c})=1$ and $0$ otherwise; and $\mathrm{Cert}_{\Pi,c}(1^\eta,(k,\pi)):=V[\Psi]((1^\eta,k),\pi,1^{\eta^c})$. This item also defines the inversion probability of a circuit against this construction, the left side of eq. (2).
--
--   **Formalization Note** The number of prover coins may depend on $r$, so the probability is a nested average. The paper applies Definition 31 "for $L$"; the reduction $(f,g)$ makes that explicit.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), proof of Theorem 39, p.34 (PDF 36); eq. (2), p.35 (PDF 37)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_ProofCryptoSynergy_KeyedOWP
import Definitions.Def_ProofCryptoSynergy_provePsi

open LaconicBarrier QAdvFew.PoQOracle

namespace ProofCryptoSynergy

/-- The instance `(1^η, k)` of the language `L = {(1^η, k) : ∃r ∈ {0,1}^{s(η)} Gen(1^η; r) = k}` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), proof of Theorem 39,
p.34 (PDF 36)). -/
def keyInst (η : ℕ) (k : List Bool) : List Bool := tup [unary η, k]

/-- A polynomial-time **witness-preserving reduction** `(f, g)` of `L` to SAT: `f` maps instances to formulas and `g` maps
`(instance, witness)` to a satisfying assignment; a satisfiable image means the instance is in `L`.

**Formalization Note** Definition 31 is for SAT and the proof of Theorem 39 (p.34) applies it "for `L`", so the reduction is made explicit.
Cook–Levin supplies one, since `L ∈ NP`. -/
def IsWitnessReduction (W : KeyedOWP) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) : Prop :=
  PolyTimeOn (ι := List Bool) (fun x => [x]) f ∧
  PolyTimeOn (ι := List Bool × List Bool) (fun i => [i.1, i.2]) (fun i => g i.1 i.2) ∧
  (∀ (η : ℕ) (r : List Bool), r.length = W.s η →
    holds (f (keyInst η (W.gen η r))) (g (keyInst η (W.gen η r)) r)) ∧
  (∀ (η : ℕ) (k : List Bool), f (keyInst η k) ∈ SAT → ∃ r, r.length = W.s η ∧ W.gen η r = k)

/-- `Cert_{Π,c}(1^η, (k, π)) := V[Ψ]((1^η, k), π, 1^{η^c})` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), proof of Theorem 39, p.34 (PDF 36)). -/
def certPrime (N : NIWIScheme) (Ψ : ℕ → List Bool) (f : List Bool → List Bool) (c η : ℕ)
    (k π : List Bool) : Bool :=
  verifyPsi N Ψ (f (keyInst η k)) π (η ^ c)

/-- `Eval′_{Π,c}(1^η, (k, π), x)` is `Eval(1^η, k, x)` if `V[Ψ]((1^η, k), π, 1^{η^c}) = 1`, and `0` otherwise (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), proof of
Theorem 39, p.34 (PDF 36)). -/
def evalPrime (W : KeyedOWP) (N : NIWIScheme) (Ψ : ℕ → List Bool) (f : List Bool → List Bool)
    (c η : ℕ) (k π x : List Bool) : List Bool :=
  if certPrime N Ψ f c η k π = true then W.eval η k x else List.replicate (W.d η) false

/-- `Pr[C((k, π), Eval′_{Π,c}(1^η, (k, π), x)) = x]` over `(k, π) ← Gen′_{Π,c}(1^η)` and `x ← {0,1}^{d(η)}`, where
`Gen′_{Π,c}(1^η; r, r′) = (k, π)`, `k = Gen(1^η; r)`, `π = P[Ψ]((1^η, k), r, 1^{η^c}; r′)` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), proof of Theorem 39, p.34 (PDF 36);
eq. (2), p.35 (PDF 37)).

**Formalization Note** The number of prover coins `r′` may depend on `r`, so the probability is a nested average; `(k, π)` is the tuple code and is
followed by the image, which has the fixed length `d(η)`. -/
noncomputable def primeInvProb (W : KeyedOWP) (N : NIWIScheme) (Ψ : ℕ → List Bool)
    (f : List Bool → List Bool) (g : List Bool → List Bool → List Bool) (c η : ℕ) {m : ℕ}
    (C : MCircuit m) : ℝ :=
  coinAvg (W.s η) fun r =>
    let k := W.gen η (bits r)
    let inst := keyInst η k
    let wit := g inst (bits r)
    coinAvg (psiCoins N Ψ (f inst) wit (η ^ c)) fun r' =>
      let π := provePsi N Ψ (f inst) wit (η ^ c) (bits r')
      coinAvg (W.d η) fun x =>
        if C.eval (padIn m (tup [k, π] ++ evalPrime W N Ψ f c η k π (bits x))) = bits x
        then 1 else 0

end ProofCryptoSynergy


