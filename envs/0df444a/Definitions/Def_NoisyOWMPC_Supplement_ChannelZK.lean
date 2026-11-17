-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_ChannelZK
-- name    : NoisyOWMPC_Supplement_ChannelZK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:00:58.988639+00:00
-- url     : https://prove2.me/theorems/bc3e68fb-7f91-44f1-a35a-a359299329d4
-- title:
--   Channel zero-knowledge proofs of knowledge (Definition E.5)
-- statement:
--   Let $C : \mathcal X \to \mathcal Y$ be a channel and $R$ an NP relation on statements $z \in \{0,1\}^{L(\lambda)}$ and witnesses $w$. A **channel zero-knowledge proof of knowledge** for $R$ over $C$ uses $n_{\mathrm{ZK}}$ channel uses and consists of a randomized prover $P_{\mathrm{ZK}}(1^\lambda, z, w) \to \hat x \in \mathcal X^{n_{\mathrm{ZK}}}$ and a deterministic verifier $V_{\mathrm{ZK}}(1^\lambda, z, \hat y) \in \{0,1\}$, with polynomial channel-use count and running times, such that:
--
--   1. **Completeness.** For a negligible $\nu$, every $(z, w)$ with $R(z, w) = 1$ satisfies $\Pr[V_{\mathrm{ZK}}(1^\lambda, z, C^{n_{\mathrm{ZK}}}(P_{\mathrm{ZK}}(1^\lambda, z, w))) = 1] \ge 1 - \nu(\lambda)$.
--   2. **Knowledge soundness.** There is a PPT extractor $\mathrm{Ext_{ZK}}(1^\lambda, z, \hat x) \to w \in \{0,1\}^* \cup \{\mathsf{fail}\}$ such that, for every statement $z$ and word $\hat x$,
--   $$
--   \Big|\Pr\big[V_{\mathrm{ZK}}(1^\lambda, z, C^{n_{\mathrm{ZK}}}(\hat x)) = 1\big] - \Pr\big[R(z, \mathrm{Ext_{ZK}}(1^\lambda, z, \hat x)) = 1\big]\Big| \le \nu(\lambda)
--   $$
--   for a negligible $\nu$, with $R(z, \mathsf{fail}) = 0$.
--   3. **Zero knowledge.** There is a PPT simulator with $C^{n_{\mathrm{ZK}}}(P_{\mathrm{ZK}}(1^\lambda, z, w)) \approx^c \mathrm{Sim_{ZK}}(1^\lambda, z)$ for every $(z, w)$ with $R(z, w) = 1$.
--
--   Construction E.8 certifies its broadcast program with such a proof for the relation $R_{\mathrm{cert}}$.
--
--   **Formalization Note** In Construction E.8 the statements have a fixed public length $L(\lambda)$, so $n_{\mathrm{ZK}}$ is a function of $\lambda$; the prover's coin count depends on $\lambda$ only. All negligible bounds are uniform over the statements, witnesses and words.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition E.5, p.62; Theorem E.6 (polynomial channel uses and running times), p.62

import Mathlib
import Definitions.Def_NoisyOWMPC_Supplement_WiretapScheme
import Definitions.Def_NoisyOWMPC_CompClose

namespace NoisyOWMPC.Supplement

open LaconicBarrier

/-- The syntax of a **channel zero-knowledge proof** over a channel with input alphabet `X` and
output alphabet `Yc`, for statements `z ∈ {0,1}^{L(λ)}` (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Definition E.5, p.62): `n_ZK` channel uses,
* `P_ZK(1^λ, z, w; ρ) → x̂ ∈ X^{n_ZK}`, the randomized prover with `coins λ` uniform coins;
* `V_ZK(1^λ, z, ŷ) ∈ {0,1}`, the deterministic verifier on observations `ŷ ∈ Yc^{n_ZK}`.

**Formalization Note** In Construction E.8 (p.64) the statements have "the resulting fixed public
length" `L(λ)`, so `n_ZK(λ, |z|)` is a function of `λ`; the prover's coin count depends on `λ`
only (a prover with fewer coins ignores the extra ones). Witnesses are bit strings. -/
structure ChannelZK (X Yc : Type) (L : ℕ → ℕ) where
  /-- the number `n_ZK` of channel uses -/
  nZK : ℕ → ℕ
  /-- the number of prover coins -/
  coins : ℕ → ℕ
  /-- the prover `P_ZK(1^λ, z, w; ρ)` -/
  prove : (lam : ℕ) → (Fin (L lam) → Bool) → List Bool → (Fin (coins lam) → Bool) →
    Fin (nZK lam) → X
  /-- the verifier `V_ZK(1^λ, z, ŷ)` -/
  verify : (lam : ℕ) → (Fin (L lam) → Bool) → (Fin (nZK lam) → Yc) → Bool

/-- The relation `R(z, w)` evaluated on an extractor output: `1w` is the witness `w`; every other
string, in particular `0`, is `fail`, with `R(z, fail) = 0` (Definition E.5, p.62). -/
def extOK {L : ℕ → ℕ} (R : (lam : ℕ) → (Fin (L lam) → Bool) → List Bool → Prop) (lam : ℕ)
    (z : Fin (L lam) → Bool) : List Bool → Prop
  | true :: w => R lam z w
  | _ => False

variable {X Yc : Type} [Fintype X] [Fintype Yc] {L : ℕ → ℕ}

/-- `Z` is a **channel zero-knowledge proof of knowledge for the NP relation `R` over `C`**
(Definition E.5, p.62), with polynomial channel-use count and running times (Theorem E.6, p.62:
"with channel-use count and running times polynomial in the security parameter and the statement
length"):
1. `n_ZK` and the prover's coins are polynomially bounded, `P_ZK` and `V_ZK` run in polynomial time;
2. *completeness*: there is a negligible `ν` with
   `Pr[V_ZK(1^λ, z, C^{n_ZK}(P_ZK(1^λ, z, w))) = 1] ≥ 1 − ν(λ)` for every `(z, w)` with `R(z, w)`;
3. *knowledge soundness* (E.4): a PPT extractor `Ext_ZK(1^λ, z, x̂)` and a negligible `ν` with
   `|Pr[V_ZK(1^λ, z, C^{n_ZK}(x̂)) = 1] − Pr[R(z, Ext_ZK(1^λ, z, x̂)) = 1]| ≤ ν(λ)` for every statement
   `z` and word `x̂ ∈ X^{n_ZK}`;
4. *zero knowledge*: a PPT simulator `Sim_ZK(1^λ, z)` with
   `C^{n_ZK}(P_ZK(1^λ, z, w)) ≈^c Sim_ZK(1^λ, z)` for every `(z, w)` with `R(z, w)`.

**Formalization Note** The two sides of (E.4) "are bits in separate experiments, so the requirement
says that their acceptance probabilities differ negligibly" (p.62), uniformly over `(z, x̂)` (§3,
p.15). The simulator's output string is compared with the encoding of the observation. -/
def ChannelZK.IsZKPoK (C : DMC X Yc) (R : (lam : ℕ) → (Fin (L lam) → Bool) → List Bool → Prop)
    (Z : ChannelZK X Yc L) : Prop :=
  PolyBounded Z.nZK ∧ PolyBounded Z.coins ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (L lam) → Bool) × List Bool × (Fin (Z.coins lam) → Bool))
    (fun q => [unary q.1, bits q.2.1, q.2.2.1, bits q.2.2.2])
    (fun q => wordEnc X (Z.prove q.1 q.2.1 q.2.2.1 q.2.2.2)) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (L lam) → Bool) × (Fin (Z.nZK lam) → Yc))
    (fun q => [unary q.1, bits q.2.1, wordEnc Yc q.2.2]) (fun q => [Z.verify q.1 q.2.1 q.2.2]) ∧
  (∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam (z : Fin (L lam) → Bool) (w : List Bool), R lam z w →
    1 - ν lam ≤ wprob (fun ω : (Fin (Z.coins lam) → Bool) × (Fin (Z.nZK lam) → Yc) =>
        (1 / 2 : ℝ) ^ (Z.coins lam) * chanW C (Z.prove lam z w ω.1) ω.2)
      (fun ω => Z.verify lam z ω.2 = true)) ∧
  (∃ Ext : CoinAlg, Ext.IsPPT ∧ ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ lam (z : Fin (L lam) → Bool) (xh : Fin (Z.nZK lam) → X),
      |wprob (fun y : Fin (Z.nZK lam) → Yc => chanW C xh y) (fun y => Z.verify lam z y = true) -
        wprob (unifW (Fin (Ext.coins lam) → Bool))
          (fun σ => extOK R lam z (Ext.run lam (QAdvFew.PoQOracle.tup [bits z, wordEnc X xh]) σ))| ≤
        ν lam) ∧
  ∃ Sim : CoinAlg, Sim.IsPPT ∧
    CompClose (I := fun lam => {q : (Fin (L lam) → Bool) × List Bool // R lam q.1 q.2})
      (fun lam q (ω : (Fin (Z.coins lam) → Bool) × (Fin (Z.nZK lam) → Yc)) =>
        (1 / 2 : ℝ) ^ (Z.coins lam) * chanW C (Z.prove lam q.1.1 q.1.2 ω.1) ω.2)
      (fun _ _ ω => wordEnc Yc ω.2)
      (fun lam _ => unifW (Fin (Sim.coins lam) → Bool))
      (fun lam q σ => Sim.run lam (bits q.1.1) σ) (fun _ => 0)

end NoisyOWMPC.Supplement


