-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_RampScheme
-- name    : RLCDiscrepancy_Supplement_RampScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:48:59.061569+00:00
-- url     : https://prove2.me/theorems/c5e5f7ca-7894-4eca-9f30-12553869ec49
-- title:
--   Secret sharing scheme and $(n,t_{\mathrm{rec}},t_{\mathrm{priv}})$-ramp scheme
-- statement:
--   A **secret sharing scheme** for $n$ parties with secrets and shares in $\mathbb F_q$ is a pair $(\mathrm{Share},\mathrm{Rec})$: $\mathrm{Share}$ is randomized, mapping a secret $s$ and uniformly random coins $\omega\in\Omega$ to a share vector $(S_1,\dots,S_n)$; $\mathrm{Rec}$ is deterministic and receives a set $T\subseteq[n]$ and only the shares $(S_i)_{i\in T}$.
--
--   It is an **$(n,t_{\mathrm{rec}},t_{\mathrm{priv}})$-ramp scheme** if
--
--   1. (Privacy) for every $T$ with $|T|\le t_{\mathrm{priv}}$ and all secrets $s,s'$, the shares $\mathrm{Share}_T(s)$ and $\mathrm{Share}_T(s')$ of the parties in $T$ are identically distributed;
--   2. (Reconstruction) for every $T$ with $|T|\ge t_{\mathrm{rec}}$ and every secret $s$, $\Pr[\mathrm{Rec}(\mathrm{Share}(s)_T,T)=s]=1$.
--
--   These are the objects of Theorems 6.5 and 6.14.
--
--   **Formalization Note** The coins are uniform on a finite type $\Omega$; probability one over uniform coins is stated as "for every coin outcome", which is equivalent when $\Omega$ is nonempty. Identical distribution is equality of the probability of every value.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.1, pp.44–45

import Mathlib
import Definitions.Def_PunctSketch_coinProb

namespace RLCDiscrepancy.Supplement

/-- A **secret sharing scheme** (Share, Rec) for n parties with secrets and shares in `F`
(§6, Definition 6.1). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.1, pp.44–45: "a pair of algorithms (Share, Rec) with Share a
randomized algorithm that receives as input a secret s ∈ S and outputs a share S_i for the i-th
party, i ∈ [n], and Rec a deterministic algorithm that receives a subset T ⊆ [n] of parties and the
shares (S_i)_{i∈T} corresponding to parties in T and outputs a guess for the secret".

**Formalization Note.** Share's randomness is a coin `ω : Ω` drawn uniformly from a finite coin
space (the hypotheses `Fintype Ω`, `Nonempty Ω` are imposed where the scheme is used). Rec receives
only `T` and the shares of the parties in `T` (a function `T → F`), so it cannot read other shares. -/
structure RampScheme (F : Type*) (n : ℕ) (Ω : Type*) where
  /-- Share(s) with coins ω: the vector of the n shares. -/
  share : F → Ω → (Fin n → F)
  /-- Rec(T, (S_i)_{i∈T}). -/
  reconstruct : (T : Finset (Fin n)) → (T → F) → F

/-- **(n, t_rec, t_priv)-ramp secret sharing scheme** (Definition 6.1). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.1,
pp.44–45:
"• Privacy: For any subset T ⊆ [n] such that |T| ≤ t_priv and any two secrets s, s′ ∈ S, the random
variables Share_T(s) and Share_T(s′) … are identically distributed.
• Reconstruction: For any subset T ⊆ [n] such that |T| ≥ t_rec and any secret s ∈ S we have
Pr[Rec(Share(s)_T, T) = s] = 1, with the probability taken over the random coins of Share."

**Formalization Note.** "Identically distributed" is equality of the probabilities of every value
`y : T → F` under uniform coins (`PunctSketch.coinProb`). "Probability 1 over the coins" is "for
every coin outcome", which is equivalent for uniform coins on a nonempty finite `Ω`. -/
def RampScheme.IsRamp {F : Type*} {n : ℕ} {Ω : Type*} [Fintype Ω] (P : RampScheme F n Ω)
    (tRec tPriv : ℕ) : Prop :=
  (∀ T : Finset (Fin n), T.card ≤ tPriv → ∀ (s s' : F) (y : T → F),
      PunctSketch.coinProb (fun ω => (fun i : T => P.share s ω i) = y) =
        PunctSketch.coinProb (fun ω => (fun i : T => P.share s' ω i) = y)) ∧
  (∀ T : Finset (Fin n), tRec ≤ T.card → ∀ (s : F) (ω : Ω),
      P.reconstruct T (fun i : T => P.share s ω i) = s)

end RLCDiscrepancy.Supplement


