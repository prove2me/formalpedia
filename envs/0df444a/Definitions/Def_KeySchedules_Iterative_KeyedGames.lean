-- Prove2me | Definitions.Def_KeySchedules_Iterative_KeyedGames
-- name    : KeySchedules_Iterative_KeyedGames
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:50:55.200444+00:00
-- url     : https://prove2.me/theorems/077eadbb-5f55-45c4-89de-2954563aa468
-- title:
--   Keyed games, key schedules E∘H, the key as auxiliary information, 𝒯_q, the expectation-method hypotheses and Δ_E
-- statement:
--   The security game of a **keyed construction** $\mathcal E$ with nonempty finite key space $K$ (Definition 2.1) is given by its ideal system $S_0$ (probabilities $p_0$) and, for every key $k$, the real system conditioned on the key $k$ (probabilities $p_1^k$). The real system samples $k$ uniformly once, so its transcript probabilities are $\frac1{|K|}\sum_k p_1^k(\tau)$, and $\mathrm{Adv}_{\mathcal E}(\mathcal A)=\mathrm{Adv}^{(S_0,S_1)}(\mathcal A)$.
--
--   A **key schedule** is a map $H:K'\to K$ from a nonempty finite master-key space; the game of $\mathcal E\circ H$ has the same ideal system and the conditional real systems $(\mathcal E\circ H)_{k'}=\mathcal E_{H(k')}$, with $k'$ uniform in $K'$.
--
--   With the **key as auxiliary information** the transcripts are pairs $(\bar\tau,k)$ and
--   $$p_1(\bar\tau,k)=\frac{p_1^k(\bar\tau)}{|K|},\qquad p_0(\bar\tau,k)=\frac{p_0(\bar\tau)}{|K|}$$
--   (an independent uniform dummy key in the ideal world). $\mathcal T_q$ is the set of query-response transcripts attainable in the ideal world ($p_0(\bar\tau)>0$) with at most $q$ queries to each oracle, of every length. The **hypotheses of Lemma 2.1 on $\mathcal T_q\times K$** with data $(\mathcal T_{\mathrm{bad}},g)$ say: for every $(\bar\tau,k)$ with $\bar\tau$ within $q$ queries and $p_0(\bar\tau,k)>0$, $g(\bar\tau,k)\ge0$, and if $(\bar\tau,k)\notin\mathcal T_{\mathrm{bad}}$ then $(1-g(\bar\tau,k))\,p_0(\bar\tau,k)\le p_1(\bar\tau,k)$. Then
--   $$\Delta_{\mathcal E}(\mathcal A)=\mathbb E\bigl[g^\star(\bar\Theta_0,k)\bigr],$$
--   with $\bar\Theta_0$ the ideal query-response transcript of $\mathcal A$ and $k$ uniform in $K$ independent of it.
--
--   **Formalization Note.** The ratio condition is written multiplicatively; $\Delta_{\mathcal E}$ depends on the data $(\mathcal T_{\mathrm{bad}},g)$, which the statements fix once by hypothesis.
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 7, Definition 2.1, Key Schedules, Eq. (1); p. 8, Lemma 2.1; p. 9, the setting of Theorem 3.1 (𝒯_q, the key as auxiliary information)

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Oracles

namespace KeySchedules.Iterative

/-!
# Keyed games, key schedules, the key as auxiliary information, `𝒯_q`, `Δ_ℰ`

Beierle, Choi, Hhan, Jha, Kim, *Minimizing Key Schedules for Key-Alternating Ciphers*,
STOC 2027 submission (manuscript sha256 cd9f815b…), Definition 2.1 and "Key Schedules" (p. 7),
Eq. (1) and the sentence after it (p. 7), Lemma 2.1 (p. 8), and the setting of Theorem 3.1
(p. 9): the secret key as auxiliary information, `𝒯_q`, the hypotheses of Lemma 2.1 on
`𝒯_q × K`.

* The security game of a keyed construction `ℰ` with key space `K` is given by its ideal system
  `S_0` and, for every key `k`, the real system conditioned on the key `k`. The real system
  samples `k` uniformly once and runs the conditional system of `k`.
* For a key schedule `H : K' → K`, the game of `ℰ ∘ H` has the same ideal system and the
  conditional real systems of the keys `H(k')`, with `k'` uniform in `K'`.
* With the key appended as auxiliary information, the transcript probabilities are
  `p_1(τ̄, k) = p_1^k(τ̄)/|K|` and `p_0(τ̄, k) = p_0(τ̄)/|K|` (an independent uniform dummy key
  in the ideal world).
-/

/-- The security game of a keyed construction with key space `K`: the ideal system and, for
every key `k`, the real system conditioned on the key `k`. -/
structure KeyedGame (I : Interface) (K : Type) where
  ideal : System I
  real : K → System I

/-- The transcript probabilities of the real system: the key is uniform in `K`. -/
noncomputable def KeyedGame.realProb {I : Interface} {K : Type} [Fintype K]
    (E : KeyedGame I K) : Transcript I → ℝ :=
  fun τ => (Fintype.card K : ℝ)⁻¹ * ∑ k : K, (E.real k).prob τ

/-- `Adv_ℰ(A) = Adv^{(S0,S1)}(A)` for the real and ideal systems of the game of `ℰ`. -/
noncomputable def KeyedGame.adv {I : Interface} {K : Type} [Fintype K]
    (E : KeyedGame I K) (A : Adversary I) : ℝ :=
  advantage E.ideal.prob E.realProb A

/-- The game of `ℰ ∘ H` for a key schedule `H : K' → K`: `(ℰ ∘ H)_{k'} = ℰ_{H(k')}`, with the
same ideal system. -/
def KeyedGame.comp {I : Interface} {K K' : Type} (E : KeyedGame I K) (H : K' → K) :
    KeyedGame I K' where
  ideal := E.ideal
  real := fun k' => E.real (H k')

/-- Ideal transcript probabilities with the key as auxiliary information:
`p_0(τ̄, k) = p_0(τ̄)/|K|` (independent uniform dummy key). -/
noncomputable def KeyedGame.idealAux {I : Interface} {K : Type} [Fintype K]
    (E : KeyedGame I K) : Transcript I → K → ℝ :=
  fun τ _ => (Fintype.card K : ℝ)⁻¹ * E.ideal.prob τ

/-- Real transcript probabilities with the key as auxiliary information:
`p_1(τ̄, k) = p_1^k(τ̄)/|K|`. -/
noncomputable def KeyedGame.realAux {I : Interface} {K : Type} [Fintype K]
    (E : KeyedGame I K) : Transcript I → K → ℝ :=
  fun τ k => (Fintype.card K : ℝ)⁻¹ * (E.real k).prob τ

/-- `𝒯_q`: the query-response transcripts attainable in the ideal world (`p_0(τ̄) > 0`) with at
most `q` queries to each oracle (of every length, the empty transcript included). -/
def Tq {I : Interface} (S0 : System I) (q : ℕ) : Set (Transcript I) :=
  {τ | 0 < S0.prob τ ∧ WithinQueries τ q}

/-- The hypotheses of Lemma 2.1 on `𝒯_q × K` with the key as auxiliary information: for every
attainable `(τ̄, k)` with `τ̄` having at most `q` queries per oracle, `g(τ̄, k) ≥ 0`, and if
`(τ̄, k) ∉ 𝒯_bad` then `p_1(τ̄, k)/p_0(τ̄, k) ≥ 1 − g(τ̄, k)` (written multiplicatively). -/
def KeyedGame.IsExpCert {I : Interface} {K : Type} [Fintype K] (E : KeyedGame I K) (q : ℕ)
    (bad : Set (Transcript I × K)) (g : Transcript I × K → ℝ) : Prop :=
  ∀ (τ : Transcript I) (k : K), WithinQueries τ q → 0 < E.idealAux τ k →
    0 ≤ g (τ, k) ∧ ((τ, k) ∉ bad → (1 - g (τ, k)) * E.idealAux τ k ≤ E.realAux τ k)

/-- `Δ_ℰ(A) = E[g★(Θ̄_0, k)]`: `Θ̄_0` the ideal query-response transcript of `A`, `k` uniform in
`K` and independent of it (Lemma 2.1 with the key as auxiliary information). -/
noncomputable def KeyedGame.delta {I : Interface} {K : Type} [Fintype K] (E : KeyedGame I K)
    (bad : Set (Transcript I × K)) (g : Transcript I × K → ℝ) (A : Adversary I) : ℝ :=
  A.sumComplete (fun τ => ∑ k : K, E.idealAux τ k * gStar bad g (τ, k))

end KeySchedules.Iterative


