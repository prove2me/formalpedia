-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_Verifiable
-- name    : NoisyOWMPC_Supplement_Verifiable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:00:15.765195+00:00
-- url     : https://prove2.me/theorems/22fdda20-1486-40d3-bc3c-9f8e5b5e03fa
-- title:
--   Verifiable release tests and verifiable selectors (Definitions E.3, E.4)
-- statement:
--   Let $C : \mathcal X \to \mathcal Y$ be a channel, viewed as a product broadcast channel with one receiver.
--
--   A **verifiable release test with errors $(\eta, \delta_{\mathrm{rel}}, \delta_{\mathrm{send}})$** is a recoverable release test for the single receiver of $C$ (Definition 5.3 with $k = 1$) with channel-input length $n$ and errors $(\eta, \delta_{\mathrm{rel}})$, together with a deterministic polynomial-time algorithm $\mathrm{Valid_{rel}}(\Theta) \in \{0,1\}$ such that
--
--   1. every $\Theta$ in the support of $\mathrm{Gen}(1^\lambda)$ is valid, and
--   2. for every valid $\Theta$ and every word $X \in \mathcal X^n$, not necessarily $\mathrm{Word}(\Theta)$,
--   $$
--   \Pr\big[Q_\Theta(D) = 1\big] \le \tfrac12 + \delta_{\mathrm{send}}, \qquad D \leftarrow C^n(X).
--   $$
--
--   A **verifiable selector on $[N]$ with input-bias bound $\delta_{\mathrm{send}} \ge 0$ and errors $(\alpha_{\mathrm{sel}}, \beta_{\mathrm{sel}}, \delta_{\mathrm{sel}})$** is a recoverable selector with errors $(\alpha_{\mathrm{sel}}, \delta_{\mathrm{sel}})$ together with a deterministic polynomial-time algorithm $\mathrm{Valid_{sel}}(K)$ such that every key in the support of $\mathrm{Gen_{sel}}$ is valid and, for every valid $K$, every random set $U \subseteq [N]$ with independent inclusion indicators and $\Pr[v \in U] \le \tfrac12 + \delta_{\mathrm{send}}$ for every $v$, and every $c \in \{0,1\}$,
--   $$
--   \Big|\Pr\big[\mathrm{Guard_{sel}}(U) = 1,\ b_K(U) = c\big] - \tfrac12 \Pr\big[\mathrm{Guard_{sel}}(U) = 1\big]\Big| \le \beta_{\mathrm{sel}}.
--   $$
--
--   These strengthen the release-test and selector interfaces of the main construction against a sender that hardwires arbitrary valid states and transmits arbitrary words.
--
--   **Formalization Note** States and keys are typed and given to the validity algorithms by their published encodings; strings encoding no state are rejected by the certification relation of Construction E.8. The inclusion probabilities may depend on the key.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definitions E.3 and E.4, p.61

import Mathlib
import Definitions.Def_NoisyOWMPC_ChannelTest
import Definitions.Def_NoisyOWMPC_Selector

namespace NoisyOWMPC.Supplement

open LaconicBarrier

/-- The output alphabets of a single-receiver channel (`k = 1`; Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), App. E, p.60: "We consider the single-receiver setting,
`k = 1`"). -/
abbrev oneY (Yc : Type) : Fin 1 → Type := fun _ => Yc

instance oneY.instFintype (Yc : Type) [Fintype Yc] (i : Fin 1) : Fintype (oneY Yc i) :=
  (inferInstance : Fintype Yc)

/-- A channel `C : X → Y` as a product broadcast channel with one receiver. -/
def oneC {X Yc : Type} [Fintype Yc] (C : DMC X Yc) : ∀ i : Fin 1, DMC X (oneY Yc i) := fun _ => C

/-- A **verifiable release test** (STOC 2027 submission (manuscript sha256 3a9569fa…),
Definition E.3, p.61): a release test for the single receiver of `C` (a published `ChannelTest`
with `k = 1`, observers `[1]`, channel-input length `n`) together with a deterministic algorithm
`Valid_rel(Θ) ∈ {0,1}` on secret states. -/
structure VerReleaseTest (X Yc : Type) [Fintype Yc] (n : ℕ → ℕ) extends
    ChannelTest 1 X (oneY Yc) 0 n Finset.univ where
  /-- `Valid_rel(Θ)` -/
  valid : (lam : ℕ) → Sec lam → Bool

variable {X Yc : Type} [Fintype X] [Fintype Yc]

/-- `T` is a **verifiable release test with errors `(η, δ_rel, δ_send)`** for `C` (Definition E.3,
p.61):
1. a recoverable release test with errors `(η, δ_rel)` (Definition 5.3 with `k = 1`, the published
   `IsRecRelease`);
2. `Valid_rel` is deterministic polynomial time;
3. *validity*: every `Θ` in the support of `Gen(1^λ)` has `Valid_rel(Θ) = 1`;
4. *acceptance upper bound* (E.2): for every `Θ` with `Valid_rel(Θ) = 1` and every word `X ∈ Xⁿ`
   (not necessarily `Word(Θ)`), `Pr[Q_Θ(D) = 1] ≤ 1/2 + δ_send` for `D ← Cⁿ(X)`.

**Formalization Note** States are typed (`Sec λ`) and given to `Valid_rel` by their published
encoding, so "returns zero on malformed encodings" concerns strings that encode no state, which the
certification relation of App. E rejects. -/
def VerReleaseTest.IsVerRelease {n : ℕ → ℕ} (C : DMC X Yc) (T : VerReleaseTest X Yc n)
    (η δrel δsend : ℕ → ℝ) : Prop :=
  T.toChannelTest.IsRecRelease (oneC C) η δrel ∧
  PolyTimeOn (ι := (lam : ℕ) × T.Sec lam) (fun z => [unary z.1, T.enc z.1 z.2])
    (fun z => [T.valid z.1 z.2]) ∧
  (∀ lam Θ, T.genW lam Θ ≠ 0 → T.valid lam Θ = true) ∧
  ∀ lam Θ, T.valid lam Θ = true → ∀ w : Fin (n lam) → X,
    ∑ d : Fin (n lam) → Yc, (∏ s, C.P (w s) (d s)) * (if T.test lam Θ d then 1 else 0) ≤
      1 / 2 + δsend lam

/-- A **verifiable selector on `[N]`** (Definition E.4, p.61): a selector (published `Selector`)
together with a deterministic algorithm `Valid_sel(K) ∈ {0,1}` on keys. -/
structure VerSelector (N : ℕ → ℕ) extends Selector N where
  /-- `Valid_sel(K)` -/
  valid : (lam : ℕ) → Key lam → Bool

/-- The law of a random set `U ⊆ [N]` with independent inclusion indicators,
`Pr[v ∈ U] = p_v`. -/
noncomputable def prodSetW {N : ℕ} (p : Fin N → ℝ) (U : Finset (Fin N)) : ℝ :=
  ∏ v, if v ∈ U then p v else 1 - p v

/-- `S` is a **verifiable selector with input-bias bound `δ_send ≥ 0` and errors
`(α_sel, β_sel, δ_sel)`** (Definition E.4, p.61):
1. a recoverable selector with errors `(α_sel, δ_sel)` (the published `IsRecSelector`), and
   `δ_send ≥ 0`;
2. `Valid_sel` is deterministic polynomial time;
3. *validity*: every `K` in the support of `Gen_sel(1^λ)` has `Valid_sel(K) = 1`;
4. *robust balance* (E.3): for every `K` with `Valid_sel(K) = 1`, every random set `U ⊆ [N]` with
   independent inclusion indicators and `Pr[v ∈ U] ≤ 1/2 + δ_send` for every `v` (the inclusion
   probabilities may depend on `K`), and every `c ∈ {0,1}`,
   `|Pr[Guard_sel(U) = 1, b_K(U) = c] − ½ Pr[Guard_sel(U) = 1]| ≤ β_sel`. -/
def VerSelector.IsVerSelector {N : ℕ → ℕ} (S : VerSelector N) (δsend αsel βsel δsel : ℕ → ℝ) :
    Prop :=
  S.toSelector.IsRecSelector αsel δsel ∧ (∀ lam, 0 ≤ δsend lam) ∧
  PolyTimeOn (ι := (lam : ℕ) × S.Key lam) (fun z => [unary z.1, S.enc z.1 z.2])
    (fun z => [S.valid z.1 z.2]) ∧
  (∀ lam K, S.genW lam K ≠ 0 → S.valid lam K = true) ∧
  ∀ lam K, S.valid lam K = true → ∀ p : Fin (N lam) → ℝ,
    (∀ v, 0 ≤ p v ∧ p v ≤ 1 ∧ p v ≤ 1 / 2 + δsend lam) → ∀ c : Bool,
      |wprob (prodSetW p) (fun U => S.guard lam U = true ∧ S.coin lam K U = c) -
        1 / 2 * wprob (prodSetW p) (fun U => S.guard lam U = true)| ≤ βsel lam

end NoisyOWMPC.Supplement


