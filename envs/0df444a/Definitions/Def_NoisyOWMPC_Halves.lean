-- Prove2me | Definitions.Def_NoisyOWMPC_Halves
-- name    : NoisyOWMPC_Halves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:37.166205+00:00
-- url     : https://prove2.me/theorems/069b14af-411d-4a14-87af-c70b1216599d
-- title:
--   Protocol halves of channel tests and selectors
-- statement:
--   The **protocol half of a channel test** for a receiver with output alphabet $\mathcal Y_i$ and channel-input length $n$ consists of the sender's state sampler $\mathrm{Gen}(1^\lambda)\to\omega$ (an exact finite reference law), the word $\mathrm{Word}(\omega)\in\mathcal X^n$, and the test $\mathrm{Test}_\omega(w)\in\{0,1\}$ on queries $w\in\mathcal Y_i^n$. The **protocol half of a selector on $[N]$** consists of the key sampler $\mathrm{Gen}_{\mathrm{sel}}$, the public guard $\mathrm{Guard}_{\mathrm{sel}}(U)$ and the coin $b_K(U)$ on sets $U\subseteq[N]$.
--
--   The module also defines, from Definitions 5.1–5.4:
--   1. the **honest experiment** of a test: $\omega\leftarrow\mathrm{Gen}$, $D\leftarrow\mathbf C^n(\mathrm{Word}(\omega))$;
--   2. **completeness** of an access test with error $\alpha$: $\Pr[A_\Omega(D_i)=0]\le\alpha$;
--   3. **unbiasedness** of a release test with error $\eta$: some $p'\in[0,1]$ with $|p'-\tfrac12|\le\eta$ has $\Pr[Q_\Theta(D_i)=1]=p'$ for every state $\Theta$ in the support;
--   4. the **trivial access test** for $k=1$ (length $0$, one state encoded by the empty string, always accepts);
--   5. **honest acceptance** $\Pr[\mathrm{Guard}_{\mathrm{sel}}(V)=0]\le\alpha_{\mathrm{sel}}$ and **balance** $\Pr[b_K(V)=1\mid\mathrm{Guard}_{\mathrm{sel}}(V)=1]=\tfrac12$ for the fair set $V$;
--   6. the bundle `Halves` of the halves used by Construction 5.23.
--
--   **Formalization Note** Queries are typed words, so malformed queries are rejected by the program's parser. Definition 5.3 asks for $p'\in(0,1)$; here $p'\in[0,1]$, which is the same whenever $\eta<\tfrac12$. The strict condition can fail at small $\lambda$ under the paper's $2^{-\lambda}$ rounding convention (at $\lambda=4$, $M=2047$, approximations near $C+2^{-4}$ make the consistency check reject every query).
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definitions 5.1–5.4, pp.22–23; Construction 5.23, p.30

import Mathlib
import Definitions.Def_NoisyOWMPC_DMC
import Definitions.Def_NoisyOWMPC_wprob

namespace NoisyOWMPC

/-- The **protocol half of a channel test** for a receiver with output alphabet `Yi` and
channel-input length `n` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…),
Definition 5.1, p.22): the sender's state sampler `Gen(1^λ) → ω` (its exact reference law `genW λ`
on the finite state space `Sec λ`), `Word(ω) ∈ Xⁿ`, and the test `Test_ω(w) ∈ {0,1}` on queries
`w ∈ Y_iⁿ`; `enc` is the fixed encoding of states hard-wired into the obfuscated program.

**Formalization Note** Queries are typed words, so the malformed-query rejection of Definition 5.1
is the parsing step of the program (`fig6Bits`). The proof-side algorithms are added in
`RecChannelTest`. -/
structure TestHalf (X Yi : Type) (n : ℕ → ℕ) where
  /-- the secret states -/
  Sec : ℕ → Type
  [finSec : ∀ lam, Fintype (Sec lam)]
  /-- the law of `Gen(1^λ)` -/
  genW : (lam : ℕ) → Sec lam → ℝ
  /-- the encoding of a state -/
  enc : (lam : ℕ) → Sec lam → List Bool
  /-- `Word(ω)` -/
  word : (lam : ℕ) → Sec lam → Fin (n lam) → X
  /-- `Test_ω(w)` -/
  test : (lam : ℕ) → Sec lam → (Fin (n lam) → Yi) → Bool

attribute [instance] TestHalf.finSec

/-- The **protocol half of a selector on `[N]`** (Definition 5.4, p.23): the key sampler
`Gen_sel(1^λ) → K` (exact reference law `genW λ` on `Key λ`), the public guard `Guard_sel(U)` and the
selected coin `b_K(U)` on sets `U ⊆ [N]`; `enc` encodes keys. -/
structure SelHalf (N : ℕ → ℕ) where
  /-- the keys -/
  Key : ℕ → Type
  [finKey : ∀ lam, Fintype (Key lam)]
  /-- the law of `Gen_sel(1^λ)` -/
  genW : (lam : ℕ) → Key lam → ℝ
  /-- the encoding of a key -/
  enc : (lam : ℕ) → Key lam → List Bool
  /-- `Guard_sel(U)` -/
  guard : (lam : ℕ) → Finset (Fin (N lam)) → Bool
  /-- `b_K(U)` -/
  coin : (lam : ℕ) → Key lam → Finset (Fin (N lam)) → Bool

attribute [instance] SelHalf.finKey

/-- The protocol halves used by Construction 5.23 (STOC 2027 submission (manuscript sha256
3a9569fa…), Construction 5.23, p.30): an access test and a release test per receiver, with common
channel-input lengths `n_acc` and `n_rel` (Theorem 5.25, p.31: "`1[k > 1] k n_acc + qN n_rel` noisy
channel uses"), a block length `N` and a selector on `[N]`.

**Formalization Note** For `k = 1` the access tests are the trivial test of Definition 5.2 (p.22:
"For `k = 1` the access test is the trivial test that always accepts"); the program skips the
access step when `k = 1` in any case. -/
structure Halves (k : ℕ) (X : Type) (Y : Fin k → Type) where
  /-- the access channel-input length -/
  nacc : ℕ → ℕ
  /-- the release channel-input length -/
  nrel : ℕ → ℕ
  /-- the block length -/
  N : ℕ → ℕ
  /-- the access test of receiver `i` -/
  acc : (i : Fin k) → TestHalf X (Y i) nacc
  /-- the release test of receiver `i` -/
  rel : (i : Fin k) → TestHalf X (Y i) nrel
  /-- the selector -/
  sel : SelHalf N

variable {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)]

/-- The state sampler's law is a **probability distribution** (nonnegative weights summing to one). -/
def TestHalf.IsDist {Yi : Type} {n : ℕ → ℕ} (T : TestHalf X Yi n) : Prop :=
  ∀ lam, (∀ ω, 0 ≤ T.genW lam ω) ∧ ∑ ω, T.genW lam ω = 1

/-- The key sampler's law is a **probability distribution**. -/
def SelHalf.IsDist {N : ℕ → ℕ} (S : SelHalf N) : Prop :=
  ∀ lam, (∀ K, 0 ≤ S.genW lam K) ∧ ∑ K, S.genW lam K = 1

/-- The **honest experiment** of a channel test (Definition 5.1, p.22: "the sender transmits
`X = Word(ω)` through the channel, and `D = (D₁, …, D_k) ← Cⁿ(X)`"): the weight of `(ω, D)`. -/
noncomputable def honestW {i : Fin k} {n : ℕ → ℕ} (C : ∀ j, DMC X (Y j)) (T : TestHalf X (Y i) n)
    (lam : ℕ) (ω : T.Sec lam × (Fin (n lam) → ∀ j, Y j)) : ℝ :=
  T.genW lam ω.1 * ∏ s, jointP C (T.word lam ω.1 s) (ω.2 s)

/-- **Completeness** of an access test with error `α` (Definition 5.2, p.22): in the honest
experiment, `Pr[A_Ω(D_i) = 0] ≤ α`. -/
def TestHalf.Complete {i : Fin k} {n : ℕ → ℕ} (C : ∀ j, DMC X (Y j)) (T : TestHalf X (Y i) n)
    (α : ℕ → ℝ) : Prop :=
  ∀ lam, wprob (honestW C T lam) (fun ω => T.test lam ω.1 (fun s => ω.2 s i) = false) ≤ α lam

/-- **Unbiasedness** of a release test with error `η` (Definition 5.3, (5.3), p.22): there is
`p′` with `|p′ − ½| ≤ η` such that `Pr[Q_Θ(D_i) = 1] = p′` for every state `Θ` in the support,
`D_i ← C_iⁿ(Word(Θ))`.

**Formalization Note** The page asks for `p′ ∈ (0, 1)`. Here `p′` is a probability, so it lies in
`[0, 1]`, and whenever `η < ½` the bound forces `p′ ∈ (0, 1)`. The strict condition is dropped
because it can fail at small `λ` under the paper's own rounding convention (§5 Conventions, p.21):
with approximations `apx = C + 2^{−λ}` at `λ = 4`, `M = 2047`, the consistency check of Construction
5.11 rejects every query, so `p′ = 0` while the release errors are allowed to exceed `½`. -/
def TestHalf.Unbiased {i : Fin k} {n : ℕ → ℕ} (C : ∀ j, DMC X (Y j)) (T : TestHalf X (Y i) n)
    (η : ℕ → ℝ) : Prop :=
  ∀ lam, ∃ p' : ℝ, 0 ≤ p' ∧ p' ≤ 1 ∧ |p' - 1 / 2| ≤ η lam ∧ ∀ Θ, T.genW lam Θ ≠ 0 →
    ∑ d : Fin (n lam) → Y i, (∏ s, (C i).P (T.word lam Θ s) (d s)) *
      (if T.test lam Θ d then 1 else 0) = p'

/-- The **trivial access test** (Definition 5.2, p.22: for `k = 1`, "the trivial test that always
accepts"): channel-input length zero, one state (encoded by the empty string), and every query
accepted. -/
def TestHalf.IsTrivial {Yi : Type} {X : Type} {n : ℕ → ℕ} (T : TestHalf X Yi n) : Prop :=
  ∀ lam, n lam = 0 ∧ Fintype.card (T.Sec lam) = 1 ∧ (∀ ω, T.genW lam ω = 1) ∧
    (∀ ω, T.enc lam ω = []) ∧ ∀ ω w, T.test lam ω w = true

/-- The **fair honest accepting set** `V ⊆ [N]`, containing each position independently with
probability `1/2` (Definition 5.4, p.23): weight `2^{−N}` on every subset. -/
noncomputable def fairW (N : ℕ) : Finset (Fin N) → ℝ := fun _ => (1 / 2 : ℝ) ^ N

/-- **Honest acceptance** of a selector with error `α_sel` (Definition 5.4, (5.5), p.23):
`Pr[Guard_sel(V) = 0] ≤ α_sel` for the fair set `V`. -/
def SelHalf.HonestAccept {N : ℕ → ℕ} (S : SelHalf N) (αsel : ℕ → ℝ) : Prop :=
  ∀ lam, wprob (fairW (N lam)) (fun V => S.guard lam V = false) ≤ αsel lam

/-- **Balance** of a selector (Definition 5.4, (5.6), p.23): for every key `K` in the support of
`Gen_sel`, `Pr[b_K(V) = 1 | Guard_sel(V) = 1] = ½`, written as
`Pr[b_K(V) = 1 ∧ Guard_sel(V) = 1] = ½ · Pr[Guard_sel(V) = 1]`. -/
def SelHalf.Balanced {N : ℕ → ℕ} (S : SelHalf N) : Prop :=
  ∀ lam K, S.genW lam K ≠ 0 →
    wprob (fairW (N lam)) (fun V => S.guard lam V = true ∧ S.coin lam K V = true) =
      1 / 2 * wprob (fairW (N lam)) (fun V => S.guard lam V = true)

end NoisyOWMPC


