-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_constructionE8
-- name    : NoisyOWMPC_Supplement_constructionE8
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:03:01.931215+00:00
-- url     : https://prove2.me/theorems/328ce242-02ed-4a51-88b8-6e35e62a7651
-- title:
--   Construction E.8: malicious one-way secure computation, with the certification relation $R_{\mathrm{cert}}$
-- statement:
--   **Construction E.8** is Construction 5.23 with one receiver, a verifiable release test and a verifiable selector, and a channel zero-knowledge proof certifying the broadcast program.
--
--   Write $\theta = (x, (\Theta_{jv})_{j \in [q], v \in [N]}, (K_j)_{j}, \pi)$ for the constants of the Fig. 6 program $P_\theta$ with $k = 1$ (there is no access test). The constants are **valid** if every release state satisfies $\mathrm{Valid_{rel}}$ and every key satisfies $\mathrm{Valid_{sel}}$. The **certification relation** is
--   $$
--   R_{\mathrm{cert}}\big(\tau, (\theta, r)\big) = 1 \iff \mathrm{Valid}(\theta) = 1 \text{ and } \tau = i\mathcal O(1^\lambda, P_\theta; r),
--   $$
--   with $\tau$ the padded and length-prefixed obfuscation; malformed witnesses are rejected.
--
--   1. **Sender** $S(1^\lambda, x)$: sample $\Theta_{jv} \leftarrow \mathrm{Gen_{rel}}$, $K_j \leftarrow \mathrm{Gen_{sel}}$, $\pi \leftarrow \{0,1\}^q$ independently; form $\theta$ and the data word $\hat x_{\mathrm{data}} = (\mathrm{Word_{rel}}(\Theta_{jv}))_{j,v}$ in the public order of Construction 5.23; sample a uniform obfuscator tape $r$ and set $\tau = i\mathcal O(1^\lambda, P_\theta; r)$; sample $\hat x_{\mathrm{ZK}} \leftarrow P_{\mathrm{ZK}}(1^\lambda, \tau, (\theta, r))$; output $\tau$ and $\hat x = \hat x_{\mathrm{data}} \Vert \hat x_{\mathrm{ZK}}$.
--   2. **Receiver** $R(1^\lambda, \tau, \hat y)$: split $\hat y = D \Vert \hat y_{\mathrm{ZK}}$; return $\mathsf{fail}$ if $V_{\mathrm{ZK}}(1^\lambda, \tau, \hat y_{\mathrm{ZK}}) = 0$; otherwise evaluate $\tau$ on $D$ as the receiver of Construction 5.23 with $k = 1$.
--
--   This is the protocol of Theorems E.9 and E.10.
--
--   **Formalization Note** The data part reuses the published Construction 5.23 (sampled constants, program generator, padding, transmission encoding, cell order and receiver), with the trivial access test of Definition 5.2 for $k = 1$. Observations are typed words, so splitting $\hat y$ cannot fail.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §E.4 (program, (E.5), (E.6), Construction E.8), pp.63–64

import Mathlib
import Definitions.Def_NoisyOWMPC_construction
import Definitions.Def_NoisyOWMPC_Supplement_Verifiable
import Definitions.Def_NoisyOWMPC_Supplement_ChannelZK

namespace NoisyOWMPC.Supplement

open KarpLiptonOM LaconicBarrier

/-- The **trivial access test** of a single receiver (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Definition 5.2, p.22: "For `k = 1` the access test is the trivial
test that always accepts"; §E.4, p.63: "there is no access test"): channel-input length `0`, one
state encoded by the empty string, every query accepted. -/
def trivAcc (X Yc : Type) : TestHalf X Yc (fun _ => 0) where
  Sec _ := Unit
  genW _ _ := 1
  enc _ _ := []
  word _ _ p := p.elim0
  test _ _ _ := true

variable {X Yc : Type} [Fintype X] [Fintype Yc]

/-- The protocol halves of Construction E.8 (p.64: "We use Construction 5.23 with one receiver,
verifiable release tests and selectors in place of recoverable ones"): the trivial access test, the
release test `R` with channel-input length `n_rel`, and the selector `S` on `[N]`. -/
def halvesE8 {nrel N : ℕ → ℕ} (R : VerReleaseTest X Yc nrel) (S : VerSelector N) :
    Halves 1 X (oneY Yc) :=
  ⟨fun _ => 0, nrel, N, fun _ => trivAcc X Yc, fun _ => R.toTestHalf, S.toSelHalf⟩

/-- **Valid constants** `Valid(θ) = 1` (p.64: "if every field has its prescribed encoding,
`x ∈ {0,1}^{ℓ_x}`, `π ∈ {0,1}^q`, `Valid_rel(Θ_{jv}) = 1` for every `j, v`, and `Valid_sel(K_j) = 1`
for every `j`"), for the typed constants of the Fig. 6 program with `k = 1`. -/
def validE8 {nrel N : ℕ → ℕ} (R : VerReleaseTest X Yc nrel) (S : VerSelector N)
    (F : Functionality 1) (lam : ℕ) (c : Consts (halvesE8 R S) F lam) : Prop :=
  (∀ b v, R.valid lam (c.2.1 b v) = true) ∧ ∀ b, S.valid lam (c.2.2.1 b) = true

/-- The encoding of a certification witness `(θ, r)`: the input `x`, the program constants and the
obfuscator tape. -/
def witEnc {nrel N : ℕ → ℕ} {R : VerReleaseTest X Yc nrel} {S : VerSelector N}
    {F : Functionality 1} {lam : ℕ} (O : IOScheme) (s : ℕ → ℕ) (x : Fin (F.lx lam) → Bool)
    (c : Consts (halvesE8 R S) F lam)
    (r : Fin (O.coins lam (inLen (halvesE8 R S) F lam) (s lam + outLen F lam)) → Bool) :
    List Bool :=
  QAdvFew.PoQOracle.tup [bits x, constsEnc (halvesE8 R S) F lam c, bits r]

/-- The **certification relation** `R_cert` (p.64, (E.6)): `R_cert(τ, (θ, r)) = 1` iff
`Valid(θ) = 1` and `τ = iO(1^λ, P_θ; r)`, where `P_θ` is the Fig. 6 program with `k = 1` built by
the generator `gen`, padded to `s` gates, and `τ` is its obfuscation length-prefixed and padded for
transmission as in Construction 5.23; witnesses are the encodings of `(x, θ, r)`, and every other
string (a malformed witness, or fields outside the prescribed sizes) is rejected. -/
def Rcert {nrel N : ℕ → ℕ} (R : VerReleaseTest X Yc nrel) (S : VerSelector N)
    (F : Functionality 1) (O : IOScheme) (gen : ProgGen (halvesE8 R S) F) (s : ℕ → ℕ)
    (lam : ℕ) (τ : Fin (txLen (halvesE8 R S) F O gen s lam) → Bool) (w : List Bool) : Prop :=
  ∃ (x : Fin (F.lx lam) → Bool) (c : Consts (halvesE8 R S) F lam)
    (r : Fin (O.coins lam (inLen (halvesE8 R S) F lam) (s lam + outLen F lam)) → Bool),
    w = witEnc O s x c r ∧ validE8 R S F lam c ∧
      τ = txEnc (halvesE8 R S) F O gen s lam (obfProg (halvesE8 R S) F O gen s lam x (c, r)).code

/-- **Construction E.8 (Malicious one-way secure computation)** (STOC 2027 submission (manuscript
sha256 3a9569fa…), p.64), for a verifiable release test `R`, a verifiable selector `S`, a public
target circuit `f` (`F`), an obfuscator `O`, a Fig. 6 generator `gen`, a pad size `s` and a channel
zero-knowledge proof `Z` for `R_cert`:
* `S(1^λ, x)`: sample `Θ_{jv} ← Gen_rel`, `K_j ← Gen_sel`, `π ← {0,1}^q` independently, form `θ` and
  the data word `x̂_data = (Word_rel(Θ_{jv}))_{j,v}` in the public order of Construction 5.23; sample
  a uniform obfuscator tape `r` and set `τ = iO(1^λ, P_θ; r)`; sample `x̂_ZK ← P_ZK(1^λ, τ, (θ, r))`
  with fresh prover coins; output `τ` and `x̂ = x̂_data ∥ x̂_ZK`;
* `R(1^λ, τ, ŷ)`: split `ŷ = D ∥ ŷ_ZK`; return `fail` if `V_ZK(1^λ, τ, ŷ_ZK) = 0`; otherwise
  evaluate `τ` on `D` as the receiver of Construction 5.23 with `k = 1`.

**Formalization Note** The data part reuses the published `construction` (its sampled constants,
padding, transmission encoding, public cell order and receiver); with the trivial access test the
access cells are empty. Observations are typed, so parsing `ŷ` cannot fail. -/
noncomputable def constructionE8 {nrel N : ℕ → ℕ} (R : VerReleaseTest X Yc nrel)
    (S : VerSelector N) (F : Functionality 1) (O : IOScheme) (gen : ProgGen (halvesE8 R S) F)
    (s : ℕ → ℕ) (Z : ChannelZK X Yc (txLen (halvesE8 R S) F O gen s)) :
    Protocol 1 X (oneY Yc) F where
  RS lam := SenderCoins (halvesE8 R S) F O s lam × (Fin (Z.coins lam) → Bool)
  wS lam r := (construction (halvesE8 R S) F O gen s).wS lam r.1 * (1 / 2 : ℝ) ^ (Z.coins lam)
  encRS lam r := QAdvFew.PoQOracle.tup [(construction (halvesE8 R S) F O gen s).encRS lam r.1,
    bits r.2]
  L := txLen (halvesE8 R S) F O gen s
  N lam := nTot (halvesE8 R S) F lam + Z.nZK lam
  send lam x r :=
    (txEnc (halvesE8 R S) F O gen s lam (obfProg (halvesE8 R S) F O gen s lam x r.1).code,
      Fin.append (chanWord (halvesE8 R S) F lam r.1.1)
        (Z.prove lam (txEnc (halvesE8 R S) F O gen s lam
            (obfProg (halvesE8 R S) F O gen s lam x r.1).code)
          (witEnc O s x r.1.1 r.1.2) r.2))
  recv lam i τ y :=
    if Z.verify lam τ (fun p => y (Fin.natAdd (nTot (halvesE8 R S) F lam) p)) then
      (construction (halvesE8 R S) F O gen s).recv lam i τ
        (fun p => y (Fin.castAdd (Z.nZK lam) p))
    else none

end NoisyOWMPC.Supplement


