-- Prove2me | Definitions.Def_RestrictedDec_Supplement_IBE
-- name    : RestrictedDec_Supplement_IBE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:27:18.899511+00:00
-- url     : https://prove2.me/theorems/6e79c4f6-2225-4599-9e6e-53d8f9594f8b
-- title:
--   Identity-based encryption, ordinary correctness and selective-identity IND-CPA (Definitions 6, 7)
-- statement:
--   An **IBE scheme** $I=(\mathrm{Setup}_I,\mathrm{Extract}_I,\mathrm{IEnc},\mathrm{IDec})$ has $\mathrm{Setup}_I(1^\lambda)=(mpk,msk)$, $\mathrm{Extract}_I(msk,id;r)=sk_{id}$ with an explicit extraction tape $r\in\{0,1\}^{r_{\mathrm{ext}}(\lambda)}$, $\mathrm{IEnc}(mpk,id,y;\rho)$, and deterministic $\mathrm{IDec}(sk_{id},a)\in\{0,1\}^*\cup\{\bot\}$. Efficiency means polynomially many coins and polynomial-time algorithms.
--
--   1. **Ordinary correctness** (Definition 6) for an identity space $\mathcal I$ and a message space $\mathcal Y$: one negligible $\delta_I$ with $\Pr[\mathrm{IDec}(\mathrm{Extract}_I(msk,id;r),\mathrm{IEnc}(mpk,id,y;\rho))\neq y]\le\delta_I(\lambda)$ for every $id\in\mathcal I_\lambda$, $y\in\mathcal Y_\lambda$, over setup, extraction and encryption coins.
--   2. **Selective-identity IND-CPA** (Definition 7): the adversary names $id^*\in\mathcal I_\lambda$ before seeing $mpk$; it may request keys of any identity $id\neq id^*$ (fresh honest extraction coins per request) before and after the challenge; it submits equal-length $y_0,y_1\in\mathcal Y_\lambda$ once and receives $\mathrm{IEnc}(mpk,id^*,y_b)$. The gap $|\Pr[A\Rightarrow1\mid b=1]-\Pr[A\Rightarrow1\mid b=0]|$ must be negligible for every uniform PPT adversary.
--
--   **Formalization Note** The gap is twice the guessing advantage; the two are negligible together.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.3, pp.30–31, Definitions 6, 7

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_Supplement_interact
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- An **identity-based encryption scheme** `I = (Setup_I, Extract_I, IEnc, IDec)`, one per
security parameter `λ`: `setup λ r = (mpk, msk)` on setup coins `r`; `extract λ msk id r = sk_id` on
explicit extraction coins `r ∈ {0,1}^{r_ext(λ)}`; `enc λ mpk id y ρ` encrypts the label `y` to the
identity `id` on coins `ρ`; `dec λ sk_id a ∈ {0,1}* ∪ {⊥}` is deterministic.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.3, p.31 ("SetupI(1λ):
output (mpk, msk). ExtractI(msk, id): output a private decryption key skid. IEnc(mpk, id, y):
encrypt a message y to identity id. IDec(skid, a): decrypt an IBE ciphertext or return ⊥."); App.
A.2, p.30 ("We regard randomized extraction as deterministic extraction with an explicit uniformly
sampled random tape of this length").

**Formalization Note.** Keys, identities, labels and ciphertexts are bit strings; randomness is an
explicit uniform coin vector. The identity space and the IBE message space are predicates supplied
to the correctness and security definitions. -/
structure IBE where
  setupCoins : ℕ → ℕ
  extCoins : ℕ → ℕ
  encCoins : ℕ → ℕ
  setup : (lam : ℕ) → (Fin (setupCoins lam) → Bool) → Str × Str
  extract : (lam : ℕ) → Str → Str → (Fin (extCoins lam) → Bool) → Str
  enc : (lam : ℕ) → Str → Str → Str → (Fin (encCoins lam) → Bool) → Str
  dec : ℕ → Str → Str → Option Str

/-- The IBE is **efficient**: polynomially many coins, and `Setup_I`, `Extract_I`, `IEnc` and `IDec`
are computed by polynomial-time machines uniformly in `λ` on generated master keys and on keys
extracted from them (App. A.3, p.31; the PPT convention, p.13). -/
def IBE.IsEfficient (I : IBE) : Prop :=
  NoisyOWMPC.PolyBounded I.setupCoins ∧ NoisyOWMPC.PolyBounded I.extCoins ∧
  NoisyOWMPC.PolyBounded I.encCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (I.setupCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, List.ofFn r]) =
      BeyondDS.tup [(I.setup lam r).1, (I.setup lam r).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (I.setupCoins lam) → Bool) (id : Str)
    (e : Fin (I.extCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, (I.setup lam r).2, id, List.ofFn e]) =
      I.extract lam (I.setup lam r).2 id e) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (I.setupCoins lam) → Bool) (id y : Str)
    (ρ : Fin (I.encCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, (I.setup lam r).1, id, y, List.ofFn ρ]) =
      I.enc lam (I.setup lam r).1 id y ρ) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (I.setupCoins lam) → Bool) (id a : Str)
    (e : Fin (I.extCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, I.extract lam (I.setup lam r).2 id e, a]) =
      encOpt (I.dec lam (I.extract lam (I.setup lam r).2 id e) a))

open Classical in
/-- **Ordinary IBE correctness** (Definition 6) for the identity space `Id` and the message space
`Ym`: one negligible `δ_I` with
`Pr_{(mpk,msk) ← Setup_I, r, ρ}[IDec(Extract_I(msk, id; r), IEnc(mpk, id, y; ρ)) ≠ y] ≤ δ_I(λ)` for
every supported identity `id ∈ Id_λ` and every label `y ∈ Ym_λ`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 6, App. A.3, p.31. -/
def IBE.Correct (Id Ym : ℕ → Str → Prop) (I : IBE) : Prop :=
  ∃ δ : ℕ → ℝ, NoisyOWMPC.Negligible δ ∧ ∀ (lam : ℕ) (id y : Str), Id lam id → Ym lam y →
    ((PMF.uniformOfFintype (Fin (I.setupCoins lam) → Bool)).bind fun r =>
      (PMF.uniformOfFintype (Fin (I.extCoins lam) → Bool)).bind fun e =>
        (PMF.uniformOfFintype (Fin (I.encCoins lam) → Bool)).map fun ρ =>
          decide (I.dec lam (I.extract lam (I.setup lam r).2 id e)
            (I.enc lam (I.setup lam r).1 id y ρ) ≠ some y)) true ≤ ENNReal.ofReal (δ lam)

/-- The challenger's state in the selective-identity game: before the target identity is named,
or after it (target `id*`, `mpk`, `msk`, whether the challenge was issued). -/
inductive SelState
  | start
  | ready (idStar mpk msk : Str) (challenged : Bool)

open Classical in
/-- The **challenger of the selective-identity IND-CPA game** (Definition 7) with secret bit `b`:
1. the adversary's first move names `id* = fld 0`; if `id* ∉ Id_λ` the game outputs `0`; otherwise
   `(mpk, msk) ← Setup_I(1^λ)` and the adversary receives `mpk`;
2. a move `tup [00, id]` is an extraction request, answered with `encOpt (some sk_id)`,
   `sk_id ← Extract_I(msk, id)` on fresh coins, for `id ∈ Id_λ`, `id ≠ id*`, and refused
   (`encOpt none`) otherwise; before and after the challenge;
3. the first move `tup [01, y₀, y₁]` with `|y₀| = |y₁|` and `y₀, y₁ ∈ Ym_λ` is answered with
   `a* ← IEnc(mpk, id*, y_b)`; an invalid or repeated challenge ends the game with output `0`;
4. any other move ends the game with the adversary's guess, the first bit of `fld 1`. -/
noncomputable def IBE.selChallenger (Id Ym : ℕ → Str → Prop) (I : IBE) (lam : ℕ) (b : Bool) :
    SelState → Str → PMF ((SelState × Str) ⊕ Bool)
  | .start, o =>
    if Id lam (fld o 0) then
      (PMF.uniformOfFintype (Fin (I.setupCoins lam) → Bool)).map fun r =>
        .inl (.ready (fld o 0) (I.setup lam r).1 (I.setup lam r).2 false, (I.setup lam r).1)
    else PMF.pure (.inr false)
  | .ready idS mpk msk ch, o =>
    if fld o 0 = [false, false] then
      if Id lam (fld o 1) ∧ fld o 1 ≠ idS then
        (PMF.uniformOfFintype (Fin (I.extCoins lam) → Bool)).map fun e =>
          .inl (.ready idS mpk msk ch, encOpt (some (I.extract lam msk (fld o 1) e)))
      else PMF.pure (.inl (.ready idS mpk msk ch, encOpt none))
    else if fld o 0 = [false, true] then
      if ch = false ∧ (fld o 1).length = (fld o 2).length ∧ Ym lam (fld o 1) ∧ Ym lam (fld o 2) then
        (PMF.uniformOfFintype (Fin (I.encCoins lam) → Bool)).map fun ρ =>
          .inl (.ready idS mpk msk true, I.enc lam mpk idS (if b then fld o 2 else fld o 1) ρ)
      else PMF.pure (.inr false)
    else PMF.pure (.inr ((fld o 1).headD false))

/-- The distinguishing gap `|Pr[A ⇒ 1 | b = 1] − Pr[A ⇒ 1 | b = 0]|` in the selective-identity
IND-CPA game (Definition 7). -/
noncomputable def IBE.selGap (Id Ym : ℕ → Str → Prop) (I : IBE) (A : Adversary) (lam : ℕ) : ℝ :=
  |((interact A lam (I.selChallenger Id Ym lam true) (A.p.eval lam + 1) .start [] []) true).toReal -
    ((interact A lam (I.selChallenger Id Ym lam false) (A.p.eval lam + 1) .start [] []) true).toReal|

/-- **Selective-identity IND-CPA security** (Definition 7): every uniform PPT adversary has
negligible gap.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 7, App. A.3, p.31
("Before seeing the public parameters, an adversary names an identity id∗ ∈ Iλ. The challenger
generates (mpk, msk), gives mpk to the adversary, and answers extraction requests for any id ≠ id∗.
The adversary then submits equal-length messages y0, y1 and receives a∗ ← IEnc(mpk, id∗, yb) for a
uniform secret bit b. Extraction queries for identities other than id∗ remain available after the
challenge. Selective-identity chosen-plaintext security requires that the adversary's advantage in
guessing b be negligible.").

**Formalization Note.** The gap is twice the guessing advantage `|Pr[b′ = b] − 1/2|`; the two are
negligible together. -/
def IBE.SelINDCPA (Id Ym : ℕ → Str → Prop) (I : IBE) : Prop :=
  ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (I.selGap Id Ym A)

end Supplement

end RestrictedDec


