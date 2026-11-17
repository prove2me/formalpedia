-- Prove2me | Definitions.Def_RestrictedDec_Supplement_OTS
-- name    : RestrictedDec_Supplement_OTS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:28:27.883351+00:00
-- url     : https://prove2.me/theorems/3f0532fe-e1f7-4109-9cae-ebc31bdfd553
-- title:
--   One-time signatures, correctness and strong one-time unforgeability (Definitions 13, 14)
-- statement:
--   A **one-time signature** $S=(\mathrm{SGen},\mathrm{Sign},\mathrm{Vrf})$ has $\mathrm{SGen}(1^\lambda)=(ssk,vk)$, $\mathrm{Sign}_{ssk}(M;\rho)=\sigma$ and $\mathrm{Vrf}_{vk}(M,\sigma)\in\{0,1\}$; efficiency means polynomially many coins and polynomial-time algorithms.
--
--   1. **Correctness** (Definition 14): honest signatures verify with probability $1$, for every message.
--   2. **Strong one-time unforgeability** (Definition 13): the adversary receives $vk$, asks one signing query $M^*$, receives $\sigma^*$, and outputs $(M,\sigma)$; it wins iff $\mathrm{Vrf}_{vk}(M,\sigma)=1$ and $(M,\sigma)\neq(M^*,\sigma^*)$. The success probability must be negligible for every uniform PPT adversary.
--
--   **Formalization Note** An output given before the signing query, or a second signing query, is a loss; an adversary can always make a dummy query first, so this changes no security level.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.5, p.34, Definitions 13, 14

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Supplement_interact
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- A **one-time signature scheme** `S = (SGen, Sign, Vrf)`: `gen λ r = (ssk, vk)` on coins `r`;
`sign λ ssk M ρ = σ` on coins `ρ`; `vrf λ vk M σ ∈ {0, 1}`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.5, p.34 ("SGen(1λ):
output a signing/verification pair (sk, vk). Signsk(M): output a signature σ on message M.
Vrfvk(M, σ): output 1 or 0."). -/
structure OTS where
  keyCoins : ℕ → ℕ
  signCoins : ℕ → ℕ
  gen : (lam : ℕ) → (Fin (keyCoins lam) → Bool) → Str × Str
  sign : (lam : ℕ) → Str → Str → (Fin (signCoins lam) → Bool) → Str
  vrf : ℕ → Str → Str → Str → Bool

/-- The signature scheme is **efficient**: polynomially many coins and polynomial-time machines,
uniform in `λ`, for `SGen`, for `Sign` under generated signing keys, and for `Vrf`. -/
def OTS.IsEfficient (S : OTS) : Prop :=
  NoisyOWMPC.PolyBounded S.keyCoins ∧ NoisyOWMPC.PolyBounded S.signCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (S.keyCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, List.ofFn r]) = BeyondDS.tup [(S.gen lam r).1, (S.gen lam r).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (S.keyCoins lam) → Bool) (m : Str)
    (ρ : Fin (S.signCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, (S.gen lam r).1, m, List.ofFn ρ]) = S.sign lam (S.gen lam r).1 m ρ) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (vk m σ : Str),
    f (BeyondDS.tup [encNat lam, vk, m, σ]) = BeyondDS.encBool (S.vrf lam vk m σ))

/-- **Signature correctness** (Definition 14): an honest signature verifies with probability `1`
for every message, i.e. for every key coin vector and every signing coin vector.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 14, App. A.5, p.34. -/
def OTS.Correct (S : OTS) : Prop :=
  ∀ lam (r : Fin (S.keyCoins lam) → Bool) (m : Str) (ρ : Fin (S.signCoins lam) → Bool),
    S.vrf lam (S.gen lam r).2 m (S.sign lam (S.gen lam r).1 m ρ) = true

open Classical in
/-- The **challenger of the strong one-time unforgeability experiment** (Definition 13), for the
key pair `(ssk, vk)`: the state is the signed pair `(M*, σ*)` once issued. A move `tup [0, M*]` is
the one signing query, answered with `σ* ← Sign_ssk(M*)`; a second query ends the experiment with
output `0`. Any other move `tup [·, M, σ]` is the output: the adversary wins iff it made its
signing query, `Vrf_vk(M, σ) = 1` and `(M, σ) ≠ (M*, σ*)`. -/
noncomputable def OTS.sufChallenger (S : OTS) (lam : ℕ) (ssk vk : Str) :
    Option (Str × Str) → Str → PMF ((Option (Str × Str) × Str) ⊕ Bool)
  | st, o =>
    if fld o 0 = [false] then
      match st with
      | none =>
        (PMF.uniformOfFintype (Fin (S.signCoins lam) → Bool)).map fun ρ =>
          .inl (some (fld o 1, S.sign lam ssk (fld o 1) ρ), S.sign lam ssk (fld o 1) ρ)
      | some _ => PMF.pure (.inr false)
    else PMF.pure (.inr (decide (∃ p, st = some p ∧ S.vrf lam vk (fld o 1) (fld o 2) = true ∧
      (fld o 1, fld o 2) ≠ p)))

/-- The **success probability** of `A` in the strong one-time unforgeability experiment
(Definition 13): `(ssk, vk) ← SGen(1^λ)`, `A` gets `vk`. -/
noncomputable def OTS.sufAdv (S : OTS) (A : Adversary) (lam : ℕ) : ℝ :=
  (((PMF.uniformOfFintype (Fin (S.keyCoins lam) → Bool)).bind fun r =>
    interact A lam (S.sufChallenger lam (S.gen lam r).1 (S.gen lam r).2) (A.p.eval lam + 1)
      none [] (S.gen lam r).2) true).toReal

/-- **Strong one-time unforgeability** (Definition 13): every uniform PPT adversary has negligible
success probability.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 13, App. A.5, p.34
("The adversary outputs a message M∗ and receives σ∗ ← Signsk(M∗). It then outputs (M, σ). The
adversary wins iff Vrfvk(M, σ) = 1 and (M, σ) ≠ (M∗, σ∗). The success probability must be negligible
for every PPT adversary."). -/
def OTS.SUF (S : OTS) : Prop :=
  ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (S.sufAdv A)

end Supplement

end RestrictedDec


