-- Prove2me | Definitions.Def_RestrictedDec_Supplement_nyProbe
-- name    : RestrictedDec_Supplement_nyProbe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:32:47.719129+00:00
-- url     : https://prove2.me/theorems/ba1c9b8d-a917-4bc4-b5b7-b0b1de859431
-- title:
--   The probe-augmented scheme $\hat\Gamma_q$ (Theorem 9)
-- statement:
--   From a scheme $\Gamma$ (in Theorem 9, the pre-challenge Naor–Yung scheme $\Gamma_q$), a witness sampler $W$, the observation $q$ and a fixed valid default message $\mathrm{dflt}(\lambda)$:
--
--   1. $\mathrm{KeyGen}$: $(pk_\Gamma,sk_\Gamma)\leftarrow\mathrm{KeyGen}_\Gamma$ and, once, $(u,v)\leftarrow W(1^\lambda)$; if $u,v$ are not valid, of equal length and with $q(u)=q(v)$, both become $\mathrm{dflt}(\lambda)$; $(u,v)$ is published in $pk$ and kept in $sk$.
--   2. $\mathrm{Enc}(m)=(0,C)$ for a fresh $\Gamma$ ciphertext $C$.
--   3. $\mathrm{Dec}(0,C)=\mathrm{Dec}_\Gamma(C)$; a probe $(1,j)$ decrypts to $u$ if $s_j=0$ and to $v$ if $s_j=1$, where $s$ encodes $sk_\Gamma$; every other input decrypts to $\bot$.
--
--   **Formalization Note** As in the published probe scheme of the base mission, $s$ is the self-delimiting code of $sk_\Gamma$ followed by zeros and every index $j$ is a probe, so the set of probe ciphertexts does not reveal $|sk_\Gamma|$.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.2, p.38

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_Supplement_interact
import Definitions.Def_RestrictedDec_Supplement_Sampler
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

open Classical in
/-- The **probe-augmented scheme** `Γ̂_q` of Theorem 9, built from a scheme `Γ` (the pre-challenge
Naor–Yung scheme `Γ_q`), a witness sampler `W`, the observation `q` and a fixed valid default
message `dflt(λ)`:
1. `KeyGen`: `(pk_Γ, sk_Γ) ← KeyGen_Γ`, and the witness pair `(u, v) ← W(1^λ)` once; if `u, v` are
   not valid, of equal length and with `q(u) = q(v)`, both are replaced by `dflt(λ)`;
   `pk = (pk_Γ, u, v)`, `sk = (sk_Γ, u, v)`;
2. `Enc_pk(m) = (0, C)` for a fresh `Γ` ciphertext `C ← Enc_Γ(pk_Γ, m)`;
3. `Dec_sk(0, C) = Dec_Γ(sk_Γ, C)`; a probe `(1, j)` decrypts to `u` if `s_j = 0` and to `v` if
   `s_j = 1`, where `s` encodes `sk_Γ`; every other input decrypts to `⊥`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.2, p.38 ("In key
generation, sample the witness pair (u, v) once and publish it in the public key, retaining it also
in the decryption key. Check publicly that the messages are valid, equal-length, and satisfy
q(u) = q(v). If the check fails, use the same fixed valid default message for both u and v. …
Honest encryption always outputs (0, C) for a fresh Γq ciphertext C. Decryption of (0, C) is Γq
decryption. Additionally, on a ciphertext (1, j) with 1 ≤ j ≤ L the algorithm returns u if sj = 0
and v if sj = 1; every other input decrypts to ⊥.").

**Formalization Note.**
1. `(β, c)` is the string `β :: c`; the probe index `j` is `encNat j` (unary, from `0`).
2. As in the published `RestrictedDec.probeScheme`, `s = BeyondDS.selfDelim sk_Γ` is read as
   followed by zeros: every `j` is a probe and bits past the code read `0`, so the set of probe
   ciphertexts does not depend on `|sk_Γ|` (a `⊥` past a key-dependent length `L` would leak it). -/
noncomputable def nyProbe (Γ : PKE) (W : Sampler) (M : ℕ → Str → Prop) (q : ℕ → Option Str → Str)
    (dflt : ℕ → Str) : PKE where
  keyCoins := fun lam => Γ.keyCoins lam + W.coins lam
  encCoins := Γ.encCoins
  keyGen := fun lam r =>
    let kΓ := Γ.keyGen lam (cL r)
    let uv := W.out lam (cR r)
    let uv' := if M lam uv.1 ∧ M lam uv.2 ∧ uv.1.length = uv.2.length ∧
        q lam (some uv.1) = q lam (some uv.2) then uv else (dflt lam, dflt lam)
    (BeyondDS.tup [kΓ.1, uv'.1, uv'.2], BeyondDS.tup [kΓ.2, uv'.1, uv'.2])
  enc := fun lam pk m ρ => false :: Γ.enc lam (fld pk 0) m ρ
  dec := fun lam sk C =>
    match C with
    | false :: c => Γ.dec lam (fld sk 0) c
    | true :: w =>
      if encNat (BeyondDS.decNat w) = w then
        some (if (BeyondDS.selfDelim (fld sk 0)).getD (BeyondDS.decNat w) false
          then fld sk 2 else fld sk 1)
      else none
    | [] => none

end Supplement

end RestrictedDec


