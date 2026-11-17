-- Prove2me | Definitions.Def_RestrictedDec_Supplement_signedCHK
-- name    : RestrictedDec_Supplement_signedCHK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:31:03.141602+00:00
-- url     : https://prove2.me/theorems/4fdfc0d1-f663-4c64-a9c2-8ee4a6b37a43
-- title:
--   The signed CHK compiler (4.3)
-- statement:
--   For an observation $q$ with $\mathrm{Valid}_q,\mathrm{Rep}_q$, a residual scheme $R$, an IBE $I$ with identity space $\mathcal I$, a PRF $P$ and a one-time signature $S$:
--
--   1. $\mathrm{KeyGen}$ as in the unsigned compiler: $pk=(pk_R,mpk)$, $sk=(sk_R,msk,k)$.
--   2. $\mathrm{Enc}_{pk}(m)$: $(ssk,vk)\leftarrow\mathrm{SGen}(1^\lambda)$, $y=q(m)$, $d\leftarrow\mathrm{Enc}_R(pk_R,m)$, $a\leftarrow\mathrm{IEnc}(mpk,vk,y)$, $\sigma\leftarrow\mathrm{Sign}_{ssk}(\langle d,a\rangle)$; $C=(d,vk,a,\sigma)$.
--   3. $\mathrm{Dec}_{sk}(C)$: reject malformed encodings and any $C$ with $\mathrm{Vrf}_{vk}(\langle d,a\rangle,\sigma)=0$; otherwise $sk_{vk}=\mathrm{Extract}_I(msk,vk;\mathrm{PRF}_k(vk))$, $y=\mathrm{IDec}(sk_{vk},a)$; if $y=\bot$ or $\mathrm{Valid}_q(1^\lambda,y)=0$ output $\bot$; else output $\mathrm{Norm}_q(y,\mathrm{Dec}_R(sk_R,d))$.
--
--   The signature covers both encrypted components and is verified under the key used as the IBE identity.
--
--   **Formalization Note** $\langle d,a\rangle$ is the tuple code of $(d,a)$; the identity is the verification-key string; an identity outside $\mathcal I_\lambda$ is malformed.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §4.2, (4.3), pp.24–25

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_Supplement_interact
import Definitions.Def_RestrictedDec_Supplement_Obs
import Definitions.Def_RestrictedDec_Supplement_IBE
import Definitions.Def_RestrictedDec_Supplement_PRF
import Definitions.Def_RestrictedDec_Supplement_OTS
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

open Classical in
/-- The **signed CHK-based compiler** (4.3) for the observation `q` with `Valid_q`, `Rep_q`, built
from a residual scheme `R`, an IBE `I`, a PRF `P` and a one-time signature `S`:
1. `KeyGen(1^λ)`: `(pk_R, sk_R) ← KeyGen_R`, `(mpk, msk) ← Setup_I`, seed `k`;
   `pk = (pk_R, mpk)`, `sk = (sk_R, msk, k)`;
2. `Enc_pk(m)`: `(ssk, vk) ← SGen(1^λ)`, `y = q(m)`, `d ← Enc_R(pk_R, m)`,
   `a ← IEnc(mpk, vk, y)`, `σ ← Sign_ssk(⟨d, a⟩)`, `C = (d, vk, a, σ)`;
3. `Dec_sk(C)`: reject malformed encodings (including an identity `vk ∉ Id_λ`) and any `C` with `Vrf_vk(⟨d, a⟩, σ) = 0`; otherwise
   `sk_vk = Extract_I(msk, vk; PRF_k(vk))`, `y = IDec(sk_vk, a)`; if `y = ⊥` or
   `Valid_q(1^λ, y) = 0` output `⊥`; else output `Norm_q(y, Dec_R(sk_R, d))`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §4.2, (4.3), pp.24–25.

**Formalization Note.** An identity outside the IBE's public identity space `Id_λ` is treated as a
malformed component and rejected. `⟨d, a⟩` is `tup [d, a]` and `C` is `tup [d, vk, a, σ]`; "malformed" means
"not the code of a 4-tuple". The identity is the verification key string itself (its canonical
injective encoding). Encryption coins are split as `SGen`, `Enc_R`, `IEnc`, `Sign`. -/
noncomputable def signedCHK (M Id : ℕ → Str → Prop) (o : Obs) (R : PKE) (I : IBE) (P : PRF)
    (S : OTS) : PKE where
  keyCoins := fun lam => R.keyCoins lam + I.setupCoins lam + P.keyCoins lam
  encCoins := fun lam => S.keyCoins lam + R.encCoins lam + I.encCoins lam + S.signCoins lam
  keyGen := fun lam r =>
    (BeyondDS.tup [(R.keyGen lam (cL (cL r))).1, (I.setup lam (cR (cL r))).1],
      BeyondDS.tup [(R.keyGen lam (cL (cL r))).2, (I.setup lam (cR (cL r))).2, P.gen lam (cR r)])
  enc := fun lam pk m ρ =>
    let kS := S.gen lam (cL (cL (cL ρ)))
    let d := R.enc lam (fld pk 0) m (cR (cL (cL ρ)))
    let a := I.enc lam (fld pk 1) kS.2 (o.q lam (some m)) (cR (cL ρ))
    BeyondDS.tup [d, kS.2, a, S.sign lam kS.1 (BeyondDS.tup [d, a]) (cR ρ)]
  dec := fun lam sk C =>
    match parseTup 4 C with
    | some [d, vk, a, σ] =>
      if Id lam vk ∧ S.vrf lam vk (BeyondDS.tup [d, a]) σ = true then
        match I.dec lam (I.extract lam (fld sk 1) vk
            (coinsOf (I.extCoins lam) (P.eval lam (fld sk 2) vk))) a with
        | some y => if o.valid lam y then norm M o lam y (R.dec lam (fld sk 0) d) else none
        | none => none
      else none
    | _ => none

end Supplement

end RestrictedDec


