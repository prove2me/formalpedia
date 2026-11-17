-- Prove2me | Definitions.Def_RestrictedDec_Supplement_unsignedCHK
-- name    : RestrictedDec_Supplement_unsignedCHK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:29:59.938937+00:00
-- url     : https://prove2.me/theorems/36fb91fa-f474-4812-a0a9-a7db005cc526
-- title:
--   The unsigned CHK compiler (4.4)
-- statement:
--   For an observation $q$ with $\mathrm{Valid}_q,\mathrm{Rep}_q$, a residual scheme $R$, an IBE $I$ with identity space $\mathcal I$ and a PRF $P$:
--
--   1. $\mathrm{KeyGen}$: $(pk_R,sk_R)\leftarrow\mathrm{KeyGen}_R$, $(mpk,msk)\leftarrow\mathrm{Setup}_I$, a seed $k$; $pk=(pk_R,mpk)$, $sk=(sk_R,msk,k)$.
--   2. $\mathrm{Enc}_{pk}(m)$: a fresh uniform identity $id\leftarrow\{0,1\}^\lambda$, $d\leftarrow\mathrm{Enc}_R(pk_R,m)$, $a\leftarrow\mathrm{IEnc}(mpk,id,q(m))$; $C=(d,id,a)$.
--   3. $\mathrm{Dec}_{sk}(C)$: reject malformed $C$; derive $sk_{id}=\mathrm{Extract}_I(msk,id;\mathrm{PRF}_k(id))$, $y=\mathrm{IDec}(sk_{id},a)$; if $y=\bot$ or $\mathrm{Valid}_q(1^\lambda,y)=0$ output $\bot$; else output $\mathrm{Norm}_q(y,\mathrm{Dec}_R(sk_R,d))$.
--
--   Decryption never rejects because the residual plaintext disagrees with the label; it normalizes instead.
--
--   **Formalization Note** Tuples are canonical tuple codes; a string that is not the code of a triple, or whose identity is outside $\mathcal I_\lambda$, is malformed and decrypts to $\bot$. The PRF output is read as the extraction tape.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §4.2, (4.4), p.25; (4.1), p.23; Lemma 2, p.31

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_Supplement_interact
import Definitions.Def_RestrictedDec_Supplement_Obs
import Definitions.Def_RestrictedDec_Supplement_IBE
import Definitions.Def_RestrictedDec_Supplement_PRF
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

open Classical in
/-- The **unsigned CHK-based compiler** (4.4) for the observation `q` with `Valid_q`, `Rep_q`,
built from a residual scheme `R`, an IBE `I` and a PRF `P` (fixed per-identity extraction coins):
1. `KeyGen(1^λ)`: `(pk_R, sk_R) ← KeyGen_R`, `(mpk, msk) ← Setup_I`, seed `k ← PGen`;
   `pk = (pk_R, mpk)`, `sk = (sk_R, msk, k)`;
2. `Enc_pk(m)`: a fresh uniform identity `id ← {0,1}^λ`, `d ← Enc_R(pk_R, m)`,
   `a ← IEnc(mpk, id, q(m))`, `C = (d, id, a)`;
3. `Dec_sk(C)`: reject (`⊥`) a malformed `C`, including one whose identity is outside the IBE
   identity space `Id_λ`; otherwise `sk_id = Extract_I(msk, id; PRF_k(id))`,
   `y = IDec(sk_id, a)`; if `y = ⊥` or `Valid_q(1^λ, y) = 0` output `⊥`; else output
   `Norm_q(y, Dec_R(sk_R, d))`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §4.2, pp.24–25 ("Replace the
verification key by a fresh uniform identity id ← {0, 1}λ, and encrypt d ← EncpkR(m),
a ← IEnc(mpk, id, q(m)), C = (d, id, a). (4.4) Decryption obtains the fixed private key for id,
decrypts a, checks label validity, and applies the same normalization."); the signed decryption
rule, p.25; Lemma 2, p.31.

**Formalization Note.** An identity outside the IBE's public identity space `Id_λ` is treated as a
malformed component and rejected. Tuples are `BeyondDS.tup` codes and "malformed" means "not the code of a
triple" (`parseTup`). The PRF output is read as the extraction coin vector (`coinsOf`; the PRF
hypotheses fix its length to `r_ext(λ)`). Coins of key generation and encryption are split in the
order listed. -/
noncomputable def unsignedCHK (M Id : ℕ → Str → Prop) (o : Obs) (R : PKE) (I : IBE) (P : PRF) :
    PKE where
  keyCoins := fun lam => R.keyCoins lam + I.setupCoins lam + P.keyCoins lam
  encCoins := fun lam => lam + R.encCoins lam + I.encCoins lam
  keyGen := fun lam r =>
    (BeyondDS.tup [(R.keyGen lam (cL (cL r))).1, (I.setup lam (cR (cL r))).1],
      BeyondDS.tup [(R.keyGen lam (cL (cL r))).2, (I.setup lam (cR (cL r))).2, P.gen lam (cR r)])
  enc := fun lam pk m ρ =>
    BeyondDS.tup [R.enc lam (fld pk 0) m (cR (cL ρ)), List.ofFn (cL (cL ρ)),
      I.enc lam (fld pk 1) (List.ofFn (cL (cL ρ))) (o.q lam (some m)) (cR ρ)]
  dec := fun lam sk C =>
    match parseTup 3 C with
    | some [d, i, a] =>
      if Id lam i then
      match I.dec lam (I.extract lam (fld sk 1) i
          (coinsOf (I.extCoins lam) (P.eval lam (fld sk 2) i))) a with
      | some y => if o.valid lam y then norm M o lam y (R.dec lam (fld sk 0) d) else none
      | none => none
      else none
    | _ => none

end Supplement

end RestrictedDec


