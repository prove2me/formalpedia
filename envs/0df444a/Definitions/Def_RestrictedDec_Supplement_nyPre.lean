-- Prove2me | Definitions.Def_RestrictedDec_Supplement_nyPre
-- name    : RestrictedDec_Supplement_nyPre
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:31:45.847839+00:00
-- url     : https://prove2.me/theorems/99090916-b5c5-4208-a6d5-8b8d2c1cf6c9
-- title:
--   The pre-challenge Naor–Yung compiler (B.1)–(B.2)
-- statement:
--   For an observation $q$ with $\mathrm{Valid}_q,\mathrm{Rep}_q$, a residual scheme $R$, a label scheme $L$ and a NIZK $N$:
--
--   1. The relation (B.1): for $x=(pk_0,pk_1,d,a_0,a_1)$ and $w=(y,r_0,r_1)$, $R_q(x;w)=1$ iff $\mathrm{Valid}_q(y)=1$, $r_0,r_1\in\mathrm{Coins}_L$, $a_0=\mathrm{Enc}_{pk_0}(y;r_0)$ and $a_1=\mathrm{Enc}_{pk_1}(y;r_1)$. The residual $d$ is in the statement but unconstrained. Well-formed statements are the 5-tuples.
--   2. $\mathrm{KeyGen}$: independent $(pk_R,sk_R)$, $(pk_0,sk_0)$, $(pk_1,sk_1)$ and $crs\leftarrow\mathrm{Setup}$.
--   3. $\mathrm{Enc}(m)=(d,a_0,a_1,\pi)$ with $d\leftarrow\mathrm{Enc}_{pk_R}(m)$, $a_b\leftarrow\mathrm{Enc}_{pk_b}(q(m);r_b)$ and $\pi\leftarrow\mathrm{Prove}(crs,x,(q(m),r_0,r_1))$.
--   4. $\mathrm{Dec}(C)$: reject malformed ciphertexts and invalid proofs; $y=\mathrm{Dec}_{sk_0}(a_0)$, reject if invalid; output $\mathrm{Norm}_q(y,\mathrm{Dec}_{sk_R}(d))$ (B.2).
--
--   **Formalization Note** The secret key also stores $pk_0,pk_1,crs$, which decryption needs to form and check the statement; $r\in\mathrm{Coins}_L$ means that $r$ has the length of $L$'s encryption coins.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.2, (B.1)–(B.2), pp.36–37

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_Supplement_interact
import Definitions.Def_RestrictedDec_Supplement_Obs
import Definitions.Def_RestrictedDec_Supplement_NIZK
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- The **label-consistency relation** (B.1) of the pre-challenge Naor–Yung compiler, for the
label scheme `L` and the observation `o`: `R_q(x; (y, r₀, r₁)) = 1` iff
`x = (pk₀, pk₁, d, a₀, a₁)`, `Valid_q(1^λ, y) = 1`, `r₀, r₁ ∈ Coins_L`, `a₀ = Enc_{pk₀}(y; r₀)` and
`a₁ = Enc_{pk₁}(y; r₁)`. The residual ciphertext `d` is part of the statement but unconstrained.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), (B.1), p.36.

**Formalization Note.** `x = tup [pk₀, pk₁, d, a₀, a₁]`, `w = tup [y, r₀, r₁]`; `r ∈ Coins_L` is
`|r| = encCoins_L(λ)` (every coin vector of `L`, see `kcFail`), and `r` is used as that vector. -/
def relB1 (L : PKE) (o : Obs) (lam : ℕ) (x w : Str) : Prop :=
  ∃ pk0 pk1 d a0 a1 y r0 r1 : Str,
    x = BeyondDS.tup [pk0, pk1, d, a0, a1] ∧ w = BeyondDS.tup [y, r0, r1] ∧
    o.valid lam y = true ∧ r0.length = L.encCoins lam ∧ r1.length = L.encCoins lam ∧
    a0 = L.enc lam pk0 y (coinsOf (L.encCoins lam) r0) ∧
    a1 = L.enc lam pk1 y (coinsOf (L.encCoins lam) r1)

/-- The **public instance space** of (B.1): the syntactically well-formed statements
`x = (pk₀, pk₁, d, a₀, a₁)` (Definition 11, p.33; Theorem 8, p.37). -/
def wfB1 (_lam : ℕ) (x : Str) : Prop :=
  ∃ pk0 pk1 d a0 a1 : Str, x = BeyondDS.tup [pk0, pk1, d, a0, a1]

/-- The **pre-challenge Naor–Yung compiler** (B.1)–(B.2) for the observation `q` with `Valid_q`,
`Rep_q`, built from a residual scheme `R`, a label scheme `L` (two independent keys) and a NIZK `N`
for (B.1):
1. `KeyGen`: independent `(pk_R, sk_R)`, `(pk₀, sk₀)`, `(pk₁, sk₁)` and `crs ← Setup(1^λ)`;
   `pk = (pk_R, pk₀, pk₁, crs)`, `sk = (sk_R, sk₀, pk₀, pk₁, crs)`;
2. `Enc_pk(m)`: `d ← Enc_{pk_R}(m)`, `a_b ← Enc_{pk_b}(q(m); r_b)` (`b = 0, 1`),
   `π ← Prove(crs, x, (q(m), r₀, r₁))` for `x = (pk₀, pk₁, d, a₀, a₁)`; `C = (d, a₀, a₁, π)`;
3. `Dec_sk(C)`: reject malformed ciphertexts and invalid proofs; `y = Dec_{sk₀}(a₀)`, reject if
   `y = ⊥` or `y` is invalid; output `Norm_q(y, Dec_{sk_R}(d))` (B.2).
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.2, pp.36–37 ("An
encryption of m is C = (d, a0, a1, π) … The decryption algorithm rejects malformed ciphertexts and
invalid proofs. Otherwise it decrypts a0 to a candidate label y, rejects if y is invalid, decrypts d
to z, and returns (B.2)").

**Formalization Note.** The secret key also stores `pk₀, pk₁, crs`, which decryption needs to form
and verify the statement. Encryption coins are split as `Enc_R`, `Enc_{pk₀}`, `Enc_{pk₁}`,
`Prove`. -/
noncomputable def nyPre (M : ℕ → Str → Prop) (o : Obs) (R L : PKE) (N : NIZK) : PKE where
  keyCoins := fun lam => R.keyCoins lam + L.keyCoins lam + L.keyCoins lam + N.crsCoins lam
  encCoins := fun lam => R.encCoins lam + L.encCoins lam + L.encCoins lam + N.proveCoins lam
  keyGen := fun lam r =>
    let kR := R.keyGen lam (cL (cL (cL r)))
    let k0 := L.keyGen lam (cR (cL (cL r)))
    let k1 := L.keyGen lam (cR (cL r))
    let crs := N.setup lam (cR r)
    (BeyondDS.tup [kR.1, k0.1, k1.1, crs], BeyondDS.tup [kR.2, k0.2, k0.1, k1.1, crs])
  enc := fun lam pk m ρ =>
    let y := o.q lam (some m)
    let d := R.enc lam (fld pk 0) m (cL (cL (cL ρ)))
    let a0 := L.enc lam (fld pk 1) y (cR (cL (cL ρ)))
    let a1 := L.enc lam (fld pk 2) y (cR (cL ρ))
    let x := BeyondDS.tup [fld pk 1, fld pk 2, d, a0, a1]
    BeyondDS.tup [d, a0, a1, N.prove lam (fld pk 3) x
      (BeyondDS.tup [y, List.ofFn (cR (cL (cL ρ))), List.ofFn (cR (cL ρ))]) (cR ρ)]
  dec := fun lam sk C =>
    match parseTup 4 C with
    | some [d, a0, a1, π] =>
      if N.verify lam (fld sk 4) (BeyondDS.tup [fld sk 2, fld sk 3, d, a0, a1]) π = true then
        match L.dec lam (fld sk 1) a0 with
        | some y => if o.valid lam y then norm M o lam y (R.dec lam (fld sk 0) d) else none
        | none => none
      else none
    | _ => none

end Supplement

end RestrictedDec


