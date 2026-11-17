-- Prove2me | Definitions.Def_RestrictedDec_Supplement_nyAd
-- name    : RestrictedDec_Supplement_nyAd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:33:30.521739+00:00
-- url     : https://prove2.me/theorems/42586a38-bc3d-4010-baf5-e7f967376f2e
-- title:
--   The adaptive signed Naor–Yung compiler $\Pi_q$ (B.4)
-- statement:
--   For an observation $q$ with $\mathrm{Valid}_q,\mathrm{Rep}_q$, a residual scheme $R$, a label scheme $L$, a NIZK $N$ and a one-time signature $S$:
--
--   1. The relation (B.4): for $x=(pk_0,pk_1,vk,d,a_0,a_1)$ and $w=(y,r_0,r_1)$, $R_q(x;w)=1$ iff $\mathrm{Valid}_q(y)=1$, $r_0,r_1\in\mathrm{Coins}_L$, $a_0=\mathrm{Enc}_{pk_0}(y;r_0)$, $a_1=\mathrm{Enc}_{pk_1}(y;r_1)$. Well-formed statements are the 6-tuples.
--   2. $\mathrm{KeyGen}$: $(pk_R,sk_R)$, $(pk_0,sk_0)$, $(pk_1,sk_1)$, $crs$; $pk=(pk_R,pk_0,pk_1,crs)$, $sk=(sk_R,sk_0)$.
--   3. $\mathrm{Enc}(m)$: $y=q(m)$, $d\leftarrow\mathrm{Enc}_{pk_R}(m)$, $a_k\leftarrow\mathrm{Enc}_{pk_k}(y;r_k)$, $(sigsk,vk)\leftarrow\mathrm{SGen}$, $\pi\leftarrow\mathrm{Prove}(crs,x;(y,r_0,r_1))$, $B=(vk,d,a_0,a_1,\pi)$, $\sigma\leftarrow\mathrm{Sign}_{sigsk}(B)$; $C=(B,\sigma)$.
--   4. $\mathrm{Dec}(C)$: reject malformed encodings; $\bot$ if the signature or the proof fails; $y=\mathrm{Dec}_{sk_0}(a_0)$, $\bot$ if $\mathrm{Valid}_q(y)=0$; output $\mathrm{Norm}_{q,y}(\mathrm{Dec}_{sk_R}(d))$.
--
--   **Formalization Note** The secret key also stores $pk_0,pk_1,crs$.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.3, (B.4), p.39

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_Supplement_interact
import Definitions.Def_RestrictedDec_Supplement_Obs
import Definitions.Def_RestrictedDec_Supplement_NIZK
import Definitions.Def_RestrictedDec_Supplement_OTS
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- The **label-consistency relation** (B.4) of the adaptive Naor–Yung compiler:
`R_q(x; (y, r₀, r₁)) = 1` iff `x = (pk₀, pk₁, vk, d, a₀, a₁)`, `Valid_q(1^λ, y) = 1`,
`r₀, r₁ ∈ Coins_L`, `a₀ = Enc_{pk₀}(y; r₀)` and `a₁ = Enc_{pk₁}(y; r₁)`; `vk` and `d` are part of
the statement but unconstrained.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), (B.4), p.39.

**Formalization Note.** As in `relB1`: `x = tup [pk₀, pk₁, vk, d, a₀, a₁]`, `w = tup [y, r₀, r₁]`,
`r ∈ Coins_L` is `|r| = encCoins_L(λ)`. -/
def relB4 (L : PKE) (o : Obs) (lam : ℕ) (x w : Str) : Prop :=
  ∃ pk0 pk1 vk d a0 a1 y r0 r1 : Str,
    x = BeyondDS.tup [pk0, pk1, vk, d, a0, a1] ∧ w = BeyondDS.tup [y, r0, r1] ∧
    o.valid lam y = true ∧ r0.length = L.encCoins lam ∧ r1.length = L.encCoins lam ∧
    a0 = L.enc lam pk0 y (coinsOf (L.encCoins lam) r0) ∧
    a1 = L.enc lam pk1 y (coinsOf (L.encCoins lam) r1)

/-- The **public instance space** of (B.4): the well-formed statements
`x = (pk₀, pk₁, vk, d, a₀, a₁)` (Definition 11, p.33). -/
def wfB4 (_lam : ℕ) (x : Str) : Prop :=
  ∃ pk0 pk1 vk d a0 a1 : Str, x = BeyondDS.tup [pk0, pk1, vk, d, a0, a1]

/-- The **adaptive signed Naor–Yung compiler** `Π_q` (App. B.3) for the observation `q` with
`Valid_q`, `Rep_q`, from a residual scheme `R`, a label scheme `L`, a NIZK `N` for (B.4) and a
one-time signature `S`:
1. `KeyGen`: `(pk_R, sk_R)`, `(pk₀, sk₀)`, `(pk₁, sk₁)`, `crs`; `pk = (pk_R, pk₀, pk₁, crs)`,
   `sk = (sk_R, sk₀, pk₀, pk₁, crs)`;
2. `Enc_pk(m)`: `y = q(m)`, `d ← Enc_{pk_R}(m)`, `a_k ← Enc_{pk_k}(y; r_k)`,
   `(sigsk, vk) ← SGen(1^λ)`, `x = (pk₀, pk₁, vk, d, a₀, a₁)`, `π ← Prove(crs, x; (y, r₀, r₁))`,
   `B = (vk, d, a₀, a₁, π)`, `σ ← Sign_sigsk(B)`, `C = (B, σ)`;
3. `Dec_sk(C)`: reject malformed encodings; `⊥` if the signature or the proof fails verification;
   `y = Dec_{sk₀}(a₀)`, `⊥` if `Valid_q(y) = 0`; output `Norm_{q,y}(Dec_{sk_R}(d))`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.3, p.39.

**Formalization Note.** `B = tup [vk, d, a₀, a₁, π]` and `C = tup [B, σ]`; "malformed" means "not
the code of a pair whose first entry is the code of a 5-tuple". The secret key also stores
`pk₀, pk₁, crs`. Encryption coins are split as `Enc_R`, `Enc_{pk₀}`, `Enc_{pk₁}`, `SGen`,
`Prove`, `Sign`. -/
noncomputable def nyAd (M : ℕ → Str → Prop) (o : Obs) (R L : PKE) (N : NIZK) (S : OTS) : PKE where
  keyCoins := fun lam => R.keyCoins lam + L.keyCoins lam + L.keyCoins lam + N.crsCoins lam
  encCoins := fun lam => R.encCoins lam + L.encCoins lam + L.encCoins lam + S.keyCoins lam +
    N.proveCoins lam + S.signCoins lam
  keyGen := fun lam r =>
    let kR := R.keyGen lam (cL (cL (cL r)))
    let k0 := L.keyGen lam (cR (cL (cL r)))
    let k1 := L.keyGen lam (cR (cL r))
    let crs := N.setup lam (cR r)
    (BeyondDS.tup [kR.1, k0.1, k1.1, crs], BeyondDS.tup [kR.2, k0.2, k0.1, k1.1, crs])
  enc := fun lam pk m ρ =>
    let y := o.q lam (some m)
    let d := R.enc lam (fld pk 0) m (cL (cL (cL (cL (cL ρ)))))
    let a0 := L.enc lam (fld pk 1) y (cR (cL (cL (cL (cL ρ)))))
    let a1 := L.enc lam (fld pk 2) y (cR (cL (cL (cL ρ))))
    let kS := S.gen lam (cR (cL (cL ρ)))
    let x := BeyondDS.tup [fld pk 1, fld pk 2, kS.2, d, a0, a1]
    let π := N.prove lam (fld pk 3) x
      (BeyondDS.tup [y, List.ofFn (cR (cL (cL (cL (cL ρ))))), List.ofFn (cR (cL (cL (cL ρ))))])
      (cR (cL ρ))
    let B := BeyondDS.tup [kS.2, d, a0, a1, π]
    BeyondDS.tup [B, S.sign lam kS.1 B (cR ρ)]
  dec := fun lam sk C =>
    match parseTup 2 C with
    | some [B, σ] =>
      match parseTup 5 B with
      | some [vk, d, a0, a1, π] =>
        if S.vrf lam vk B σ = true ∧
            N.verify lam (fld sk 4) (BeyondDS.tup [fld sk 2, fld sk 3, vk, d, a0, a1]) π = true then
          match L.dec lam (fld sk 1) a0 with
          | some y => if o.valid lam y then norm M o lam y (R.dec lam (fld sk 0) d) else none
          | none => none
        else none
      | _ => none
    | _ => none

end Supplement

end RestrictedDec


