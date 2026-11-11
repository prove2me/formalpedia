-- Prove2me | Definitions.Def_AnyWE_CEFCorrectness_WEPrime
-- name    : AnyWE_CEFCorrectness_WEPrime
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:53:13.62052+00:00
-- url     : https://prove2.me/theorems/45023812-e9ab-4e61-b540-3e9197b208fc
-- title:
--   The transformed witness encryption $\mathrm{WE}'$ of Algorithm 3 (with $N=m$)
-- statement:
--   Given the relation circuits $R$, $\mathrm{Com}$, $G$, a NIWI for $R^\vee_{\mathrm{gate}}$ and a witness encryption scheme $\mathrm{WE}$ for $R_{\mathrm{NIZK}}$, the scheme $\mathrm{WE}'$ for $R$ (instance length $n$, witness length $m$) is:
--   - $\mathrm{WE}'.\mathrm{Enc}(1^\lambda,x,b)$: $\mathrm{crs}\leftarrow\Pi.\mathrm{Gen}$; $\Gamma\leftarrow\mathrm{WE.Enc}(1^\lambda,(\mathrm{crs},x),b)$; output $\mathrm{ct}=(\mathrm{crs},\Gamma)$.
--   - $\mathrm{WE}'.\mathrm{Dec}(\mathrm{ct},x,w)$: parse $\mathrm{ct}=(\mathrm{crs},\Gamma)$; if $R(x,w)=0$ output $\bot$; otherwise $\pi\leftarrow\Pi.P(\mathrm{crs},x,w)$ and output $\mathrm{WE.Dec}(\Gamma,(\mathrm{crs},x),\pi)$.
--
--   The encryption tape is $(\text{coins of }\Pi.\mathrm{Gen},\text{coins of WE.Enc})$ and the decryption tape is $(\text{coins of }\Pi.P,\text{coins of WE.Dec})$; both algorithms are circuits composed from the circuits of their parts.
--
--   This is the transformation of the paper's main result: it uses $\mathrm{WE}$ as a black box and needs no proof of its correctness.
--
--   **Formalization Note.** The witness bound is $N=m$ (proof of Corollary 7.6), so $|x|=n_x$ and $|w|\le N$ always hold and there are no malformed encodings. The output $(\mathit{valid},\mathit{bit})$ is normalized so that $\bot$ is $(0,0)$.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), pp. 61-62, §7.2 and Algorithm 3; p. 64 (proof of Corollary 7.6: N = n_w)

import Mathlib
import Definitions.Def_AnyWE_CEFCorrectness_GateNIZK
set_option autoImplicit false

/-!
# The transformed witness encryption WE′ of Algorithm 3

Jain, Jin, Mathialagan, *SNARGs from any Witness Encryption, and More*, STOC 2027 submission
(manuscript sha256 9bc2f227…), §7.2 pp. 61–62, Algorithm 3, with the NIZK of Algorithm 1 and the
witness-length bound `N = n_w = m(λ)` (proof of Corollary 7.6, p. 64).

`WE` is a witness encryption scheme for `R_NIZK`; `WE′` is a witness encryption scheme for the
relation `R` given by the circuits `RC` (instance length `n`, witness length `m`).
-/

namespace AnyWE.CEFCorrectness

namespace WEPrime

open GateNIZK

variable (n m : ℕ → ℕ) (RC : ∀ lam, Circuit (n lam + m lam) 1) (Com : Commitment) (G : PRG)
  (NIWI : NIWIScheme (orGateRel n m RC Com G)) (WE : WEScheme (nizkRel n m RC Com G NIWI))

/-- **`WE′.Enc(1^λ, N, x, b)` (Algorithm 3)**: `crs ← NIZK.Gen(1^λ, n_x, N, R)`,
`Γ ← WE.Enc(1^λ, ℓ_π, (crs, x), b)`, output `ct = (crs, Γ)`. -/
def enc (lam : ℕ) :
    Circuit (n lam + 1 + (genTape n m RC Com G NIWI lam + WE.encTape lam))
      (crsLen n m RC Com G NIWI lam + WE.ctLen lam) :=
  Circuit.build _ _ fun inp => do
    let x := vleft (vleft inp)
    let b := vright (vleft inp)
    let crs ← BM.embed (gen n m RC Com G NIWI lam) (vleft (vright inp))
    let Γ ← BM.embed (WE.enc lam) (Fin.append (Fin.append (Fin.append crs x) b) (vright (vright inp)))
    pure (Fin.append crs Γ)

/-- **`WE′.Dec(ct, x, w)` (Algorithm 3)**: parse `ct = (crs, Γ)`; if `R(x, w) = 0` output `⊥`;
otherwise `π ← NIZK.P(crs, x, w)` and output `WE.Dec(Γ, (crs, x), π)`. The output `(valid, bit)`
is normalized so that `⊥` is `(0, 0)`. (At the fixed lengths there are no malformed encodings and
`|x| = n_x`, `|w| = N` always hold.) -/
def dec (lam : ℕ) :
    Circuit (crsLen n m RC Com G NIWI lam + WE.ctLen lam + n lam + m lam +
      (proveTape n m RC Com G NIWI lam + WE.decTape lam)) 2 :=
  Circuit.build _ _ fun inp => do
    let ct := vleft (vleft (vleft inp))
    let crs := vleft ct
    let Γ := vright ct
    let x := vright (vleft (vleft inp))
    let w := vright (vleft inp)
    let coins := vright inp
    let ok ← BM.embed (RC lam) (Fin.append x w)
    let pf ← BM.embed (prove n m RC Com G NIWI lam)
      (Fin.append (Fin.append (Fin.append crs x) w) (vleft coins))
    let d ← BM.embed (WE.dec lam)
      (Fin.append (Fin.append (Fin.append Γ (Fin.append crs x)) pf) (vright coins))
    let valid ← BM.and (ok 0) (d 0)
    let bit ← BM.and valid (d 1)
    pure ![valid, bit]

/-- **The scheme `WE′` (Algorithm 3)** as a witness encryption scheme for `R` at instance length
`n` and witness length `m`. -/
def scheme : WEScheme (relOf n m RC) where
  ctLen := fun lam => crsLen n m RC Com G NIWI lam + WE.ctLen lam
  encTape := fun lam => genTape n m RC Com G NIWI lam + WE.encTape lam
  decTape := fun lam => proveTape n m RC Com G NIWI lam + WE.decTape lam
  enc := enc n m RC Com G NIWI WE
  dec := dec n m RC Com G NIWI WE

end WEPrime

end AnyWE.CEFCorrectness


