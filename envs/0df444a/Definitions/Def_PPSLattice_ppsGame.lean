-- Prove2me | Definitions.Def_PPSLattice_ppsGame
-- name    : PPSLattice_ppsGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:37:11.606551+00:00
-- url     : https://prove2.me/theorems/924aca00-d49e-4df0-8c77-70618f7dd8fe
-- title:
--   The experiments of mode indistinguishability and payload hiding
-- statement:
--   The experiment outputs $1$ iff the adversary's guess $b'$ equals $b$:
--
--   1. The adversary outputs $(N,i^*)$ (mode indistinguishability) or $(N,i^*,\mu_{i^*})$ (payload hiding); it must have $i^*\in[N]$ and, for payload hiding, $\mu_{i^*}\in\{0,1\}^\lambda$ (otherwise the output is a uniform bit).
--   2. $b\leftarrow\{0,1\}$, $\mathrm{crs}\leftarrow\mathrm{GSetup}(1^\lambda,N)$, $\mathrm{msk}\leftarrow\mathrm{MSKGen}(\mathrm{crs})$; if $b=0$, $\mathrm{ct}_{i^*}\leftarrow\mathrm{pkEnc}(i^*)$; if $b=1$, $\mathrm{ct}_{i^*}\leftarrow\mathrm{skEnc}(\mathrm{msk},i^*,\mu_{i^*})$, where $\mu_{i^*}\leftarrow\{0,1\}^\lambda$ is uniform (mode indistinguishability) or the adversary's message (payload hiding).
--   3. The adversary receives $(\mathrm{crs},\mathrm{ct}_{i^*})$ and continues with oracle access until it names $S$, receives $\mathrm{sk}_S$ and guesses.
--
--   **Formalization Note** $N$ is chosen by the adversary in binary, without the bound $N\le2^\lambda$ of correctness and compactness, as printed.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, p.18

import Mathlib
import Definitions.Def_PPSLattice_ppsRun
import Definitions.Def_AvgPHETH_uniformDist
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace PPSLattice

/-- The **security experiments of Definition 4.1**, with output `1` iff the adversary's guess `b′`
equals the challenge bit `b`; `payload = false` is mode indistinguishability and `payload = true`
payload hiding.
1. The adversary's first move `tup [N, i*]` (mode indistinguishability) or `tup [N, i*, µ_{i*}]`
   (payload hiding), with `N`, `i*` in binary, must satisfy `i* ∈ [N]` and, for payload hiding,
   `µ_{i*} ∈ {0,1}^λ`; otherwise the output is a uniform bit.
2. `b ← {0,1}`, `crs ← GSetup(1^λ, N)`, `msk ← MSKGen(crs)`; if `b = 0`, `ct_{i*} ← pkEnc(i*)`; if
   `b = 1`, `ct_{i*} ← skEnc(msk, i*, µ_{i*})` where `µ_{i*} ← {0,1}^λ` is uniform (mode
   indistinguishability) or the adversary's message (payload hiding).
3. The adversary receives `(crs, ct_{i*})` and continues as in `ppsRun`, with `p(λ)` further
   activations.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Mode Indistinguishability and Payload Hiding, p.18.

**Formalization Note.** `N` is chosen by the adversary, in binary, with no upper bound beyond the
length of its output; the bound `N ≤ 2^λ` of correctness and compactness does not apply to the
games, as printed. Drawing `b` after the first move is the order of the printed experiment. -/
noncomputable def ppsGame (payload : Bool) (E : PPS) (A : RestrictedDec.Adversary) (lam : ℕ) :
    PMF Bool :=
  (A.activate lam [] (BeyondDS.tup [])).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let N := decBin (fs.getD 0 [])
    let istar := decBin (fs.getD 1 [])
    let muA := fs.getD 2 []
    if istar ∈ Finset.Icc 1 N ∧ (payload = true → muA.length = lam) then
      (PMF.uniformOfFintype Bool).bind fun b =>
        (E.gsetup lam N).bind fun crs =>
          (E.mskgen lam N crs).bind fun msk =>
            (if b then
                ((if payload then PMF.pure muA else AvgPHETH.uniformDist lam).bind fun mu =>
                  E.skEnc lam N crs msk istar mu)
              else E.pkEnc lam N crs istar).bind fun ct =>
              (ppsRun E A lam N crs msk istar payload (A.p.eval lam) r0.1
                  (BeyondDS.tup [crs, ct])).map fun b' => decide (b' = b)
    else PMF.uniformOfFintype Bool

end PPSLattice


