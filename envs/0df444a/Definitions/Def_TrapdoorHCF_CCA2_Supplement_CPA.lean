-- Prove2me | Definitions.Def_TrapdoorHCF_CCA2_Supplement_CPA
-- name    : TrapdoorHCF_CCA2_Supplement_CPA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:39:32.647565+00:00
-- url     : https://prove2.me/theorems/8d439bc7-8d67-4b68-8919-55657f6813f6
-- title:
--   Statistical distance, TDHF security, IND-CPA security and the Section A.1 encryption scheme
-- statement:
--   This file fixes four notions used by the chosen-plaintext half of the source.
--
--   1. **Statistical distance.** For probability mass functions $p,q$ on an arbitrary set $\Omega$,
--   $$\Delta(p,q)=\tfrac12\sum_{\omega\in\Omega}\bigl|p(\omega)-q(\omega)\bigr|.$$
--   The sum is taken over every outcome; no finiteness of $\Omega$ is assumed.
--
--   2. **TDHF security** (Definition 10). For a trapdoor hardcore function $T$ with hardcore length $l(\lambda)$, sample $(pk,sk)\leftarrow\mathrm{KGen}(1^\lambda)$ and $x\leftarrow D_\lambda$. A uniform probabilistic polynomial-time adversary receives $(1^\lambda,pk,\mathrm{Eval}(pk,x),z)$, where $z=\mathrm{hEval}(pk,x)$ in the real experiment and $z$ is a uniform string of $l(\lambda)$ bits in the random one. Its advantage is the absolute difference of its output-one probabilities. $T$ is *secure* if it is perfectly correct and every such adversary has negligible advantage.
--
--   3. **IND-CPA security** (Definition 2 with atk = CPA). The classical two-stage game with no decryption access: the first stage sees $(1^\lambda,pk)$ and names $m_0,m_1\in\{0,1\}^{n(\lambda)}$; invalid messages make the experiment output $0$; the second stage receives $\mathrm{Enc}(pk,m_b)$ and its state. The scheme is IND-CPA secure if every uniform PPT adversary has negligible advantage. No correctness is part of this notion.
--
--   4. **The Section A.1 scheme** $\mathrm{KEM}(T)$. Keys are those of $T$. To encrypt $m$, sample an input $r\leftarrow D_\lambda$ and output $(\mathrm{Eval}(pk,r),\ \mathrm{hEval}(pk,r)\oplus m)$. To decrypt $(ct_1,ct_2)$, compute $z=\mathrm{pInv}(sk,ct_1)$; output $\perp$ if $z=\perp$, and otherwise $z\oplus ct_2$.
--
--   These are the objects of Theorems 1, 5 and 6 and the base of the lossy constructions.
--
--   **Formalization Note** The adversary model, the stage runner `runStage` and the advantage are the published base definitions; the IND-CPA game is the base IND-CCA2 game with both oracles removed. Ciphertext pairs are tuple codes. Decryption of $\mathrm{KEM}(T)$ also returns $\perp$ when $|z|\ne|ct_2|$, which happens only for strings outside the ciphertext space and makes decryption output elements of $\{0,1\}^{l(\lambda)}\cup\{\perp\}$.
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Notation 8, p.10; Definition 2, p.11; Definition 10, p.16; Section A.1, p.32

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Constructions
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Notation 8, p.10: statistical distance `Δ(X,Y) = ½ Σ_ω |Pr[X=ω] − Pr[Y=ω]|`, over every
outcome `ω` of an arbitrary (possibly infinite) type. On PMFs the series is summable. -/
noncomputable def sd {α : Type} (p q : PMF α) : ℝ :=
  (1 / 2) * ∑' ω, |(p ω).toReal - (q ω).toReal|

/-- Definition 10, p.16. One oracle-free stage on input `(1^λ, pk, Eval(pk,x), z)`, with
`x ← D_λ` and `z` the designated value (`b = false`) or `l(λ)` uniform bits (`b = true`).
The first bit of the output is the guess; exhaustion outputs 0. -/
noncomputable def expTDHF (l : ℕ → ℕ) (T : TDHF) (A : RestrictedDec.Adversary) (b : Bool)
    (lam : ℕ) : PMF Bool := do
  let keys ← T.keyLaw lam
  let x ← T.inputLaw lam
  let u ← coinsLaw (l lam)
  let y := T.eval lam keys.1 x
  let z := if b then List.ofFn u else T.hEval lam keys.1 x
  let r ← runStage A lam (fun _ => none) (A.p.eval lam + 1) []
    (BeyondDS.tup [encNat lam, keys.1, y, z])
  pure ((r.output.getD []).headD false)

noncomputable def advTDHF (l : ℕ → ℕ) (T : TDHF) (A : RestrictedDec.Adversary) : ℕ → ℝ :=
  advantage (expTDHF l T A false) (expTDHF l T A true)

/-- Definition 10, p.16: "A perfectly correct TDHF is secure if" every uniform PPT adversary
has negligible advantage. Perfect correctness (Definition 9) is part of the notion. -/
def IsSecureTDHF (l : ℕ → ℕ) (T : TDHF) : Prop :=
  T.PerfectlyCorrect ∧
    ∀ A : RestrictedDec.Adversary, A.Valid → NoisyOWMPC.Negligible (advTDHF l T A)

/-- Definition 2, p.11, with atk = CPA: the base `expCCA2` with no decryption access in either
stage. Invalid messages and exhausted stages output 0 in both experiments. -/
noncomputable def expCPA (n : ℕ → ℕ) (P : RestrictedDec.PKE)
    (A : RestrictedDec.Adversary) (b : Bool) (lam : ℕ) : PMF Bool := do
  let keys ← P.keyLaw lam
  let pre ← runStage A lam (fun _ => none) (A.p.eval lam + 1) []
    (BeyondDS.tup [encNat lam, keys.1])
  match pre.output with
  | none => pure false
  | some out =>
      let ms := BeyondDS.untup out
      let m0 := ms.getD 0 []
      let m1 := ms.getD 1 []
      if m0.length = n lam ∧ m1.length = n lam ∧ m0.length = m1.length then
        let ct ← P.encLaw lam keys.1 (if b then m1 else m0)
        let post ← runStage A lam (fun _ => none) pre.fuel pre.state
          (BeyondDS.tup [ct, pre.state])
        pure ((post.output.getD []).headD false)
      else pure false

noncomputable def advCPA (n : ℕ → ℕ) (P : RestrictedDec.PKE)
    (A : RestrictedDec.Adversary) : ℕ → ℝ :=
  advantage (expCPA n P A false) (expCPA n P A true)

/-- Definition 2, p.11: IND-CPA security. No correctness clause. -/
def INDCPA (n : ℕ → ℕ) (P : RestrictedDec.PKE) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid → NoisyOWMPC.Negligible (advCPA n P A)

/-- Bitwise exclusive or `⊕` of two strings (of equal length wherever it is used). -/
def xorStr (a b : Str) : Str := List.zipWith xor a b

/-- Section A.1, p.32. The encryption randomness is an input `r ∈ D_λ`, drawn by the TDHF
sampler on the encryption coins. The ciphertext `(ct1, ct2)` is the tuple code
`tup [Eval(pk,r), hEval(pk,r) ⊕ m]`. Decryption returns `⊥` when `pInv` does (p.32), and also
when `|ct2| ≠ |z|`, which happens only outside the ciphertext space `C_λ`. -/
def kemPKE (T : TDHF) : RestrictedDec.PKE where
  keyCoins := T.keyCoins
  encCoins := T.sampCoins
  keyGen := T.keyGen
  enc := fun lam pk m r =>
    BeyondDS.tup [T.eval lam pk (T.samp lam r), xorStr (T.hEval lam pk (T.samp lam r)) m]
  dec := fun lam sk c =>
    let fields := BeyondDS.untup c
    let ct1 := fields.getD 0 []
    let ct2 := fields.getD 1 []
    match T.pInv lam sk ct1 with
    | none => none
    | some z => if z.length = ct2.length then some (xorStr z ct2) else none

end TrapdoorHCF.CCA2.Supplement


