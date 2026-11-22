-- Prove2me | Definitions.Def_CertRandQROM_Supplement_honestRejProb
-- name    : CertRandQROM_Supplement_honestRejProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:43:09.610307+00:00
-- url     : https://prove2.me/theorems/421a646e-1936-4b87-86c2-f2c0ba159368
-- title:
--   Output law of the honest prover $\mathrm{Prove}^h$ of Construction 6.2 and its rejection probability
-- statement:
--   Fix a code $C\subseteq\Sigma^n$ ($\Sigma=\mathbb F_q^m$), a decoding radius $\tau$, a trial count $L$ and an oracle $h:[n]\times\Sigma\to\{0,1\}$; write $T_i=\{e\in\Sigma:\ h(i,e)=0\}$.
--
--   1. **Step 1.** For each $i\in[n]$ the prover tries up to $L$ times to prepare $|\phi_i\rangle=|T_i|^{-1/2}\sum_{e\in T_i}|e\rangle$; each trial succeeds with probability $|T_i|/|\Sigma|$. If some coordinate fails all its trials the prover outputs $\bot$. The probability that it does not abort is
--   $$
--   s(h)=\prod_{i\in[n]}\Big(1-\big(1-|T_i|/|\Sigma|\big)^{L}\Big).
--   $$
--   2. **Steps 2–5.** With $|\phi\rangle=\bigotimes_i|\phi_i\rangle$ and $|\psi\rangle=|C|^{-1/2}\sum_{x\in C}|x\rangle$, the prover forms $|\eta\rangle=\mathrm{QFT}^{\otimes n}_\Sigma|\psi\rangle\otimes\mathrm{QFT}^{\otimes n}_\Sigma|\phi\rangle$ and applies $U_{\mathrm{add}}|x\rangle|e\rangle=|x\rangle|x+e\rangle$, then $U_{\mathrm{decode}}|x\rangle|z\rangle=|x-\mathrm{Decode}_{C^\perp}(z)\rangle|z\rangle$, then $I\otimes(\mathrm{QFT}^{-1}_\Sigma)^{\otimes n}$, obtaining a state $|\mathrm{fin}\rangle$.
--   3. **Step 6.** It measures the second register and outputs the outcome $w$:
--   $$
--   \Pr[\pi=w]=s(h)\sum_{x'\in\Sigma^n}\big|\langle x',w|\mathrm{fin}\rangle\big|^2,\qquad \Pr[\pi=\bot]=1-s(h).
--   $$
--
--   The **rejection probability** is $\Pr[\mathrm{Verify}^h(\pi)=\bot]=\Pr[\pi=\bot]+\sum_{w\ \text{not correct}}\Pr[\pi=w]$, where $w$ is correct when $w\in C$ and $h(i,w_i)=0$ for all $i$. At security parameter $\lambda$ the construction uses $C=C_\lambda$, $\tau=\lfloor (k(\lambda)+1)/2\rfloor$ and $L=\lambda$.
--
--   This is the quantity whose average over the biased oracle the correctness property bounds.
--
--   **Formalization Note** `zeroSet` is $T_i$, `stepOneSucc` is $s(h)$, `phiVec`, `psiVec` are the amplitude functions of $|\phi\rangle$, $|\psi\rangle$, `finalState` is $|\mathrm{fin}\rangle$ as a function of the two registers, `proveOut` is the law on $\Sigma^n\cup\{\bot\}$ (`none` $=\bot$), `rejProb` the rejection probability and `honestRejProb F γ λ h` its value for the parameters of Construction 6.2 at $\lambda$. The trial outcomes of step 1 are integrated out exactly: given success the state is $|\phi\rangle$ whatever the history. When $T_i=\emptyset$ the law is $\bot$ with probability $1$.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Construction 6.2, pp.28–29 (PDF pp.30–31); Definition 6.1, Correctness, p.28 (PDF p.30); T_i^{H_i}, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_CertRandQROM_code
import Definitions.Def_CertRandQROM_IsCorrect
import Definitions.Def_CertRandQROM_Supplement_decodeDual
import Definitions.Def_CertRandQROM_Supplement_qft

set_option autoImplicit false

namespace CertRandQROM.Supplement

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n m : ℕ}

open Classical in
/-- `T_i^{H_i} = {e_i ∈ Σ : H_i(e_i) = 0}` (proof of Theorem 6.6, p.31 of Coladangelo et al.,
arXiv:2608.31112, sha256 b75095a2…), for an oracle `h : [n] × Σ → {0,1}` (`false` = `0`). -/
noncomputable def zeroSet (h : Fin n × (Fin m → K) → Bool) (i : Fin n) : Finset (Fin m → K) :=
  Finset.univ.filter fun e => h (i, e) = false

/-- **Step 1 of `Prove^h` succeeds** (Construction 6.2, step 1, pp.28–29): for each `i ∈ [n]`,
independently, up to `L` trials, each preparing the uniform superposition over `Σ`, evaluating
`H_i` coherently and measuring; a trial succeeds (leaving `|φ_i⟩`) with probability `|T_i|/|Σ|`.
The probability that no coordinate exhausts its `L` trials is
`Π_i (1 − (1 − |T_i|/|Σ|)^L)`; Construction 6.2 uses `L = λ`. -/
noncomputable def stepOneSucc (L : ℕ) (h : Fin n × (Fin m → K) → Bool) : ℝ :=
  ∏ i, (1 - (1 - ((zeroSet h i).card : ℝ) / (Fintype.card (Fin m → K) : ℝ)) ^ L)

/-- `|φ⟩ = |φ_1⟩ ⊗ ⋯ ⊗ |φ_n⟩`, `|φ_i⟩ = |T_i|^{−1/2} Σ_{e_i ∈ T_i} |e_i⟩` (Construction 6.2,
steps 1–2, pp.28–29). -/
noncomputable def phiVec (h : Fin n × (Fin m → K) → Bool) : (Fin n → Fin m → K) → ℂ :=
  fun e => ∏ i, if h (i, e i) = false then ((Real.sqrt (zeroSet h i).card)⁻¹ : ℂ) else 0

open Classical in
/-- `|ψ⟩ = |C|^{−1/2} Σ_{x ∈ C} |x⟩` (Construction 6.2, step 3, p.29). -/
noncomputable def psiVec (C : Finset (Fin n → Fin m → K)) : (Fin n → Fin m → K) → ℂ :=
  fun x => if x ∈ C then ((Real.sqrt C.card)⁻¹ : ℂ) else 0

/-- **The final state of `Prove^h` before the measurement** (Construction 6.2, steps 4–5, p.29),
given that step 1 succeeded: `|η⟩ = QFT^{⊗n}|ψ⟩ ⊗ QFT^{⊗n}|φ⟩`, then
`U_add |x⟩|e⟩ = |x⟩|x + e⟩`, then `U_decode |x⟩|z⟩ = |x − Decode_{C⊥}(z)⟩|z⟩`, then
`I ⊗ (QFT_Σ^{−1})^{⊗n}`. As a function of the two registers `(x′, w)`:
`final(x′, w) = (QFT^{−1 ⊗n}_z ↦ η(x′ + D(z), z − x′ − D(z)))(w)` with `D = Decode_{C⊥}` at
radius `τ`. -/
noncomputable def finalState (C : Finset (Fin n → Fin m → K)) (τ : ℕ)
    (h : Fin n × (Fin m → K) → Bool) (x' w : Fin n → Fin m → K) : ℂ :=
  qftInv (fun z => qft (psiVec C) (x' + decodeDual C τ z) *
      qft (phiVec h) (z - (x' + decodeDual C τ z))) w

/-- **The output law of `Prove^h`** (Construction 6.2, pp.28–29) on `Option (Σ^n)`
(`none` = `π = ⊥`): abort with probability `1 − stepOneSucc`; otherwise measure the second
register of `finalState` in the computational basis (step 6), so
`Pr[π = w] = stepOneSucc · Σ_{x′} |final(x′, w)|²`. -/
noncomputable def proveOut (C : Finset (Fin n → Fin m → K)) (τ L : ℕ)
    (h : Fin n × (Fin m → K) → Bool) : Option (Fin n → Fin m → K) → ℝ
  | none => 1 - stepOneSucc L h
  | some w => stepOneSucc L h * ∑ x', Complex.normSq (finalState C τ h x' w)

open Classical in
/-- `Pr[Verify^h(Prove^h) = ⊥ | H = h]` (Definition 6.1, Correctness, p.28, for Construction 6.2,
p.29): `Verify` rejects `π = ⊥` and every `x` that is not correct (`x ∉ C` or `H_i(x_i) = 1` for
some `i`; the published `CertRandQROM.IsCorrect`). -/
noncomputable def rejProb (C : Finset (Fin n → Fin m → K)) (τ L : ℕ)
    (h : Fin n × (Fin m → K) → Bool) : ℝ :=
  proveOut C τ L h none +
    ∑ w, if CertRandQROM.IsCorrect C h w then 0 else proveOut C τ L h (some w)

/-- **Rejection probability of the honest prover of Construction 6.2 at security parameter `λ`**
for a fixed oracle `h : [n] × Σ → {0,1}` (Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal,
arXiv:2608.31112, sha256 b75095a2…, Construction 6.2 pp.28–29, Definition 6.1 p.28): the code is
`C_λ = CertRandQROM.code F γ λ` (§5.2), `Decode_{C⊥}` has radius `τ = ⌊(k(λ) + 1)/2⌋` (p.25),
and step 1 makes at most `λ` trials per coordinate.

**Formalization Note** The prover's internal randomness (the trial outcomes of step 1 and the
final measurement) is integrated out exactly: given success of step 1 the state is `|φ⟩`
whatever the trial history. The input `1^{h∞}` is ignored by `Prove` and `Verify`, so the
quantity does not depend on it. -/
noncomputable def honestRejProb (F : ℕ → Type) [∀ l, Field (F l)] [∀ l, Fintype (F l)]
    [∀ l, DecidableEq (F l)] (γ : ∀ l, F l) (l : ℕ) (h : CertRandQROM.Dom F l → Bool) : ℝ :=
  rejProb (CertRandQROM.code F γ l) (decRadius (CertRandQROM.kPar F l)) l h

end CertRandQROM.Supplement


