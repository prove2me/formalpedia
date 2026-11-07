-- Prove2me | Definitions.Def_QuantumPRC_pfIso
-- name    : QuantumPRC_pfIso
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:24.852839+00:00
-- url     : https://prove2.me/theorems/341e6385-93ce-42c5-b292-114ded1b3ae6
-- title:
--   PF isometries $V_{\pi',f'}$ (167) and the laws $\mathcal D,\mathcal D'$ of Lemma 7.10
-- statement:
--   For $n_{\mathrm P}=n_{\mathrm L}+\ell+s$, a permutation $\pi'$ of $\{0,1\}^{n_{\mathrm P}}$ and $f':\{0,1\}^{n_{\mathrm L}+\ell}\to\{0,1\}$, the **PF isometry** is
--
--   $$
--   V_{\pi',f'}:|x\rangle\mapsto\frac1{\sqrt{2^\ell}}\sum_{y\in\{0,1\}^\ell}(-1)^{f'(x\|y)}|\pi'(x\|y\|0^s)\rangle\qquad(167).
--   $$
--
--   For $n,r,m\in\mathbb N$, $\mathcal D$ is the law of $h(z)=\pi(z\|0^r)\|f(z)$ for a uniform function $f:\{0,1\}^n\to\{0,1\}^m$ and a uniform permutation $\pi$ of $\{0,1\}^{n+r}$, and $\mathcal D'$ is the law of $h(z)=\pi'(z\|0^{r+m})$ for a uniform permutation $\pi'$ of $\{0,1\}^{n+r+m}$; both are laws on functions $\{0,1\}^n\to\{0,1\}^{n+r+m}$, given by their probability mass functions.
--
--   These are the objects of the pseudorandomness proof of Construction 7.2 (Theorem 7.9, Lemma 7.10).
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 7.9, Eq. (167), p.49; Lemma 7.10, p.49

import Mathlib
import Definitions.Def_QuantumPRC_PRF

open Matrix

namespace QuantumPRC

/-- The all-zero string `0^r`. -/
def zeros (r : ℕ) : Bits r := fun _ => false

/-- **PF isometry** `V_{π′,f′}`, Eq. (167). Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
Theorem 7.9, p.49: "For a permutation `π′` over `nP` bits and a function `f′ : {0,1}^{nL+ℓ} → {0,1}`, define
an isometry from `nL` qubits to `nP` qubits by `V_{π′,f′} : |x⟩ ↦ (1/√2^ℓ) Σ_{y∈{0,1}^ℓ} (−1)^{f′(x∥y)}
|π′(x∥y∥0^s)⟩`", with `nP := nL + ℓ + s`. -/
noncomputable def pfIso {nL ℓ s : ℕ} (π' : Equiv.Perm (Bits (nL + ℓ + s))) (f' : Bits (nL + ℓ) → Bool) :
    Matrix (Bits (nL + ℓ + s)) (Bits nL) ℂ :=
  fun w x => ((Real.sqrt 2 : ℂ) ^ ℓ)⁻¹ * ∑ y : Bits ℓ,
    if w = π' (Fin.append (Fin.append x y) (zeros s)) then
      (if f' (Fin.append x y) then -1 else 1)
    else 0

/-- The injective function `h(z) := π(z∥0^r)∥f(z)` of Lemma 7.10 (distribution `D`). -/
def injD {n r m : ℕ} (f : Bits n → Bits m) (π : Equiv.Perm (Bits (n + r))) :
    Bits n → Bits (n + r + m) :=
  fun z => Fin.append (π (Fin.append z (zeros r))) (f z)

/-- The injective function `h(z) := π′(z∥0^{r+m})` of Lemma 7.10 (distribution `D′`). -/
def injD' {n r m : ℕ} (π' : Equiv.Perm (Bits (n + r + m))) : Bits n → Bits (n + r + m) :=
  fun z => π' (Fin.append (Fin.append z (zeros r)) (zeros m))

/-- `Pr_{h←D}[h = h₀]` (Lemma 7.10, p.49: "Choose a uniformly random function `f : {0,1}^n → {0,1}^m`
and a uniformly random permutation `π : {0,1}^{n+r} → {0,1}^{n+r}`. Define `h(z) := π(z∥0^r)∥f(z)`"). -/
noncomputable def lawD (n r m : ℕ) (h₀ : Bits n → Bits (n + r + m)) : ℝ :=
  ((Fintype.card (Bits n → Bits m) : ℝ) * Fintype.card (Equiv.Perm (Bits (n + r))))⁻¹ *
    ((Finset.univ : Finset ((Bits n → Bits m) × Equiv.Perm (Bits (n + r)))).filter
      fun p => injD p.1 p.2 = h₀).card

/-- `Pr_{h←D′}[h = h₀]` (Lemma 7.10: "Choose a uniformly random permutation `π′ : {0,1}^{n+r+m} →
{0,1}^{n+r+m}`. Define `h(z) := π′(z∥0^{r+m})`"). -/
noncomputable def lawD' (n r m : ℕ) (h₀ : Bits n → Bits (n + r + m)) : ℝ :=
  (Fintype.card (Equiv.Perm (Bits (n + r + m))) : ℝ)⁻¹ *
    ((Finset.univ : Finset (Equiv.Perm (Bits (n + r + m)))).filter fun π' => injD' π' = h₀).card

end QuantumPRC


