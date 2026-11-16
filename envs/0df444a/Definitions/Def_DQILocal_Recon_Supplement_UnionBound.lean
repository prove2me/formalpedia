-- Prove2me | Definitions.Def_DQILocal_Recon_Supplement_UnionBound
-- name    : DQILocal_Recon_Supplement_UnionBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:26:53.887201+00:00
-- url     : https://prove2.me/theorems/bd409cbd-d1b9-4318-8b92-2f8dea3ea3ef
-- title:
--   The weight enumerator $U_C(\theta)$, $h$, $W_D$, $G_{k,D}$ and the constants $A$, $\varepsilon$ of Theorem 6.16
-- statement:
--   For a binary code $C=\{c\in\mathbb Z_2^m:B^\top c=0\}$ and $\theta\in\mathbb R$:
--
--   1. $U_C(\theta)=\sum_{c\in C\setminus\{0\}}\theta^{|c|}$;
--   2. $h(u)=-u\ln u-(1-u)\ln(1-u)$, with $0\ln0=0$;
--   3. $W_D(x)=\tfrac12\bigl((1+x)^D+(1-x)^D\bigr)$, the generating function of the even-weight vectors of $\{0,1\}^D$;
--   4. $$G_{k,D}(u,x;\theta)=(1-k)\,h(u)+\frac kD\ln W_D(x)-k\,u\ln x+u\ln\theta;$$
--   5. $A=e^{1+2^{D-1}k/D}$ and $\varepsilon=(2A)^{-1/(k/2-1)}$.
--
--   These are the ingredients of the first-moment bound on the weight enumerator of random regular codes, which controls Prange's sampler.
--
--   **Formalization Note** Powers in $\varepsilon$ are real powers, with $k/2-1$ a real number.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §6.3.3, pp. 50–52

import Mathlib
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Supplement_Thresholds

namespace DQILocal.Recon.Supplement

open scoped BigOperators
open DQILocal.Recon

/-- **The weight enumerator `U_C(θ)`.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §6.3.3, p. 50:
`U_C(θ) = Σ_{c ∈ C ∖ {0}} θ^{|c|}`, `|c|` the Hamming weight, for the binary code
`C = {c ∈ ℤ_2^m : Bᵀc = 0}` (base `code 2 B`). -/
noncomputable def weightEnum {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (θ : ℝ) : ℝ :=
  ∑ c ∈ (codeFinset 2 B).filter (fun c => c ≠ 0), θ ^ hamWt c

/-- **Binary entropy in nats (p. 51)**: `h(u) = -u ln u - (1 - u) ln(1 - u)`, with `0 ln 0 = 0`
(`Real.negMulLog`). -/
noncomputable def binEnt (u : ℝ) : ℝ := Real.negMulLog u + Real.negMulLog (1 - u)

/-- **`W_D(x) = ½((1 + x)^D + (1 - x)^D)` (p. 51)**, the generating function of the even-weight
vectors of `{0,1}^D` counted by weight. -/
noncomputable def evenGF (D : ℕ) (x : ℝ) : ℝ := (1 / 2) * ((1 + x) ^ D + (1 - x) ^ D)

/-- **`G_{k,D}(u, x; θ) = (1 - k) h(u) + (k/D) ln W_D(x) - k u ln x + u ln θ` (p. 51).** -/
noncomputable def Gfun (k D : ℕ) (u x θ : ℝ) : ℝ :=
  (1 - (k : ℝ)) * binEnt u + ((k : ℝ) / D) * Real.log (evenGF D x) - (k : ℝ) * u * Real.log x +
    u * Real.log θ

/-- **The constant `A = e^{1 + 2^{D-1} k / D}` of Theorem 6.16 (p. 52).** -/
noncomputable def constA (k D : ℕ) : ℝ := Real.exp (1 + (2 : ℝ) ^ (D - 1) * (k : ℝ) / D)

/-- **The constant `ε = (2A)^{-1/(k/2 - 1)}` of Theorem 6.16 (p. 52)**, a real power with
`k/2 - 1` a real number (positive for `k ≥ 3`). -/
noncomputable def epsUB (k D : ℕ) : ℝ := (2 * constA k D) ^ (-1 / ((k : ℝ) / 2 - 1))

end DQILocal.Recon.Supplement


