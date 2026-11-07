-- Prove2me | Definitions.Def_QPACLarge_prfAdv
-- name    : QPACLarge_prfAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:51.41473+00:00
-- url     : https://prove2.me/theorems/402ab45f-ee76-4e38-8e53-20faef2ae7b7
-- title:
--   Distinguishing advantage $\mathrm{Adv}_G(D,\lambda)$
-- statement:
--   For a randomized oracle algorithm $D$,
--
--   $$
--   \mathrm{Adv}_G(D, \lambda) = \Big|\Pr_{s \sim U_{\ell(\lambda)},\, D}\big[D^{g_{\lambda,s}}(1^\lambda) = 1\big] - \Pr_{R \sim \mathrm{ALL}_\lambda,\, D}\big[D^{R}(1^\lambda) = 1\big]\Big|,
--   $$
--
--   where $R$ is a uniformly random Boolean function on $\lambda$ bits. Here $D$ is an oracle Turing machine with $T$ uniform coins, clocked at $T$ steps; it accepts when it halts with output $1$ within $T$ steps.
--
--   **Formalization Note** Oracle machines are the published `HMBinPacking.OracleMachine` (adaptive classical queries at unit cost). The oracle answers a $\lambda$-bit query $x$ with $g_{\lambda,s}(x)$ (resp. $R(x)$) and any other query with the empty word.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 4.2.1, p.31

import Mathlib
import Definitions.Def_QPACLarge_prfEval
import Definitions.Def_HMBinPacking_OracleMachine

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **Distinguishing advantage against a function family.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 4.2.1, p.31: "For a randomized oracle algorithm `D`, define
`Adv_G(D, λ) ≜ |Pr_{s∼U_{ℓ(λ)}, D}[D^{g_{λ,s}}(1^λ) = 1] − Pr_{R∼ALL_λ, D}[D^R(1^λ) = 1]|`, where `R` is a
uniformly random Boolean function on `λ` bits."

`prfAdv D ℓ G λ T`: the distinguisher is an oracle machine (the published
`HMBinPacking.OracleMachine`, adaptive classical queries at unit cost) started on `1^λ0 · r` with `T`
uniform coin bits `r`; it accepts when it halts with output `1` within `T` steps. The oracle answers
a `λ`-bit query `x` by the bit `g_{λ,s}(x)` (resp. `R(x)`) and any other query by the empty word.
The advantage is the absolute difference of the acceptance probabilities under a uniform key
`s ∈ {0,1}^{ℓ(λ)}` and under a uniform `R : {0,1}^λ → {0,1}`.

**Formalization Note.** A run that does not accept within `T` steps rejects (clocked machines;
see `SubexpOWFExists`). -/
noncomputable def prfAdv (D : HMBinPacking.OracleMachine) (ℓ : ℕ → ℕ) (G : Str → Str) (lam T : ℕ) :
    ℝ :=
  open Classical in
  let acc : (Str → Str) → ℝ := fun O =>
    ((2 : ℝ) ^ T)⁻¹ * ((Finset.univ.filter fun r : Fin T → Bool =>
      HMBinPacking.ORunsWithin D O (encNat lam ++ List.ofFn r) [true] T T).card : ℝ)
  |((2 : ℝ) ^ ℓ lam)⁻¹ * ∑ s : Fin (ℓ lam) → Bool,
      acc (fun q => if q.length = lam then
        [prfEval G lam (List.ofFn s) (fun i => q.getD i false)] else []) -
    ((2 : ℝ) ^ (2 ^ lam))⁻¹ * ∑ R : Qubits lam → Bool,
      acc (fun q => if q.length = lam then [R (fun i => q.getD i false)] else [])|

end QPACLarge


