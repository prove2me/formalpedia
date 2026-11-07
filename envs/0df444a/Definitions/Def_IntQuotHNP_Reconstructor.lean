-- Prove2me | Definitions.Def_IntQuotHNP_Reconstructor
-- name    : IntQuotHNP_Reconstructor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:15.915211+00:00
-- url     : https://prove2.me/theorems/4c56dd63-0af5-4284-80ca-10cc51c2f992
-- title:
--   §4.1 — the MIHNP reconstructor $R(a)$
-- statement:
--   Given $a\in\{0,\dots,X-1\}$: if $v_1+a\notin\mathbb Z_p\setminus\{0\}$, then $R(a)=\emptyset$. Otherwise put $\hat y=[(v_1+a)^{-1}-t_1]_p$. If $\hat y+t_i\equiv0\pmod p$ for some $i$, then $R(a)=\emptyset$. Otherwise put $\hat z_i=[(\hat y+t_i)^{-1}]_p$ and $\hat x_i=\hat z_i-v_i$; then $R(a)=\{\hat y\}$ if $\hat x_i\in\{0,\dots,X-1\}$ for every $i$, and $R(a)=\emptyset$ otherwise.
--
--   $R$ turns a guess for the first error coordinate into at most one fully verified secret.
--
--   **Formalization Note** The check $v_1+a\in\mathbb Z_p\setminus\{0\}$ is the integer condition $1\le v_1+a\le p-1$. The interval check on $\hat x_i$ is done over the integers, as $v_i\le\hat z_i<v_i+X$. For $N=0$, excluded by the promise, the value is $\emptyset$.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.1, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_IntQuotHNP_MIHNPInput

namespace IntQuotHNP

open Classical in
/-- **The MIHNP reconstructor `R(a)`** (§4.1).
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §4.1, p.23 (PDF p.24): "Given a ∈ B₁, first check v₁ + a ∈ ℤ_p \ {0}. If this fails, set
R(a) = ∅ and stop. Otherwise compute ŷ = [(v₁ + a)⁻¹ − t₁]_p. If ŷ + t_i ≡ 0 (mod p) for any
i ∈ [N], set R(a) = ∅ and stop. Otherwise, for every i ∈ [N], compute ẑ_i = [(ŷ + t_i)⁻¹]_p and
x̂_i = ẑ_i − v_i. Set R(a) = {ŷ} if x̂ ∈ B, and R(a) = ∅ otherwise."

**Formalization Note.** `v₁ + a ∈ ℤ_p \ {0}` is the integer condition `1 ≤ v₁ + a ≤ p − 1`.
Inverses are taken in `ZMod p` at nonzero arguments only (the checks come first) and represented by
`ZMod.val`. `x̂ ∈ B` means `0 ≤ ẑ_i − v_i ≤ X − 1` as integers, i.e. `v_i ≤ ẑ_i < v_i + X`. The
paper's index 1 is the 0-based index `0`; for `N = 0` (excluded by the promise) the set is empty. -/
noncomputable def reconstruct (I : MIHNPInput) (a : ℕ) : Finset ℕ :=
  if h : 0 < I.N then
    if 1 ≤ I.v ⟨0, h⟩ + a ∧ I.v ⟨0, h⟩ + a < I.p then
      let yhat : ℕ := ((((I.v ⟨0, h⟩ + a : ℕ) : ZMod I.p)⁻¹) - ((I.t ⟨0, h⟩ : ℕ) : ZMod I.p)).val
      if ∃ i, (yhat + I.t i) % I.p = 0 then ∅
      else
        let zhat : Fin I.N → ℕ := fun i => (((yhat + I.t i : ℕ) : ZMod I.p)⁻¹).val
        if ∀ i, I.v i ≤ zhat i ∧ zhat i < I.v i + I.X then {yhat} else ∅
    else ∅
  else ∅

end IntQuotHNP


