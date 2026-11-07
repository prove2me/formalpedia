-- Prove2me | Definitions.Def_KTUnitary_Synth_UColumn
-- name    : KTUnitary_Synth_UColumn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:37.384749+00:00
-- url     : https://prove2.me/theorems/c54429a5-d23d-4de8-8e46-0c9d2441fc1e
-- title:
--   The column language $\mathcal U\mathrm{Column}$
-- statement:
--   For a unitary language $\mathcal U=\{U_n\}$, let $|\psi_x\rangle=\big(|0\rangle|0^n\rangle-|1\rangle U_n|x\rangle\big)/\sqrt2$. Then $\mathcal U\mathrm{Column}=\{V_{2n+1}\}$ with
--   $$V_{2n+1}=\sum_{x\in\{0,1\}^n}|x\rangle\langle x|\otimes\big(I-2|\psi_x\rangle\langle\psi_x|\big).$$
--   $V_{2n+1}$ maps $|x\rangle|0\rangle|0^n\rangle$ to $|x\rangle|1\rangle U_n|x\rangle$; it is item 3 of Theorem 6.17.
--
--   **Formalization Note** Qubit order $(x,\text{flag},n\text{-qubit register})$. For even $m$, where the paper defines nothing, $V_m$ is the identity.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.12, p. 28

import Mathlib
import Definitions.Def_KTUnitary_Synth_ULang

open QAlgorithms.Complexity

namespace KTUnitary.Synth

open Classical in
/-- **The column language `𝒰Column`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.12, p. 28): "Let `𝒰 = {U_n}` be a
unitary language. Denote by `|ψ_x⟩ := (|0⟩|0^n⟩ − |1⟩U_n|x⟩)/√2`. Then `𝒰Column = {V_{2n+1}}` is the
unitary language defined by `V_{2n+1} = Σ_{x ∈ {0,1}^n} |x⟩⟨x| ⊗ (I − 2|ψ_x⟩⟨ψ_x|)`."

Here, on `2n + 1` qubits, a basis state `z` is read as `x = z₀ ⋯ z_{n−1}`, a flag qubit `z_n` and
`r = z_{n+1} ⋯ z_{2n}`. The amplitude of `|ψ_x⟩` at `(flag, r)` is `1/√2` at `(0, 0^n)`, `0` at the
other `(0, r)`, and `−⟨r|U_n|x⟩/√2` at `(1, r)`. The entry of `V_{2n+1}` in row `z`, column `z'` is
`[(flag, r) = (flag', r')] − 2 ψ_x(flag, r) · conj(ψ_x(flag', r'))` when `x = x'`, and `0` otherwise.

**Formalization Note** The registers are in the order `(x, flag, n-qubit register)`, as in
`|x⟩⟨x| ⊗ (I − 2|ψ_x⟩⟨ψ_x|)` with `|ψ_x⟩` on `|flag⟩|r⟩`. For even `m`, where the paper defines no
`V_m`, the member is the identity. -/
noncomputable def UColumn (U : ULang) : ULang :=
  ULang.ofMatrices fun m =>
    if m % 2 = 1 then
      let n := m / 2
      let xOf : Bits m → Bits n := fun z q => (List.ofFn z).getD q false
      let fOf : Bits m → Bool := fun z => (List.ofFn z).getD n false
      let rOf : Bits m → Bits n := fun z q => (List.ofFn z).getD (n + 1 + q) false
      let ψ : Bits n → Bool → Bits n → ℂ := fun x fl r =>
        if fl then -((U n : Matrix (Bits n) (Bits n) ℂ) r x) / (Real.sqrt 2 : ℂ)
        else if r = (fun _ => false) then 1 / (Real.sqrt 2 : ℂ) else 0
      Matrix.of fun z z' =>
        if xOf z = xOf z' then
          (if fOf z = fOf z' ∧ rOf z = rOf z' then 1 else 0) -
            2 * ψ (xOf z) (fOf z) (rOf z) * star (ψ (xOf z) (fOf z') (rOf z'))
        else 0
    else 1

end KTUnitary.Synth


