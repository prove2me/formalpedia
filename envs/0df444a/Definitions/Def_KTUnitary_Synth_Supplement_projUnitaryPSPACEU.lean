-- Prove2me | Definitions.Def_KTUnitary_Synth_Supplement_projUnitaryPSPACEU
-- name    : KTUnitary_Synth_Supplement_projUnitaryPSPACEU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:16:44.59374+00:00
-- url     : https://prove2.me/theorems/c81192d9-b4f9-4d14-b282-ac72bdc5f641
-- title:
--   $\mathsf{projUnitaryPSPACE}^{\mathcal O}$ for a unitary oracle $\mathcal O$
-- statement:
--   Let $\mathcal O=\{O_n\}_{n\in\mathbb N}$ be a unitary language used as an oracle. A **projective $\mathcal O$-oracle unitary quantum circuit** is a sequence of explicitly specified unitary gates (entries given by an FPTEAS encoding) and oracle gates from the set
--   $$\{O_n,\;O_n^*,\;O_n^\dagger,\;O_n^{\mathrm T}\}_{n\in\mathbb N},$$
--   with no controlled oracle gate. A unitary language $\mathcal U=\{U_n\}$ lies in $\mathsf{projUnitaryPSPACE}^{\mathcal O}$ if there is a space-uniform family $\{C_{n,\varepsilon}\}$ of projective $\mathcal O$-oracle circuits on $n+a(n,\varepsilon)\le\mathrm{poly}(n,\log 1/\varepsilon)$ qubits such that for every $n$ and $\varepsilon$ there is an $a$-qubit **dilation** $\overline U$ of $U_n$, that is a unitary with $\overline U|\psi\rangle|0^a\rangle=(U_n|\psi\rangle)|g\rangle$ for one garbage state $|g\rangle$ and every $|\psi\rangle$, with
--   $$\|\overline U-C_{n,\varepsilon}\|_{\mathrm{op}}\le\varepsilon .$$
--
--   The projective classes forget global phases: a dilation of $U$ with garbage $|g\rangle$ is also a dilation of $\phi U$ with garbage $\phi^*|g\rangle$. This class relative to a general unitary oracle is used in Theorem 5.23.
--
--   **Formalization Note** The precision is $\varepsilon=2^{-l}$, $l\in\mathbb N$ (footnote 4, p. 14); one FPTEAS encoding serves the whole family; space uniformity means the description has length at most $2^{\mathrm{poly}}$, each gate description has polynomial length, and its bits are decidable in polynomial space. The body is that of the published clean class with the published `PSPACEOracleSynth.Main.IsDilation` in place of an extension and with controlled oracle gates excluded. For a classical oracle it coincides with the published `PSPACEOracleSynth.Main.projUnitaryPSPACE`.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definitions 5.16 and 5.17, p. 21

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_KTUnitary_Synth_SpaceUniform
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity QAdvFew.PoQOracle PSPACEOracleSynth.Main

namespace KTUnitary.Synth.Supplement

/-- **The class `projUnitaryPSPACE^𝒪` for a unitary oracle `𝒪`** (Kretschmer, Tang, *Unitary
Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 5.16 and 5.17,
p. 21): "`projUnitaryPSPACE^𝒪` is defined the same way, but where `{C_{n,ε}}` is a space-uniform
family."

Here: as `KTUnitary.Synth.Supplement.projUnitaryPU 𝒪` (projective `𝒪`-oracle circuits: oracle gates `O_n, O_n^*, O_n^†, O_n^T`,
no controlled oracle gate `UGate.corac`; a dilation in place of an extension), with the descriptions of `C n l`
space-uniform in `tup [1^n, 1^l]` (published `KTUnitary.Synth.SpaceUniform`: description length at
most `2^{p'}`, gate descriptions of length at most `p'`, bits decidable in polynomial space).

**Formalization Note** The body is that of the published `KTUnitary.Synth.unitaryPSPACE 𝒪` with
`IsDilation` in place of `IsExtension` and the gate restriction of Definition 5.16 (no gate of the form `UGate.corac`; the uncontrolled
oracle gates `UGate.orac κ` of all four kinds `κ` are allowed). -/
def projUnitaryPSPACEU (O : ULang) : Set ULang :=
  {U | ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
    SpaceUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2]) (fun nl => (C nl.1 nl.2).code)
      (fun nl => (C nl.1 nl.2).gateCodes) ∧
    ∀ n l : ℕ, (C n l).Valid f ∧
      (∀ g ∈ (C n l).gates, ¬ ∃ κ m w, g = UGate.corac κ m w) ∧ ∃ h : n ≤ (C n l).N, (C n l).N ≤ n + p.eval (n + l) ∧
      ∃ Ub, IsDilation h (U n : Matrix (Bits n) (Bits n) ℂ) Ub ∧
        opNorm (Ub - (C n l).unitary f O) ≤ (2 : ℝ)⁻¹ ^ l}

end KTUnitary.Synth.Supplement


